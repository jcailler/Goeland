/**
* Copyright 2022 by the authors (see AUTHORS).
*
* Goéland is an automated theorem prover for first order logic.
*
* This software is governed by the CeCILL license under French law and
* abiding by the rules of distribution of free software.  You can  use,
* modify and/ or redistribute the software under the terms of the CeCILL
* license as circulated by CEA, CNRS and INRIA at the following URL
* "http://www.cecill.info".
*
* As a counterpart to the access to the source code and  rights to copy,
* modify and redistribute granted by the license, users are provided only
* with a limited warranty  and the software's author,  the holder of the
* economic rights,  and the successive licensors  have only  limited
* liability.
*
* In this respect, the user's attention is drawn to the risks associated
* with loading,  using,  modifying and/or developing or reproducing the
* software by the user in light of its specific status of free software,
* that may mean  that it is complicated to manipulate,  and  that  also
* therefore means  that it is reserved for developers  and  experienced
* professionals having in-depth computer knowledge. Users are therefore
* encouraged to load and test the software's suitability as regards their
* requirements in conditions enabling the security of their systems and/or
* data to be ensured and,  more generally, to use and operate it in the
* same conditions as regards security.
*
* The fact that you are presently reading this means that you have had
* knowledge of the CeCILL license and that you accept its terms.
**/

/**
* This file implements a congruence closure over ground terms.
*
* Terms are hash-consed into a DAG, so structurally equal terms share a node.
* Classes are maintained with a union-find (path compression + union by size),
* and congruence is restored incrementally: each class keeps the list of the
* applications it occurs in, so merging two classes only re-canonicalises the
* applications that can actually change signature, instead of re-scanning every
* term until a fixpoint is reached.
**/

package cc

import (
	"strconv"
	"strings"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Lib"
)

// application is a hash-consed node of the term DAG. [args] holds node ids; a
// constant is simply an application with no argument.
type application struct {
	symbol string
	args   []int
}

// Closure is a congruence closure over ground terms.
type Closure struct {
	apps   []application
	parent []int
	size   []int
	// uses[c] lists the applications having c among the representatives of
	// their arguments. Only maintained for class representatives.
	uses [][]int
	// intern maps a structural key to its node id (hash-consing).
	intern map[string]int
	// signatures maps the canonical signature of an application to the node
	// currently carrying it, which is how congruent applications are detected.
	signatures map[string]int
	pending    []int
}

func NewClosure() *Closure {
	return &Closure{
		intern:     make(map[string]int),
		signatures: make(map[string]int),
	}
}

// Find returns the representative of the class of [n], compressing the path.
func (c *Closure) Find(n int) int {
	root := n
	for c.parent[root] != root {
		root = c.parent[root]
	}
	for c.parent[n] != root {
		c.parent[n], n = root, c.parent[n]
	}
	return root
}

// Equivalent reports whether the two terms are equal in the current closure.
// Terms absent from the closure are only equal to themselves.
func (c *Closure) Equivalent(s, t AST.Term) bool {
	i, ok1 := c.lookup(s)
	j, ok2 := c.lookup(t)
	if !ok1 || !ok2 {
		return false
	}
	return c.Find(i) == c.Find(j)
}

func (c *Closure) lookup(t AST.Term) (int, bool) {
	key, ok := c.keyOf(t)
	if !ok {
		return 0, false
	}
	id, found := c.intern[key]
	return id, found
}

// keyOf builds the hash-consing key of [t], adding its subterms to the DAG on
// the way. It fails on non-ground terms: the caller must have filtered them out.
func (c *Closure) keyOf(t AST.Term) (string, bool) {
	switch typed := t.(type) {
	case AST.Fun:
		args := make([]int, 0, typed.GetArgs().Len())
		for _, arg := range typed.GetArgs().GetSlice() {
			id, ok := c.Add(arg)
			if !ok {
				return "", false
			}
			args = append(args, id)
		}
		return c.signatureOf(symbolOf(typed), args), true
	case AST.Meta:
		return "", false
	default:
		return "@" + t.ToString(), true
	}
}

// symbolOf includes the type arguments so that two instances of a polymorphic
// symbol at different types are kept apart.
func symbolOf(f AST.Fun) string {
	if f.GetTyArgs().Len() == 0 {
		return f.GetName()
	}
	var b strings.Builder
	b.WriteString(f.GetName())
	b.WriteByte('<')
	for i, ty := range f.GetTyArgs().GetSlice() {
		if i > 0 {
			b.WriteByte(',')
		}
		b.WriteString(ty.ToString())
	}
	b.WriteByte('>')
	return b.String()
}

// signatureOf is the canonical key of an application whose arguments are given
// by node id. Callers pass representatives to obtain a congruence signature.
func (c *Closure) signatureOf(symbol string, args []int) string {
	var b strings.Builder
	b.WriteString(symbol)
	b.WriteByte('/')
	b.WriteString(strconv.Itoa(len(args)))
	for _, a := range args {
		b.WriteByte(',')
		b.WriteString(strconv.Itoa(a))
	}
	return b.String()
}

// Add registers [t] and its subterms, returning the id of its node. It reports
// false if [t] is not ground.
func (c *Closure) Add(t AST.Term) (int, bool) {
	key, ok := c.keyOf(t)
	if !ok {
		return 0, false
	}
	if id, found := c.intern[key]; found {
		return id, true
	}

	var app application
	switch typed := t.(type) {
	case AST.Fun:
		args := make([]int, 0, typed.GetArgs().Len())
		for _, arg := range typed.GetArgs().GetSlice() {
			// Subterms were registered by keyOf, so this cannot fail here.
			id, _ := c.Add(arg)
			args = append(args, id)
		}
		app = application{symbol: symbolOf(typed), args: args}
	default:
		app = application{symbol: key}
	}

	id := len(c.apps)
	c.apps = append(c.apps, app)
	c.parent = append(c.parent, id)
	c.size = append(c.size, 1)
	c.uses = append(c.uses, nil)
	c.intern[key] = id

	for _, a := range app.args {
		r := c.Find(a)
		c.uses[r] = append(c.uses[r], id)
	}
	c.signatures[c.currentSignature(id)] = id
	return id, true
}

func (c *Closure) currentSignature(id int) string {
	app := c.apps[id]
	args := make([]int, len(app.args))
	for i, a := range app.args {
		args[i] = c.Find(a)
	}
	return c.signatureOf(app.symbol, args)
}

// Assert states that s and t denote the same object. It reports false if either
// term is not ground.
func (c *Closure) Assert(s, t AST.Term) bool {
	i, ok1 := c.Add(s)
	j, ok2 := c.Add(t)
	if !ok1 || !ok2 {
		return false
	}
	c.merge(i, j)
	return true
}

// merge unions the two classes and restores congruence. Only the applications
// using the absorbed class are re-canonicalised.
func (c *Closure) merge(a, b int) {
	c.pending = append(c.pending, a, b)
	for len(c.pending) > 0 {
		y := c.pending[len(c.pending)-1]
		x := c.pending[len(c.pending)-2]
		c.pending = c.pending[:len(c.pending)-2]

		rx, ry := c.Find(x), c.Find(y)
		if rx == ry {
			continue
		}
		// Union by size: the smaller class is absorbed, so the number of
		// applications we have to revisit stays bounded.
		if c.size[rx] < c.size[ry] {
			rx, ry = ry, rx
		}
		c.parent[ry] = rx
		c.size[rx] += c.size[ry]

		absorbed := c.uses[ry]
		c.uses[ry] = nil
		for _, u := range absorbed {
			sig := c.currentSignature(u)
			if other, found := c.signatures[sig]; found && c.Find(other) != c.Find(u) {
				c.pending = append(c.pending, u, other)
			} else if !found {
				c.signatures[sig] = u
			}
			c.uses[rx] = append(c.uses[rx], u)
		}
	}
}

// ---------------------------------------------------------------------------
// Branch-level entry point

// literal is a ground atom of the branch, kept with its polarity.
type literal struct {
	positive bool
	pred     AST.Pred
}

// GroundContradiction runs a congruence closure over the ground fragment of the
// branch and reports whether that fragment is contradictory. Non-ground formulas
// are ignored, which keeps the answer sound: a contradiction among ground
// literals closes the branch whatever the metavariables are instantiated with,
// so no substitution has to be reported to the father.
//
// The converse does not hold, so a negative answer means "no ground
// contradiction", not "the branch cannot be closed": the caller must still run
// the general (rigid) equality reasoning.
func GroundContradiction(atomics Lib.List[AST.Form]) bool {
	// Without a ground equality there is nothing congruence closure can derive
	// that the plain closure rule does not already catch, so bail out before
	// allocating anything. This is the common case.
	if !hasGroundEquality(atomics) {
		return false
	}

	closure := NewClosure()
	literals := make([]literal, 0, atomics.Len())
	disequalities := make([][2]AST.Term, 0)

	for _, form := range atomics.GetSlice() {
		if !form.GetMetas().IsEmpty() {
			continue
		}
		positive := true
		atom := form
		if not, ok := form.(AST.Not); ok {
			positive = false
			atom = not.GetChildFormulas().At(0)
		}
		pred, ok := atom.(AST.Pred)
		if !ok {
			continue
		}

		if pred.GetID().Equals(AST.Id_eq) && pred.GetArgs().Len() == 2 {
			lhs, rhs := pred.GetArgs().At(0), pred.GetArgs().At(1)
			if positive {
				closure.Assert(lhs, rhs)
			} else {
				disequalities = append(disequalities, [2]AST.Term{lhs, rhs})
			}
			continue
		}

		for _, arg := range pred.GetArgs().GetSlice() {
			closure.Add(arg)
		}
		literals = append(literals, literal{positive: positive, pred: pred})
	}

	// s != t together with s = t.
	for _, pair := range disequalities {
		if closure.Equivalent(pair[0], pair[1]) {
			return true
		}
	}

	// p(t...) together with ~p(s...) where the arguments are pairwise equal.
	for i, first := range literals {
		for _, second := range literals[i+1:] {
			if first.positive == second.positive {
				continue
			}
			if !first.pred.GetID().Equals(second.pred.GetID()) {
				continue
			}
			if congruentArgs(closure, first.pred, second.pred) {
				return true
			}
		}
	}

	return false
}

func hasGroundEquality(atomics Lib.List[AST.Form]) bool {
	for _, form := range atomics.GetSlice() {
		pred, ok := form.(AST.Pred)
		if !ok {
			continue
		}
		if pred.GetID().Equals(AST.Id_eq) && pred.GetMetas().IsEmpty() {
			return true
		}
	}
	return false
}

func congruentArgs(closure *Closure, p, q AST.Pred) bool {
	if p.GetArgs().Len() != q.GetArgs().Len() {
		return false
	}
	for i := range p.GetArgs().GetSlice() {
		if !closure.Equivalent(p.GetArgs().At(i), q.GetArgs().At(i)) {
			return false
		}
	}
	return true
}

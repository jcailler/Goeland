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
* This file implements term indexing with discrimination trees, an alternative
* to the code trees of [code-trees.go].
*
* A term is flattened into its preorder sequence of symbols, every metavariable
* being written as the wildcard *, and that sequence is the path leading to the
* term in the trie. Since every symbol carries a fixed arity, the sequence
* determines the term, so no information is lost by the flattening.
*
* Retrieval is a filter: walking the trie yields a superset of the unifiable
* entries, which are then unified for real. Unlike code trees, which interleave
* both phases in an instruction machine, the walk here is a plain map lookup per
* symbol, and the (expensive) unification only runs on the entries the trie
* could not rule out.
**/

package Unif

import (
	"fmt"
	"strings"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Lib"
)

// wildcard is the symbol a metavariable is flattened to. It cannot clash with a
// real symbol, which is always stored prefixed by its kind.
const wildcard = "*"

// symbol is one entry of a flattened term. [arity] is what makes it possible to
// skip over a subterm without rebuilding it.
type symbol struct {
	name  string
	arity int
}

// DiscriminationTree indexes formulas on the preorder flattening of their terms.
type DiscriminationTree struct {
	children map[symbol]*DiscriminationTree
	// formulas ends a path: the entries whose flattening is exactly that path.
	formulas Lib.List[AST.Form]
}

func NewDiscriminationTree() *DiscriminationTree {
	return &DiscriminationTree{children: make(map[symbol]*DiscriminationTree)}
}

/********************/
/* DataStructure    */
/********************/

func (dt *DiscriminationTree) IsEmpty() bool {
	return len(dt.children) == 0 && dt.formulas.Len() == 0
}

func (dt *DiscriminationTree) MakeDataStruct(fl Lib.List[AST.Form], is_pos bool) DataStructure {
	fresh := NewDiscriminationTree()
	for _, f := range fl.GetSlice() {
		switch typed := f.(type) {
		case AST.Pred:
			if is_pos {
				fresh.insert(typed)
			}
		case AST.Not:
			if pred, ok := typed.GetForm().(AST.Pred); ok && !is_pos {
				fresh.insert(pred)
			}
		case TermForm:
			// Equality reasoning indexes bare terms.
			fresh.insert(typed)
		}
	}
	return fresh
}

func (dt *DiscriminationTree) InsertFormulaListToDataStructure(
	fl Lib.List[AST.Form],
) DataStructure {
	for _, f := range fl.GetSlice() {
		switch typed := f.Copy().(type) {
		case AST.Pred:
			dt.insert(typed)
		case AST.Not:
			if pred, ok := typed.GetForm().(AST.Pred); ok {
				dt.insert(pred)
			}
		case TermForm:
			dt.insert(typed)
		}
	}
	return dt
}

func (dt *DiscriminationTree) Copy() DataStructure {
	return dt.deepCopy()
}

func (dt *DiscriminationTree) deepCopy() *DiscriminationTree {
	res := &DiscriminationTree{
		children: make(map[symbol]*DiscriminationTree, len(dt.children)),
		formulas: Lib.ListCpy(dt.formulas),
	}
	for sym, child := range dt.children {
		res.children[sym] = child.deepCopy()
	}
	return res
}

func (dt *DiscriminationTree) Print() {
	debug(Lib.MkLazy(func() string { return dt.toString("") }))
}

func (dt *DiscriminationTree) toString(prefix string) string {
	var b strings.Builder
	for _, f := range dt.formulas.GetSlice() {
		b.WriteString(fmt.Sprintf("%s|- %s\n", prefix, f.ToString()))
	}
	for sym, child := range dt.children {
		b.WriteString(fmt.Sprintf("%s%s/%d\n", prefix, sym.name, sym.arity))
		b.WriteString(child.toString(prefix + "  "))
	}
	return b.String()
}

// Unify returns every indexed formula unifiable with [formula], together with
// the corresponding substitution.
func (dt *DiscriminationTree) Unify(formula AST.Form) (bool, []MixedSubstitutions) {
	query, ok := indexedTerm(formula)
	if !ok {
		return false, []MixedSubstitutions{}
	}

	candidates := []AST.Form{}
	dt.retrieve(flatten(query), 0, &candidates)

	res := []MixedSubstitutions{}
	for _, candidate := range candidates {
		stored, ok := indexedTerm(candidate)
		if !ok {
			continue
		}
		subst := AddUnification(query.Copy(), stored.Copy(), MakeEmptySubstitution())
		if subst.Equals(Failure()) {
			continue
		}
		res = append(res, MakeMatchingSubstitutions(candidate, subst).toMixed())
	}

	return len(res) > 0, res
}

/********************/
/* Flattening       */
/********************/

// indexedTerm is the term a formula is indexed on. Predicates are turned into
// functions the same way the code tree machine does, so both indexes see the
// same shape and type arguments are folded into the term arguments.
func indexedTerm(f AST.Form) (AST.Term, bool) {
	switch typed := f.(type) {
	case AST.Pred:
		return AST.MakerFun(
			typed.GetID(),
			Lib.NewList[AST.Ty](),
			getFunctionalArguments(typed.GetTyArgs(), typed.GetArgs()),
		), true
	case TermForm:
		return typed.GetTerm(), true
	default:
		return nil, false
	}
}

func flatten(t AST.Term) []symbol {
	out := []symbol{}
	flattenInto(t, &out)
	return out
}

func flattenInto(t AST.Term, out *[]symbol) {
	switch typed := t.(type) {
	case AST.Fun:
		*out = append(*out, symbol{name: "f" + typed.GetName(), arity: typed.GetArgs().Len()})
		for _, arg := range typed.GetArgs().GetSlice() {
			flattenInto(arg, out)
		}
	case AST.Meta:
		// Every metavariable is the same wildcard: which one it is cannot be
		// used to discriminate, since it may be bound to anything.
		*out = append(*out, symbol{name: wildcard, arity: 0})
	default:
		*out = append(*out, symbol{name: "c" + t.ToString(), arity: 0})
	}
}

/********************/
/* Insertion        */
/********************/

func (dt *DiscriminationTree) insert(f AST.Form) {
	term, ok := indexedTerm(f)
	if !ok {
		return
	}
	node := dt
	for _, sym := range flatten(term) {
		child, found := node.children[sym]
		if !found {
			child = NewDiscriminationTree()
			node.children[sym] = child
		}
		node = child
	}
	node.formulas.Append(f.Copy())
}

/********************/
/* Retrieval        */
/********************/

// retrieve collects every entry whose path can unify with the query flattening
// starting at position [qi].
//
// Two wildcards have to be handled, and they are not symmetric:
//   - the query holds one: it may be instantiated by any indexed subterm, so we
//     skip one whole subterm in the trie;
//   - the trie holds one: the indexed entry may be instantiated by the query
//     subterm, so we skip one whole subterm in the query.
func (dt *DiscriminationTree) retrieve(query []symbol, qi int, out *[]AST.Form) {
	if qi == len(query) {
		*out = append(*out, dt.formulas.GetSlice()...)
		return
	}

	head := query[qi]

	if head.name == wildcard {
		for _, node := range dt.skipSubterms(1) {
			node.retrieve(query, qi+1, out)
		}
		return
	}

	if child, found := dt.children[head]; found {
		child.retrieve(query, qi+1, out)
	}

	// An indexed metavariable swallows the whole query subterm.
	if child, found := dt.children[symbol{name: wildcard, arity: 0}]; found {
		child.retrieve(query, skipSubterm(query, qi), out)
	}
}

// skipSubterms returns the nodes reached from dt by consuming exactly [pending]
// complete subterms.
func (dt *DiscriminationTree) skipSubterms(pending int) []*DiscriminationTree {
	if pending == 0 {
		return []*DiscriminationTree{dt}
	}
	res := []*DiscriminationTree{}
	for sym, child := range dt.children {
		// Consuming this symbol settles one subterm but opens [sym.arity] more.
		res = append(res, child.skipSubterms(pending-1+sym.arity)...)
	}
	return res
}

// skipSubterm returns the position just after the subterm starting at [qi].
func skipSubterm(query []symbol, qi int) int {
	pending := 1
	for pending > 0 {
		pending += query[qi].arity - 1
		qi++
	}
	return qi
}

/********************/
/* Index selection  */
/********************/

var useDiscriminationTrees = false

// UseDiscriminationTrees makes NewIndex hand out discrimination trees instead of
// code trees.
func UseDiscriminationTrees() { useDiscriminationTrees = true }

// NewIndex builds an empty term index of the currently selected kind. Every
// place that needs an index should go through it rather than pick an
// implementation itself.
func NewIndex() DataStructure {
	if useDiscriminationTrees {
		return NewDiscriminationTree()
	}
	return NewNode()
}

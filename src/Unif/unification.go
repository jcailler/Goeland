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
* This file implements term unification directly on the terms.
*
* The default implementation goes through the code tree machine: unifying two
* terms compiles the first one into a one-branch code tree and runs the matching
* machine on the second (see tryUnification). That is what ties unification to
* the code tree machinery. This file is the counterpart of
* [discrimination-trees.go]: with -dt, no code tree is built at all, neither for
* indexing nor for unifying.
*
* The two implementations must agree, so they are compared against each other in
* the test-suite rather than trusted separately.
**/

package Unif

import (
	"github.com/GoelandProver/Goeland/AST"
)

// resolveBound is a safety net: a cyclic substitution would otherwise make
// resolve spin. Occur-check and Eliminate are supposed to rule that out.
const resolveBound = 1 << 16

// unifyDirect unifies the two terms under the bindings already in [subst],
// returning the extended substitution or Failure.
func unifyDirect(term1, term2 AST.Term, subst Substitutions) Substitutions {
	res := subst.Copy()
	if !unifyTerms(term1.Copy(), term2.Copy(), &res) {
		return Failure()
	}
	EliminateMeta(&res)
	Eliminate(&res)
	if res.Equals(Failure()) {
		return Failure()
	}
	return res
}

func unifyTerms(t1, t2 AST.Term, subst *Substitutions) bool {
	t1 = resolve(t1, *subst)
	t2 = resolve(t2, *subst)

	if t1.Equals(t2) {
		return true
	}

	if meta, ok := t1.(AST.Meta); ok {
		return bindMeta(meta, t2, subst)
	}
	if meta, ok := t2.(AST.Meta); ok {
		return bindMeta(meta, t1, subst)
	}

	fun1, ok1 := t1.(AST.Fun)
	fun2, ok2 := t2.(AST.Fun)
	if !ok1 || !ok2 {
		return false
	}
	if !fun1.GetID().Equals(fun2.GetID()) {
		return false
	}

	// Type arguments are folded into the term arguments, exactly as the code
	// tree machine does when it compiles a term (see parseTerms).
	args1 := getFunctionalArguments(fun1.GetTyArgs(), fun1.GetArgs())
	args2 := getFunctionalArguments(fun2.GetTyArgs(), fun2.GetArgs())
	if args1.Len() != args2.Len() {
		return false
	}
	for i := range args1.GetSlice() {
		if !unifyTerms(args1.At(i), args2.At(i), subst) {
			return false
		}
	}
	return true
}

func bindMeta(meta AST.Meta, term AST.Term, subst *Substitutions) bool {
	if !OccurCheckValid(meta, term) {
		return false
	}
	subst.Set(meta, term)
	return true
}

// resolve follows the bindings of [t] until reaching a term that is not a bound
// metavariable.
func resolve(t AST.Term, subst Substitutions) AST.Term {
	for i := 0; i < resolveBound; i++ {
		meta, ok := t.(AST.Meta)
		if !ok {
			return t
		}
		value, index := subst.Get(meta)
		if index == -1 || value == nil {
			return t
		}
		t = value
	}
	return t
}

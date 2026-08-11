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
* This file implements some useful functions for the plugin.
**/

package dmt

import (
	"fmt"
	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Lib"
)

func isEquality(pred AST.Pred) bool {
	return pred.GetID().Equals(AST.Id_eq)
}

func predFromNegatedAtom(f AST.Form) AST.Pred {
	return f.(AST.Not).GetForm().(AST.Pred)
}

func selectFromPolarity[T any](polarity bool, positive, negative T) T {
	if polarity {
		return positive
	}
	return negative
}

/*
patternKey renders a rewrite rule's left-hand side for use as a key of the rewrite
map. It has to keep the index of a metavariable, which the default printer leaves
out: two axioms read from ! [x] : P(x) <=> ... carry different metavariables that
both print as "P(X)", so they would share a key. Retrieval then answers with both
consequents, and the substitution that matched one rule binds nothing in the
other's -- the rewriting hands back a formula with a free variable that belongs to
another rule.
*/
func patternKey(form AST.Form) string {
	switch typed := form.(type) {
	case AST.Not:
		return "~" + patternKey(typed.GetForm())
	case AST.Pred:
		key := typed.GetID().ToString() + "("
		for i, arg := range typed.GetArgs().GetSlice() {
			if i > 0 {
				key += ","
			}
			key += termKey(arg)
		}
		return key + ")"
	default:
		return form.ToString()
	}
}

func termKey(term AST.Term) string {
	switch typed := term.(type) {
	case AST.Meta:
		return fmt.Sprintf("%s#%d", typed.GetName(), typed.GetIndex())
	case AST.Fun:
		key := typed.GetID().ToString() + "("
		for i, arg := range typed.GetArgs().GetSlice() {
			if i > 0 {
				key += ","
			}
			key += termKey(arg)
		}
		return key + ")"
	default:
		return term.ToString()
	}
}

func rewriteMapInsertion(polarity bool, key string, val AST.Form) {
	rewriteMap := selectFromPolarity(polarity, positiveRewrite, negativeRewrite)

	if _, ok := rewriteMap[key]; !ok {
		rewriteMap[key] = Lib.NewList[AST.Form]()
	}

	ls := rewriteMap[key]
	ls.Append(val)
	rewriteMap[key] = ls
}

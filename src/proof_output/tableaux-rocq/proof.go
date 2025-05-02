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
* This file provides a TableauxRocq proof from Goéland's proof.
**/

package tableauxrocq

import (
	"strings"

	bt "github.com/GoelandProver/Goeland/types/basic-types"
	vp "github.com/GoelandProver/Goeland/visualization_proof"
)

/** TODO
* Step 1 : proof tree
	* Tableaux
	* Follow the tree
	* Keep formulas
	* Add intermediate formulas in case of non-native steps
	* Retrieve all relevant formulas
* Step 2 : proof
	* Tableaux + substitution
	* Replay rules
**/

func makeTableauxRocqProofFromTableaux(proof []vp.ProofStruct) string {
	print(strings.TrimSuffix(makeTableaux(proof, bt.NewFormList()), "\n") + ").\n")
	return ""
}

func makeTableaux(proof []vp.ProofStruct, forms *bt.FormList) string {
	res := ""
	for _, ps := range proof {
		res += makeStep(ps, forms)
		if proofStructRuleToTableauxRocqRules(ps.GetRuleName()) != AX {
			forms.Append(ps.GetFormula().GetForm())
		}
	}
	// children
	if len(proof[len(proof)-1].GetChildren()) > 1 {
		// for _, c := range proof[len(proof)-1].GetChildren() {
		res += makeTableaux(proof[len(proof)-1].GetChildren()[0], forms.Copy())
		// }
	}

	closing_par := ""
	for i := 0; i < len(proof)-1; i++ {
		closing_par += ")"
	}

	return strings.TrimSuffix(res, " \n") + closing_par + "\n"
}

func makeStep(s vp.ProofStruct, forms *bt.FormList) string {
	rule := proofStructRuleToTableauxRocqRules(s.GetRuleName())
	res := ""
	shift := ""
	for i := 0; i < forms.Len(); i++ {
		shift += "  "
	}

	if rule == AX {
		println("Axiom Found")
		res = shift + "(" + TableauxRocqRulesToString(rule) + "\n"
		forms.Remove(forms.Len() - 1)
		res += formListToTableauxRocq(forms.Copy()) + ") \n"
	} else {
		res = shift + "(" + TableauxRocqRulesToString(rule) + "\n"
	}
	return res
}

// add more than once if non native steps --> switch
// Pas de forall ou exists multiples -> faire une fonction de split
// func unfoldProofSteps(proof []vp.ProofStruct) []vp.ProofStruct {
// 	res := make([]vp.ProofStruct, 0)
// 	for _, ps := range proof {
// 		switch proofStructRuleToTableauxRocqRules(ps.Rule_name) {
// 		case ALL:
// 			if ps.GetFormula().GetTerms().Len() > 1 {
// 				for i, v := range ps.GetFormula().GetTerms().Slice() {
// 					tmp_struct := ps.Copy()
// 					tmp_form := bt.MakerAll([]bt.Var{v}, ps.Formula.GetForm())
// 					tmp_children := nil
// 					if i == ps.GetFormula().GetTerms().Len()-1 {
// 						tmp_children = ps.GetChildren()
// 					} else {
// 						tmp_children =
// 					}
// 					tmp_child := bt.MakerAll([]bt.Var{v}, ps.Formula.GetForm())
// 					tmp_struct.SetFormulaProof()
// 					res = append(res, vp.MakeProofStruct())
// 				}
// 			} else {
// 				res = append(res, ps)
// 			}
// 		}
// 	}
// 	return res
// }

func makeLemma() string {
	return ""
}

func makeProof() string {
	return ""
}

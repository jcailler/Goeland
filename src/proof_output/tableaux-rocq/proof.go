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
	"slices"
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
	print(strings.TrimSuffix(makeTableaux(unfoldProofSteps(proof), bt.NewFormList()), "\n") + ").\n")
	return ""
}

func makeTableaux(proof []vp.ProofStruct, forms *bt.FormList) string {
	res := ""
	forms.Append(proof[0].GetFormula().GetForm())
	for _, ps := range proof {
		res += makeStep(ps, forms)
		if proofStructRuleToTableauxRocqRules(ps.GetRuleName()) != AX {
			for _, child := range ps.GetResultFormulas() {
				for _, child_form := range child.GetForms().Slice() {
					forms.Append(child_form)
				}
			}
		}
	}

	if len(proof[len(proof)-1].GetChildren()) > 1 {
		for _, c := range proof[len(proof)-1].GetChildren() {
			res += makeTableaux(c, forms.Copy())
		}
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
	for i := 0; i < forms.Len()-1; i++ {
		shift += "  "
	}

	if rule == AX {
		res = shift + "(" + TableauxRocqRulesToString(rule) + "\n"
		forms.Remove(forms.Len() - 1)
		res += "[" + formListToTableauxRocq(forms.Copy()) + "]) \n"
	} else {
		res = shift + "(" + TableauxRocqRulesToString(rule) + "\n"
	}
	return res
}

func unfoldProofSteps(proof []vp.ProofStruct) []vp.ProofStruct {
	res := make([]vp.ProofStruct, 0)
	for _, ps := range proof {
		switch proofStructRuleToTableauxRocqRules(ps.Rule_name) {
		case ALL:
			if f, ok := ps.GetFormula().GetForm().(bt.All); ok {
				var_list_param := f.GetVarList()
				if len(var_list_param) > 1 {
					tmp_step := ps.Copy()
					child := f.GetForm()
					slices.Reverse(var_list_param)
					for _, v := range var_list_param {
						f_tmp := bt.MakerAll([]bt.Var{v}, child)
						fnt_tmp := bt.MakeFormAndTerm(f_tmp, bt.MakeEmptyTermList())
						child_fnt := bt.MakeFormAndTerm(child, bt.MakeEmptyTermList())
						tmp_step.SetResultFormulasProof([]vp.IntFormAndTermsList{vp.MakeIntFormAndTermsList(-1, bt.MakeSingleElementFormAndTermList(child_fnt))})
						tmp_step.SetFormulaProof(fnt_tmp)
						child = f_tmp
					}
					res = append(res, tmp_step)
				} else {
					res = append(res, ps)
				}
			}
		default:
			res = append(res, ps)
		}
	}
	return res
}

func makeLemma() string {
	return ""
}

func makeProof() string {
	return ""
}

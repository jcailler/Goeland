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
	"fmt"
	"slices"
	"strings"

	treetypes "github.com/GoelandProver/Goeland/code-trees/tree-types"
	bt "github.com/GoelandProver/Goeland/types/basic-types"
	vp "github.com/GoelandProver/Goeland/visualization_proof"
	// gs3"github.com/GoelandProver/Goeland/proof_output/gs3"
	gs3 "github.com/GoelandProver/Goeland/proof_output/gs3"
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

/************ Tableau ************/

func makeTableauxRocqProofFromTableaux(proof []vp.ProofStruct) string {
	final_tableaux, _ := makeTableaux(unfoldProofSteps(proof), bt.NewFormList(), make([]string, 0))
	return strings.TrimSuffix(final_tableaux, "\n")
}

func makeTableaux(proof []vp.ProofStruct, forms *bt.FormList, previous_instantiations []string) (string, []string) {
	res := ""
	forms.Append(proof[0].GetFormula().GetForm())
	for _, ps := range proof {
		res_form, res_subst := makeStepTableau(ps, forms, previous_instantiations)
		previous_instantiations = append(previous_instantiations, res_subst...)
		res += res_form
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
			res_form, res_subst := makeTableaux(c, forms.Copy(), previous_instantiations)
			previous_instantiations = append(previous_instantiations, res_subst...)
			res += res_form
		}
	}

	closing_par := ""
	for i := 0; i < len(proof)-1; i++ {
		closing_par += ")"
	}

	return strings.TrimSuffix(res, " \n") + closing_par + "\n", previous_instantiations
}

func makeStepTableau(s vp.ProofStruct, forms *bt.FormList, previous_instantiations []string) (string, []string) {
	rule := proofStructRuleToTableauxRocqRules(s.GetRuleName())
	res_form := ""
	shift := ""
	for i := 0; i < forms.Len()-1; i++ {
		shift += "  "
	}

	switch rule {

	case AX:
		{
			form_original := forms.Copy().Slice()
			slices.Reverse(form_original)
			form_reverse := bt.NewFormList(form_original...)

			res_form = shift + "(" + TableauxRocqRulesToString(rule) + "\n"
			res_form += shift + "  " + "(" + "Context.make" + "\n"
			forms.Remove(forms.Len() - 1)
			res_form += "([" + formListToTableauxRocq(form_reverse) + "]))) \n"
			res_form += "([" + substListToTableauxRocq(previous_instantiations) + "])\n"
		}
	case EX:
		{
			form_as_ex := s.GetFormula().GetForm()
			println(form_as_ex.ToString())
			println(s.GetResultFormulas()[0].GetForms().Get(0).ToString())
			new_ss := gs3.ManageDeltasSkolemisations(form_as_ex, s.GetResultFormulas()[0].GetForms().Get(0))
			previous_instantiations = append(previous_instantiations, "(" + new_ss.GetName() + ", " + formToTableauxRocq(form_as_ex) + ")")
			res_form = shift + "(" + TableauxRocqRulesToString(rule) + "\n"
		}

	default:
		{
			res_form = shift + "(" + TableauxRocqRulesToString(rule) + "\n"
		}
	}
	return res_form, previous_instantiations
}

// Update formulas ALL and EX in a form
func updateAllInForm(f bt.Form) bt.Form {
	switch nf := f.(type) {
	case bt.Not:
		return bt.MakerNot(updateAllInForm(nf.GetForm()))
	case bt.And:
		res_list := make([]bt.Form, 0)
		for _, f2 := range nf.GetChildFormulas().Slice() {
			res_list = append(res_list, updateAllInForm(f2))
		}
		return bt.MakerAnd(bt.NewFormList(res_list...))
	case bt.Or:
		res_list := make([]bt.Form, 0)
		for _, f2 := range nf.GetChildFormulas().Slice() {
			res_list = append(res_list, updateAllInForm(f2))
		}
		return bt.MakerOr(bt.NewFormList(res_list...))
	case bt.Imp:
		f1 := updateAllInForm(nf.GetF1())
		f2 := updateAllInForm(nf.GetF2())
		return bt.MakerImp(f1, f2)
	case bt.Equ:
		f1 := updateAllInForm(nf.GetF1())
		f2 := updateAllInForm(nf.GetF2())
		return bt.MakerEqu(f1, f2)
	case bt.Ex:
		f_tmp := nf.Copy()
		var_list_param := nf.GetVarList()
		if len(var_list_param) > 1 {
			child := updateAllInForm(nf.GetForm())
			slices.Reverse(var_list_param)
			for _, v := range var_list_param {
				f_tmp = bt.MakerEx([]bt.Var{v}, child)
				child = f_tmp
			}
		}
		return f_tmp
	case bt.All:
		f_tmp := nf.Copy()
		var_list_param := nf.GetVarList()
		if len(var_list_param) > 1 {
			child := updateAllInForm(nf.GetForm())
			slices.Reverse(var_list_param)
			for _, v := range var_list_param {
				f_tmp = bt.MakerAll([]bt.Var{v}, child)
				child = f_tmp
			}
		}
		return f_tmp
	default:
		return f.Copy()
	}
}

// Update formulas ALL and EX in  a list of list of forms
func updateAllInResultingForm(rfl []vp.IntFormAndTermsList) []vp.IntFormAndTermsList {
	tmp_resulting_forms := make([]vp.IntFormAndTermsList, 0)
	for _, rf := range rfl {
		tmp_resulting_forms_aux := vp.MakeIntFormAndTermsList(rf.GetI(), nil)
		for _, rf2 := range rf.GetFL() {
			tmp_resulting_forms_aux.Add(bt.MakeFormAndTerm(updateAllInForm(rf2.GetForm()), rf2.GetTerms()))
		}
		tmp_resulting_forms = append(tmp_resulting_forms, tmp_resulting_forms_aux)
	}
	return tmp_resulting_forms
}

// Add formulas in the branch for non-trivial steps management
func unfoldProofStep(ps vp.ProofStruct) vp.ProofStruct {
	tmp_form := bt.MakeFormAndTerm(updateAllInForm(ps.GetFormula().GetForm().Copy()), ps.GetFormula().GetTerms())
	tmp_resulting_forms := updateAllInResultingForm(ps.GetResultFormulas())
	tmp_step := ps.Copy()
	tmp_step.SetFormulaProof(tmp_form)
	tmp_step.SetResultFormulasProof(tmp_resulting_forms)
	tmp_step.SetChildrenProof(nil)

	switch t := ps.GetFormula().GetForm().(type) {
	case bt.And: // A, B -> A, B, ~A, ~B
		new_resulting_forms := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[0].GetI(), nil)
		a := tmp_step.GetResultFormulas()[0].GetFL()[0]
		b := tmp_step.GetResultFormulas()[0].GetFL()[1]
		new_resulting_forms.Add(bt.MakeFormAndTerm(bt.MakerNot(b.GetForm()), b.GetTerms()))
		new_resulting_forms.Add(bt.MakeFormAndTerm(bt.MakerNot(a.GetForm()), a.GetTerms()))
		new_resulting_forms.Add(b)
		new_resulting_forms.Add(a)
		tmp_step.SetResultFormulasProof([]vp.IntFormAndTermsList{new_resulting_forms})
	case bt.Equ: // ~B ~A, A B ==>  ~B ~A A -> B B -> A ~~(A -> B) ~~(B -> A) , A B A -> B B -> A ~~(A -> B)
		neg_b := tmp_step.GetResultFormulas()[0].GetFL()[0]
		neg_a := tmp_step.GetResultFormulas()[0].GetFL()[1]
		a := tmp_step.GetResultFormulas()[1].GetFL()[0]
		b := tmp_step.GetResultFormulas()[1].GetFL()[1]

		terms_a_imp_b := a.GetTerms().Copy()
		terms_a_imp_b.Merge(b.GetTerms().List)

		terms_b_imp_a := b.GetTerms().Copy()
		terms_b_imp_a.Merge(a.GetTerms().List)

		b_imp_a := bt.MakerImp(b.GetForm(), a.GetForm())
		a_imp_b := bt.MakerImp(a.GetForm(), b.GetForm())
		b_imp_a_fnt := bt.MakeFormAndTerm(b_imp_a, terms_b_imp_a)
		a_imp_b_fnt := bt.MakeFormAndTerm(a_imp_b, terms_a_imp_b)

		neg_neg_b_imp_a := bt.MakeFormAndTerm(bt.MakerNot(bt.MakerNot(b_imp_a)), terms_b_imp_a)
		neg_neg_a_imp_b := bt.MakeFormAndTerm(bt.MakerNot(bt.MakerNot(a_imp_b)), terms_a_imp_b)
		c1 := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[0].GetI(), bt.FormAndTermsList{neg_b, neg_a, a_imp_b_fnt, b_imp_a_fnt, neg_neg_a_imp_b, neg_neg_b_imp_a})
		c2 := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[1].GetI(), bt.FormAndTermsList{a, b, a_imp_b_fnt, b_imp_a_fnt, neg_neg_a_imp_b, neg_neg_b_imp_a})
		tmp_step.SetResultFormulasProof([]vp.IntFormAndTermsList{c2, c1})
	case bt.Ex: // A -> A, ~~A
		a := tmp_step.GetResultFormulas()[0].GetFL()[0]
		neg_neg_a := (bt.MakeFormAndTerm(bt.MakerNot(bt.MakerNot(a.GetForm())), a.GetTerms()))
		new_resulting_forms := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[0].GetI(), nil)
		new_resulting_forms.Add(neg_neg_a)
		new_resulting_forms.Add(a)
		tmp_step.SetResultFormulasProof([]vp.IntFormAndTermsList{new_resulting_forms})
	case bt.Not:
		switch tt := t.GetForm().(type) {
		case bt.Top: // ~T -> ~~B
			new_resulting_forms := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[0].GetI(), nil)
			new_resulting_forms.Add(bt.MakeFormAndTerm(bt.MakerNot(bt.MakerNot(bt.MakerBot())), bt.MakeEmptyTermList()))
			new_resulting_forms.Add(bt.MakeFormAndTerm(bt.MakerNot(bt.MakerTop()), bt.MakeEmptyTermList()))
			tmp_step.SetResultFormulasProof([]vp.IntFormAndTermsList{new_resulting_forms})
		case bt.And: // ~A, ~B -> ~A ~A \/ ~B, ~B ~A \/ ~B
			neg_a := tmp_step.GetResultFormulas()[0].GetForms().Get(0)
			neg_b := tmp_step.GetResultFormulas()[1].GetForms().Get(0)
			terms_neg_a_or_neg_b := tmp_step.GetResultFormulas()[0].GetFL()[0].GetTerms().Copy()
			terms_neg_a_or_neg_b.Merge(tmp_step.GetResultFormulas()[1].GetFL()[0].GetTerms().List)

			neg_a_or_b := bt.MakerOr(bt.NewFormList(neg_a, neg_b))
			c1 := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[0].GetI(), bt.FormAndTermsList{bt.MakeFormAndTerm(neg_a, tmp_step.GetResultFormulas()[0].GetFL()[0].GetTerms()), bt.MakeFormAndTerm(neg_a_or_b, terms_neg_a_or_neg_b)})
			c2 := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[1].GetI(), bt.FormAndTermsList{bt.MakeFormAndTerm(neg_b, tmp_step.GetResultFormulas()[1].GetFL()[0].GetTerms()), bt.MakeFormAndTerm(neg_a_or_b, terms_neg_a_or_neg_b)})
			tmp_step.SetResultFormulasProof([]vp.IntFormAndTermsList{c2, c1})
		case bt.Imp: // A, ~B -> A ~~A, ~B
			new_resulting_forms := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[0].GetI(), nil)
			a := tmp_step.GetResultFormulas()[0].GetFL()[0]
			neg_neg_a := (bt.MakeFormAndTerm(bt.MakerNot(bt.MakerNot(a.GetForm())), a.GetTerms()))
			neg_b := tmp_step.GetResultFormulas()[0].GetFL()[1]
			new_resulting_forms.Add(neg_b)
			new_resulting_forms.Add(neg_neg_a)
			new_resulting_forms.Add(a)
			tmp_step.SetResultFormulasProof([]vp.IntFormAndTermsList{new_resulting_forms})
		case bt.Equ: // A ~B, B ~A ==> A ~~A ~B ~(A -> B) OR(~(A -> B) ~(B -> A)), B ~~B ~A ~(B -> A) OR(~(A -> B) ~(B -> A))
			a := tmp_step.GetResultFormulas()[0].GetFL()[0]
			neg_b := tmp_step.GetResultFormulas()[0].GetFL()[1]
			b := tmp_step.GetResultFormulas()[1].GetFL()[0]
			neg_a := tmp_step.GetResultFormulas()[1].GetFL()[1]

			neg_neg_a := bt.MakeFormAndTerm(bt.MakerNot(bt.MakerNot(a.GetForm())), a.GetTerms())
			neg_neg_b := bt.MakeFormAndTerm(bt.MakerNot(bt.MakerNot(b.GetForm())), b.GetTerms())

			b_imp_a := bt.MakerImp(b.GetForm(), a.GetForm())
			a_imp_b := bt.MakerImp(a.GetForm(), b.GetForm())
			neg_b_imp_a := bt.MakerNot(b_imp_a)
			neg_a_imp_b := bt.MakerNot(a_imp_b)

			terms_neg_a_imp_b := a.GetTerms().Copy()
			terms_neg_a_imp_b.Merge(b.GetTerms().List)

			terms_neg_b_imp_a := b.GetTerms().Copy()
			terms_neg_b_imp_a.Merge(a.GetTerms().List)

			neg_b_imp_a_fnt := bt.MakeFormAndTerm(neg_b_imp_a, terms_neg_b_imp_a)
			neg_a_imp_b_fnt := bt.MakeFormAndTerm(neg_a_imp_b, terms_neg_a_imp_b)
			or_neg_imp := bt.MakeFormAndTerm(bt.MakerOr(bt.NewFormList(neg_a_imp_b, neg_b_imp_a)), terms_neg_a_imp_b)

			c1 := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[0].GetI(), bt.FormAndTermsList{a, neg_neg_a, neg_b, neg_a_imp_b_fnt, or_neg_imp})
			c2 := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[1].GetI(), bt.FormAndTermsList{b, neg_neg_b, neg_a, neg_b_imp_a_fnt, or_neg_imp})
			tmp_step.SetResultFormulasProof([]vp.IntFormAndTermsList{c2, c1})
		case bt.Ex: // ~A -> ~A, Vx ~A
			neg_a := tmp_step.GetResultFormulas()[0].GetFL()[0]
			forall_neg_a := bt.MakeFormAndTerm(bt.MakerAll(tt.GetVarList(), tt.GetForm()), neg_a.GetTerms())
			new_resulting_forms := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[0].GetI(), nil)
			new_resulting_forms.Add(neg_a)
			new_resulting_forms.Add(forall_neg_a)
			tmp_step.SetResultFormulasProof([]vp.IntFormAndTermsList{new_resulting_forms})
		}
	}
	return tmp_step
}

// Iterate on all proof steps
func unfoldProofSteps(ps []vp.ProofStruct) []vp.ProofStruct {
	new_proof := make([]vp.ProofStruct, 0)
	for _, ps := range ps {
		new_step := unfoldProofStep(ps)
		new_child := make([][]vp.ProofStruct, 0)
		for _, c := range ps.GetChildren() {
			new_child = append(new_child, unfoldProofSteps(c))
		}
		new_step.SetChildrenProof(new_child)

		new_proof = append(new_proof, new_step)
	}

	return new_proof
}

/************ Substitution ************/
func makeSubst(m bt.Meta, t bt.Term) string {
	return fmt.Sprintf("(\"%v\" , Term.const \" %v\")", m.GetName(), t.ToString())
}

func makeGlobalSubst(sub treetypes.Substitutions) string {
	res := "Substitution.from_list (["

	for i, s := range sub {
		res += makeSubst(s.Get())
		if i < len(sub)-1 {
			res += "; "
		}
	}

	res += "]) _ .\n"
	return res
}

/************ Lemma ************/

func makeStepInLemma(s vp.ProofStruct) string {
	switch s.GetFormula().GetForm().(type) {
	case bt.All:
		return "All"
	default:
		return "Admit."
	}
}

func makeLemma(proof []vp.ProofStruct) string {
	res := ""
	res += "econstructor; eauto.\n"

	for _, s := range proof {
		res += makeStepInLemma(s) + "\n"
	}

	return res
}

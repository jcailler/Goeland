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
* This file provides TableauxRocq's output
**/

package tableauxrocq

import (
	"fmt"
	"strings"

	// "strings"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Core"
	"github.com/GoelandProver/Goeland/Glob"
	"github.com/GoelandProver/Goeland/Lib"
	"github.com/GoelandProver/Goeland/Search"
	"github.com/GoelandProver/Goeland/Unif"
)

/************ Formula ************/
func makeFormula(prf Search.IProof) string {
	res := FormToTR(prf.AppliedOn())
	return fmt.Sprintf("	%v \n", res) 
}

/************ Substitution ************/
func makeSubst(m AST.Meta, t AST.Term) string {
	return fmt.Sprintf("(\"%v\", %v)", m.ToString(), TermToTR(t))
}

func makeGlobalSubst(sub Unif.Substitutions) string {
	var res strings.Builder
	res.WriteString("[")

	for i, s := range sub {
		res.WriteString(makeSubst(s.Get()))
		if i < len(sub)-1 {
			res.WriteString("; ")
		}
	}

	res.WriteString("].\n")
	return res.String()
}

func extractTermsFromSubstList(sub Unif.Substitutions) (Lib.List[AST.Meta], Lib.List[AST.Term]) {
	return sub.GetMeta(), Core.GetGeneratedSymbolSkolemization()
}

/************ Proof ************/

// TODO: Keep list of used formula to get the right index
func makeStepInProof(s Search.IProof, form_list Lib.List[int]) (string, Lib.List[Lib.List[int]]) {
	Glob.PrintInfo("MakeStep", "-----------------------------")
	Glob.PrintInfo("MakeStep", fmt.Sprintf("Rule %v - Form %v (ID: %v)", s.(Search.TableauxProof)[0].Rule_name, s.AppliedOn().ToString(), s.AppliedOn().GetIndex()))
	Glob.PrintInfo("MakeStep", "Form list : ")
	for _, v := range form_list.GetSlice() {
        Glob.PrintInfo("MakeStep", fmt.Sprintf("%v ",v))
    }

	Glob.PrintInfo("MakeStep", "Children: ")
	for _, branch := range s.Children().GetSlice() {
		for _, child := range branch.Children().GetSlice() {
			Glob.PrintInfo("MakeStep", fmt.Sprintf("%v (ID: %v)", child.AppliedOn().ToString(), child.AppliedOn().GetIndex()))
		}
	}

	new_form_list := Lib.NewList[Lib.List[int]]()
	l1 := form_list.Copy(func(i int) int {return i})
	// l2 := Lib.NewList[int]()

	index := form_list.IndexOf(s.AppliedOn().GetIndex(), func(i1, i2 int) bool {return i1 == i2})
	real_index := -1

	switch index_t := index.(type) {
		case Lib.Some[int]:
			real_index = index_t.Val - form_list.Len()
		case Lib.None[int]:
			Glob.Anomaly("TR", "Index not found in MakeStep")
	}


	// Manage tab formula id
	// check fs.getform id
	// check index in the list
	// tab t[i] = rule id
	// On garde tout ! Et les indices c'est la distance par rapport à la dernière formule ajoutée
    // Par exemple on a (Gamma ,, F) et tu veux appliquer sur F, tu dois donner l'indice 0
	// Get the right index : len - indexOf
	switch s.RuleApplied()  {
	case Search.RuleClosure:
		return "Closure", new_form_list
	case Search.RuleNotNot:
		return "Not Not", new_form_list
	case Search.RuleNotOr:
		return "Not Or", new_form_list
	case Search.RuleNotImp:
		res := fmt.Sprintf("eapply hasTableauNegImp with (i := %v).\n", real_index)
		res += "1: { reflexivity. }"
		l1.Append(s.ResultFormulas().At(0).At(0).GetIndex())
		l1.Append(s.ResultFormulas().At(0).At(1).GetIndex())
		new_form_list.Append(l1)

		return res, new_form_list
	case Search.RuleAnd:
		return "And", new_form_list
	case Search.RuleNotAnd:
		return "Not And", new_form_list
	case Search.RuleNotEqu:
		return "Not Equ", new_form_list
	case Search.RuleOr:
		return "Or", new_form_list
	case Search.RuleImp:
		return "Imply", new_form_list
	case Search.RuleEqu:
		return "Equiv",new_form_list
	case Search.RuleNotEx:
		res := fmt.Sprintf("eapply hasTableauNegEx with (i := %v).\n", real_index)
		res += "1: { reflexivity. }\n"
		res += "1: { set_decide. }"
		l1.Append(s.ResultFormulas().At(0).At(0).GetIndex())
		new_form_list.Append(l1)

		return res, new_form_list
	case Search.RuleAll:
		return "Forall",new_form_list
	case Search.RuleNotAll:
		res := fmt.Sprintf("eapply hasTableauNegAll with (i := %v).\n", real_index)
		res += "1, 2: shelve.\n"
		res += "1: exact TODO.\n"
		res += "1, 2: reflexivity.\n"
		l1.Append(s.ResultFormulas().At(0).At(0).GetIndex())
		new_form_list.Append(l1)

		return res, new_form_list
	case Search.RuleEx:
		res := fmt.Sprintf("eapply hasTableauEx with (i := %v).", real_index)
		l1.Append(s.ResultFormulas().At(0).At(0).GetIndex())
		new_form_list.Append(l1)

		return res, new_form_list
	case Search.RuleReintro: 
		return "Reintroduction", new_form_list
	default:
		return "Error Admit.", new_form_list
	}
}

func makeProof(prf Search.IProof, sub Unif.Substitutions) string {
	res := ""
	var_list, sko_list := extractTermsFromSubstList(sub)

	var_str := ""
	for _, v := range var_list.GetSlice() {
		var_str += fmt.Sprintf(" \"%v\" ", v.ToString())
	}

	sko_str := ""
	for _, s := range sko_list.GetSlice() {
		sko_str += fmt.Sprintf(" \"%v\" ", s.GetName())
	}

	res += fmt.Sprintf("exists \\{%v\\}, \\{%v\\}.\n", var_str, sko_str)

	return makeProofAux(prf, Lib.NewList[int]())
}

func makeProofAux(prf Search.IProof, form_list Lib.List[int]) string {
	res := ""
	form_list.Append(prf.AppliedOn().GetIndex())
	res2, generated_formulas := makeStepInProof(prf, form_list) 
	
	res = res + "\n" + res2 + "\n"

	for i, s := range prf.Children().GetSlice() {
		res_child, _ := makeStepInProof(s, generated_formulas.At(i))
		res += res_child + "\n"
	}	
	return res

}

// func makeFormula(prf Search.TableauxProof) string {
// 	final_tableaux, _ := makeTableaux(unfoldProofSteps(prf), Lib.NewList[AST.Form](), make([]string, 0))
// 	return strings.TrimSuffix(final_tableaux, "\n")
// }

// func makeTableaux(prf Search.TableauxProof, forms Lib.List[AST.Form], previous_instantiations []string) (string, []string) {
// 	res := ""
// 	forms.Append(prf[0].GetFormula().GetForm())
// 	for _, ps := range prf {
// 		res_form, res_subst := makeStepTableau(ps, forms, previous_instantiations)
// 		previous_instantiations = mergeIfNotContains(previous_instantiations, res_subst)
// 		res += res_form
// 		if proofStructRuleToTableauxRocqRules(ps.GetRuleName()) != AX {
// 			for _, child := range ps.GetResultFormulas() {
// 				for _, child_form := range child.GetForms().Slice() {
// 					forms.Append(child_form)
// 				}
// 			}
// 		}
// 	}
//
// 	if len(proof[len(proof)-1].GetChildren()) > 1 {
// 		for _, c := range proof[len(proof)-1].GetChildren() {
// 			res_form, res_subst := makeTableaux(c, forms.Copy(), previous_instantiations)
// 			previous_instantiations = mergeIfNotContains(previous_instantiations, res_subst)
// 			res += res_form
// 		}
// 	}
//
// 	closing_par := ""
// 	for i := 0; i < len(proof)-1; i++ {
// 		closing_par += ")"
// 	}
//
// 	return strings.TrimSuffix(res, " \n") + closing_par + "\n", previous_instantiations
// }

// func makeStepTableau(s vp.ProofStruct, forms *bt.FormList, previous_instantiations []string) (string, []string) {
// 	rule := proofStructRuleToTableauxRocqRules(s.GetRuleName())
// 	res_form := ""
// 	shift := ""
// 	for i := 0; i < forms.Len()-1; i++ {
// 		shift += "  "
// 	}
//
// 	switch rule {
//
// 	case AX:
// 		{
// 			form_original := forms.Copy().Slice()
// 			slices.Reverse(form_original)
// 			form_reverse := bt.NewFormList(form_original...)
//
// 			res_form = shift + "(" + TableauxRocqRulesToString(rule) + "\n"
// 			res_form += shift + "  " + "(" + "Context.make" + "\n"
// 			forms.Remove(forms.Len() - 1)
// 			res_form += "([" + formListToTableauxRocq(form_reverse) + "]) \n"
// 			res_form += "([" + substListToTableauxRocq(previous_instantiations) + "])))\n"
// 		}
// 	case EX:
// 		{
// 			form_as_ex := s.GetFormula().GetForm()
// 			new_ss := gs3.ManageDeltasSkolemisations(form_as_ex, s.GetResultFormulas()[0].GetForms().Get(1))
// 			previous_instantiations = append(previous_instantiations, "(\"" + new_ss.GetName() + "\", " + formToTableauxRocq(form_as_ex) + ")")
// 			res_form = shift + "(" + TableauxRocqRulesToString(rule) + "\n"
// 		}
// 	default:
// 		{
// 			res_form = shift + "(" + TableauxRocqRulesToString(rule) + "\n"
// 		}
// 	}
// 	return res_form, previous_instantiations
// }

// Update formulas ALL and EX in a form
// func updateAllInForm(f bt.Form) bt.Form {
// 	switch nf := f.(type) {
// 	case bt.Not:
// 		return bt.MakerNot(updateAllInForm(nf.GetForm()))
// 	case bt.And:
// 		res_list := make([]bt.Form, 0)
// 		for _, f2 := range nf.GetChildFormulas().Slice() {
// 			res_list = append(res_list, updateAllInForm(f2))
// 		}
// 		return bt.MakerAnd(bt.NewFormList(res_list...))
// 	case bt.Or:
// 		res_list := make([]bt.Form, 0)
// 		for _, f2 := range nf.GetChildFormulas().Slice() {
// 			res_list = append(res_list, updateAllInForm(f2))
// 		}
// 		return bt.MakerOr(bt.NewFormList(res_list...))
// 	case bt.Imp:
// 		f1 := updateAllInForm(nf.GetF1())
// 		f2 := updateAllInForm(nf.GetF2())
// 		return bt.MakerImp(f1, f2)
// 	case bt.Equ:
// 		f1 := updateAllInForm(nf.GetF1())
// 		f2 := updateAllInForm(nf.GetF2())
// 		return bt.MakerEqu(f1, f2)
// 	case bt.Ex:
// 		f_tmp := nf.Copy()
// 		var_list_param := nf.GetVarList()
// 		if len(var_list_param) > 1 {
// 			child := updateAllInForm(nf.GetForm())
// 			slices.Reverse(var_list_param)
// 			for _, v := range var_list_param {
// 				f_tmp = bt.MakerEx([]bt.Var{v}, child)
// 				child = f_tmp
// 			}
// 		}
// 		return f_tmp
// 	case bt.All:
// 		f_tmp := nf.Copy()
// 		var_list_param := nf.GetVarList()
// 		if len(var_list_param) > 1 {
// 			child := updateAllInForm(nf.GetForm())
// 			slices.Reverse(var_list_param)
// 			for _, v := range var_list_param {
// 				f_tmp = bt.MakerAll([]bt.Var{v}, child)
// 				child = f_tmp
// 			}
// 		}
// 		return f_tmp
// 	default:
// 		return f.Copy()
// 	}
// }

// Update formulas ALL and EX in  a list of list of forms
// func updateAllInResultingForm(rfl []vp.IntFormAndTermsList) []vp.IntFormAndTermsList {
// 	tmp_resulting_forms := make([]vp.IntFormAndTermsList, 0)
// 	for _, rf := range rfl {
// 		tmp_resulting_forms_aux := vp.MakeIntFormAndTermsList(rf.GetI(), nil)
// 		for _, rf2 := range rf.GetFL() {
// 			tmp_resulting_forms_aux.Add(bt.MakeFormAndTerm(updateAllInForm(rf2.GetForm()), rf2.GetTerms()))
// 		}
// 		tmp_resulting_forms = append(tmp_resulting_forms, tmp_resulting_forms_aux)
// 	}
// 	return tmp_resulting_forms
// }

// Add formulas in the branch for non-trivial steps management
// func unfoldProofStep(ps vp.ProofStruct) vp.ProofStruct {
// 	tmp_form := bt.MakeFormAndTerm(updateAllInForm(ps.GetFormula().GetForm().Copy()), ps.GetFormula().GetTerms())
// 	tmp_resulting_forms := updateAllInResultingForm(ps.GetResultFormulas())
// 	tmp_step := ps.Copy()
// 	tmp_step.SetFormulaProof(tmp_form)
// 	tmp_step.SetResultFormulasProof(tmp_resulting_forms)
// 	tmp_step.SetChildrenProof(nil)
//
// 	switch t := ps.GetFormula().GetForm().(type) {
// 	case bt.And: // A, B -> A, B, ~A, ~B
// 		new_resulting_forms := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[0].GetI(), nil)
// 		a := tmp_step.GetResultFormulas()[0].GetFL()[0]
// 		b := tmp_step.GetResultFormulas()[0].GetFL()[1]
// 		new_resulting_forms.Add(bt.MakeFormAndTerm(bt.MakerNot(b.GetForm()), b.GetTerms()))
// 		new_resulting_forms.Add(bt.MakeFormAndTerm(bt.MakerNot(a.GetForm()), a.GetTerms()))
// 		new_resulting_forms.Add(b)
// 		new_resulting_forms.Add(a)
// 		tmp_step.SetResultFormulasProof([]vp.IntFormAndTermsList{new_resulting_forms})
// 	case bt.Equ: // ~B ~A, A B ==>  ~B ~A A -> B B -> A ~~(A -> B) ~~(B -> A) , A B A -> B B -> A ~~(A -> B)
// 		neg_b := tmp_step.GetResultFormulas()[0].GetFL()[0]
// 		neg_a := tmp_step.GetResultFormulas()[0].GetFL()[1]
// 		a := tmp_step.GetResultFormulas()[1].GetFL()[0]
// 		b := tmp_step.GetResultFormulas()[1].GetFL()[1]
//
// 		terms_a_imp_b := a.GetTerms().Copy()
// 		terms_a_imp_b.Merge(b.GetTerms().List)
//
// 		terms_b_imp_a := b.GetTerms().Copy()
// 		terms_b_imp_a.Merge(a.GetTerms().List)
//
// 		b_imp_a := bt.MakerImp(b.GetForm(), a.GetForm())
// 		a_imp_b := bt.MakerImp(a.GetForm(), b.GetForm())
// 		b_imp_a_fnt := bt.MakeFormAndTerm(b_imp_a, terms_b_imp_a)
// 		a_imp_b_fnt := bt.MakeFormAndTerm(a_imp_b, terms_a_imp_b)
//
// 		neg_neg_b_imp_a := bt.MakeFormAndTerm(bt.MakerNot(bt.MakerNot(b_imp_a)), terms_b_imp_a)
// 		neg_neg_a_imp_b := bt.MakeFormAndTerm(bt.MakerNot(bt.MakerNot(a_imp_b)), terms_a_imp_b)
// 		c1 := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[0].GetI(), bt.FormAndTermsList{neg_b, neg_a, a_imp_b_fnt, b_imp_a_fnt, neg_neg_a_imp_b, neg_neg_b_imp_a})
// 		c2 := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[1].GetI(), bt.FormAndTermsList{a, b, a_imp_b_fnt, b_imp_a_fnt, neg_neg_a_imp_b, neg_neg_b_imp_a})
// 		tmp_step.SetResultFormulasProof([]vp.IntFormAndTermsList{c2, c1})
// 	case bt.Ex: // A -> A, ~~A
// 		a := tmp_step.GetResultFormulas()[0].GetFL()[0]
// 		neg_neg_a := (bt.MakeFormAndTerm(bt.MakerNot(bt.MakerNot(a.GetForm())), a.GetTerms()))
// 		new_resulting_forms := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[0].GetI(), nil)
// 		new_resulting_forms.Add(neg_neg_a)
// 		new_resulting_forms.Add(a)
// 		tmp_step.SetResultFormulasProof([]vp.IntFormAndTermsList{new_resulting_forms})
// 	case bt.Not:
// 		switch tt := t.GetForm().(type) {
// 		case bt.Top: // ~T -> ~~B
// 			new_resulting_forms := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[0].GetI(), nil)
// 			new_resulting_forms.Add(bt.MakeFormAndTerm(bt.MakerNot(bt.MakerNot(bt.MakerBot())), bt.MakeEmptyTermList()))
// 			new_resulting_forms.Add(bt.MakeFormAndTerm(bt.MakerNot(bt.MakerTop()), bt.MakeEmptyTermList()))
// 			tmp_step.SetResultFormulasProof([]vp.IntFormAndTermsList{new_resulting_forms})
// 		case bt.And: // ~A, ~B -> ~A ~A \/ ~B, ~B ~A \/ ~B
// 			neg_a := tmp_step.GetResultFormulas()[0].GetForms().Get(0)
// 			neg_b := tmp_step.GetResultFormulas()[1].GetForms().Get(0)
// 			terms_neg_a_or_neg_b := tmp_step.GetResultFormulas()[0].GetFL()[0].GetTerms().Copy()
// 			terms_neg_a_or_neg_b.Merge(tmp_step.GetResultFormulas()[1].GetFL()[0].GetTerms().List)
//
// 			neg_a_or_b := bt.MakerOr(bt.NewFormList(neg_a, neg_b))
// 			c1 := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[0].GetI(), bt.FormAndTermsList{bt.MakeFormAndTerm(neg_a, tmp_step.GetResultFormulas()[0].GetFL()[0].GetTerms()), bt.MakeFormAndTerm(neg_a_or_b, terms_neg_a_or_neg_b)})
// 			c2 := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[1].GetI(), bt.FormAndTermsList{bt.MakeFormAndTerm(neg_b, tmp_step.GetResultFormulas()[1].GetFL()[0].GetTerms()), bt.MakeFormAndTerm(neg_a_or_b, terms_neg_a_or_neg_b)})
// 			tmp_step.SetResultFormulasProof([]vp.IntFormAndTermsList{c2, c1})
// 		case bt.Imp: // A, ~B -> A ~~A, ~B
// 			new_resulting_forms := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[0].GetI(), nil)
// 			a := tmp_step.GetResultFormulas()[0].GetFL()[0]
// 			neg_neg_a := (bt.MakeFormAndTerm(bt.MakerNot(bt.MakerNot(a.GetForm())), a.GetTerms()))
// 			neg_b := tmp_step.GetResultFormulas()[0].GetFL()[1]
// 			new_resulting_forms.Add(neg_b)
// 			new_resulting_forms.Add(neg_neg_a)
// 			new_resulting_forms.Add(a)
// 			tmp_step.SetResultFormulasProof([]vp.IntFormAndTermsList{new_resulting_forms})
// 		case bt.Equ: // A ~B, B ~A ==> A ~~A ~B ~(A -> B) OR(~(A -> B) ~(B -> A)), B ~~B ~A ~(B -> A) OR(~(A -> B) ~(B -> A))
// 			a := tmp_step.GetResultFormulas()[0].GetFL()[0]
// 			neg_b := tmp_step.GetResultFormulas()[0].GetFL()[1]
// 			b := tmp_step.GetResultFormulas()[1].GetFL()[0]
// 			neg_a := tmp_step.GetResultFormulas()[1].GetFL()[1]
//
// 			neg_neg_a := bt.MakeFormAndTerm(bt.MakerNot(bt.MakerNot(a.GetForm())), a.GetTerms())
// 			neg_neg_b := bt.MakeFormAndTerm(bt.MakerNot(bt.MakerNot(b.GetForm())), b.GetTerms())
//
// 			b_imp_a := bt.MakerImp(b.GetForm(), a.GetForm())
// 			a_imp_b := bt.MakerImp(a.GetForm(), b.GetForm())
// 			neg_b_imp_a := bt.MakerNot(b_imp_a)
// 			neg_a_imp_b := bt.MakerNot(a_imp_b)
//
// 			terms_neg_a_imp_b := a.GetTerms().Copy()
// 			terms_neg_a_imp_b.Merge(b.GetTerms().List)
//
// 			terms_neg_b_imp_a := b.GetTerms().Copy()
// 			terms_neg_b_imp_a.Merge(a.GetTerms().List)
//
// 			neg_b_imp_a_fnt := bt.MakeFormAndTerm(neg_b_imp_a, terms_neg_b_imp_a)
// 			neg_a_imp_b_fnt := bt.MakeFormAndTerm(neg_a_imp_b, terms_neg_a_imp_b)
// 			or_neg_imp := bt.MakeFormAndTerm(bt.MakerOr(bt.NewFormList(neg_a_imp_b, neg_b_imp_a)), terms_neg_a_imp_b)
//
// 			c1 := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[0].GetI(), bt.FormAndTermsList{a, neg_neg_a, neg_b, neg_a_imp_b_fnt, or_neg_imp})
// 			c2 := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[1].GetI(), bt.FormAndTermsList{b, neg_neg_b, neg_a, neg_b_imp_a_fnt, or_neg_imp})
// 			tmp_step.SetResultFormulasProof([]vp.IntFormAndTermsList{c2, c1})
// 		case bt.Ex: // ~A -> ~A, Vx ~A
// 			neg_a := tmp_step.GetResultFormulas()[0].GetFL()[0]
// 			forall_neg_a := bt.MakeFormAndTerm(bt.MakerAll(tt.GetVarList(), tt.GetForm()), neg_a.GetTerms())
// 			new_resulting_forms := vp.MakeIntFormAndTermsList(ps.GetResultFormulas()[0].GetI(), nil)
// 			new_resulting_forms.Add(neg_a)
// 			new_resulting_forms.Add(forall_neg_a)
// 			tmp_step.SetResultFormulasProof([]vp.IntFormAndTermsList{new_resulting_forms})
// 		}
// 	}
// 	return tmp_step
// }

// Iterate on all proof steps
// func unfoldProofSteps(ps []vp.ProofStruct) []vp.ProofStruct {
// 	new_proof := make([]vp.ProofStruct, 0)
// 	for _, ps := range ps {
// 		new_step := unfoldProofStep(ps)
// 		new_child := make([][]vp.ProofStruct, 0)
// 		for _, c := range ps.GetChildren() {
// 			new_child = append(new_child, unfoldProofSteps(c))
// 		}
// 		new_step.SetChildrenProof(new_child)
//
// 		new_proof = append(new_proof, new_step)
// 	}
//
// 	return new_proof
// }

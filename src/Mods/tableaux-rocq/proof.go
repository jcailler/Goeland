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

// Return a pair of indexes of complementary predicate (positive, negative) among a list of formulas
func findIndexClosureRule(f AST.Form, form_list Lib.List[AST.Form]) (int, int) {
	f_pos := -1
	f_neg := -1

	switch initial_formula := f.(type) {
		case AST.Not:
			targetPos = get(initial_formula.GetForm(), hypotheses)
		default:
			targetPos = target
		}

	if (f_pos == -1) || (f_neg == -1) {
		Glob.Anomaly("findIndexClosureRule", "Complementary literal not found")
	}

	return f_pos, f_neg
}

func manageUnaryRule(s Search.IProof, index int, rule_name string, form_list Lib.List[int], unshelve ...bool) (string, Lib.List[Lib.List[int]]) {
	new_form_list := Lib.NewList[Lib.List[int]]()
	l1 := form_list.Copy(func(i int) int {return i})

	res := fmt.Sprintf("eapply %v (i := %v).\n", rule_name, index)
	if len(unshelve) > 0 {
		res = "unshelve " + res
	}

	for _, child := range s.ResultFormulas().At(0).GetSlice() {
		l1.Append(child.GetIndex())
	}
	new_form_list.Append(l1)
	return res, new_form_list
}

func manageBinaryRule(s Search.IProof, index int, rule_name string, form_list Lib.List[int], unshelve ...bool) (string, Lib.List[Lib.List[int]]) {
	new_form_list := Lib.NewList[Lib.List[int]]()
	l1 := form_list.Copy(func(i int) int {return i})
	l2 := form_list.Copy(func(i int) int {return i})

	res := fmt.Sprintf("eapply %v (i := %v).\n", rule_name, index)

	if len(unshelve) > 0 {
		res = "unshelve " + res
	}

	for _, child := range s.ResultFormulas().At(0).GetSlice() {
		l1.Append(child.GetIndex())
	}

	for _, child := range s.ResultFormulas().At(1).GetSlice() {
		l2.Append(child.GetIndex())
	}
	new_form_list.Append(l1)
	new_form_list.Append(l2)
	return res, new_form_list
}



func makeStepInProof(s Search.IProof, form_list Lib.List[int]) (string, Lib.List[Lib.List[int]]) {
	Glob.PrintInfo("MakeStep", "-----------------------------")
	Glob.PrintInfo("MakeStep", fmt.Sprintf("[%v][%v] : %v", s.(Search.TableauxProof)[0].Rule_name, s.AppliedOn().GetIndex(), s.AppliedOn().ToString()))
	Glob.PrintInfo("MakeStep", "Form list : ")
	for _, v := range form_list.GetSlice() {
        Glob.PrintInfo("MakeStep", fmt.Sprintf("%v ",v))
    }

	index := form_list.IndexOf(s.AppliedOn().GetIndex(), func(i1, i2 int) bool {return i1 == i2})
	real_index := -1

	switch index_t := index.(type) {
		case Lib.Some[int]:
			real_index = form_list.Len() - 1 - index_t.Val
		case Lib.None[int]:
			Glob.Anomaly("TR", "Index not found in MakeStep")
	}
	Glob.PrintInfo("MakeStep", fmt.Sprintf("Real index : %v", real_index))


	Glob.PrintInfo("MakeStep", fmt.Sprintf(fmt.Sprintf("Children: %v", s.Children().Len())))
	for _, branch := range s.Children().GetSlice() {
		for _, child := range branch.Children().GetSlice() {
			Glob.PrintInfo("MakeStep", fmt.Sprintf("[%v] %v",child.AppliedOn().GetIndex(), child.AppliedOn().ToString()))
		}
	}

	Glob.PrintInfo("MakeStep","Result Forms:")
	for _, rfl := range s.ResultFormulas().GetSlice() {
		for _, rf := range rfl.GetSlice() {
			Glob.PrintInfo("MakeStep", fmt.Sprintf("[%v] %v", rf.GetIndex(), rf.ToString()))
		}
	}

	switch s.RuleApplied()  {
	case Search.RuleClosure:
		index_pos, index_neg := findIndexClosureRule(s.AppliedOn(), s.)
		res := fmt.Sprintf("eapply hasTableauContr (i := %v) (j := %v).\n", index_pos, index_neg)
		res += "1: { reflexivity. }\n"
		res += "1: { reflexivity. }\n"
		res += "esimpl.\n"
		res += "reflexivity.\n"
		new_form_list := Lib.NewList[Lib.List[int]]()
		l1 := form_list.Copy(func(i int) int {return i})
		l1.Append(-1)
		new_form_list.Append(l1)

		return res, new_form_list
	case Search.RuleNotNot:
		res, new_form_list := manageUnaryRule(s, real_index, "hasTableauNegNeg", form_list)
		return res, new_form_list
	case Search.RuleNotOr:
		res, new_form_list := manageUnaryRule(s, real_index, "hasTableauNegOr", form_list)
		res += "1: { reflexivity. }\n"
		return res, new_form_list
	case Search.RuleNotImp:
		res, new_form_list := manageUnaryRule(s, real_index, "hasTableauNegImp", form_list)
		res += "1: { reflexivity. }\n"
		tmp_form := AST.MakerNot(AST.MakerNot(s.ResultFormulas().At(0).At(0)))
		tmp_l1 := new_form_list.At(0).Copy(func(i int) int {return i})
		tmp_l1.Append(tmp_form.GetIndex())
		tmp_new_form_list :=  Lib.NewList[Lib.List[int]]()
		tmp_new_form_list.Append(tmp_l1)
		return res, tmp_new_form_list
	case Search.RuleAnd:
		res, new_form_list := manageUnaryRule(s, real_index, "hasTableauAnd", form_list)
		return res, new_form_list
	case Search.RuleNotAnd:
		res, new_form_list := manageBinaryRule(s, real_index, "hasTableauNegAnd", form_list)
		res += "1: { reflexivity. }\n"
		return res, new_form_list
	case Search.RuleNotEqu:
		res, new_form_list := manageBinaryRule(s, real_index, "hasTableauNegEqu", form_list)
		return res, new_form_list
	case Search.RuleOr:
		res, new_form_list := manageBinaryRule(s, real_index, "hasTableauOr", form_list)
		return res, new_form_list
	case Search.RuleImp:
		res, new_form_list := manageBinaryRule(s, real_index, "hasTableauImp", form_list)
		return res, new_form_list
	case Search.RuleEqu:
		res, new_form_list := manageBinaryRule(s, real_index, "hasTableauEqu", form_list)
		return res, new_form_list
	case Search.RuleNotEx:
		res, new_form_list := manageUnaryRule(s, real_index, "hasTableauNegEx", form_list)
		res += "1: { reflexivity. }\n"
		res += "1: { set_decide. }\n"
		return res, new_form_list
	case Search.RuleAll:
		res, new_form_list := manageUnaryRule(s, real_index, "hasTableauAl", form_list)
		return res, new_form_list
	case Search.RuleNotAll:
		res, new_form_list := manageUnaryRule(s, real_index, "hasTableauNegAll", form_list, true)
		
		var real_generated_term AST.Term
		generated_term := s.TermGenerated()
		switch generated_term_t := generated_term.(type) {
			case Lib.Some[Lib.Either[AST.Ty, AST.Term]]:
				switch generated_term_t2 := generated_term_t.Val.(type) {
					case Lib.Left[AST.Ty, AST.Term]:
						Glob.Fatal("TMakeStepR", "Not implemented yet")
					case Lib.Right[AST.Ty, AST.Term]:
						real_generated_term = generated_term_t2.Val
					}
			case Lib.None[AST.Term]:
				Glob.Anomaly("MakeStep", "Generated term not found")
		}

		Glob.PrintInfo("MakeStep", fmt.Sprintf("Generated term : %v", real_generated_term.ToString()))

		res += "1, 2: shelve.\n"
		res += fmt.Sprintf("1: exact (%v).\n", TermToTR(real_generated_term))
		res += "2, 3: reflexivity.\n"
		res += "1: { set_decide. }\n"
		return res, new_form_list
	case Search.RuleEx:
		res, new_form_list := manageUnaryRule(s, real_index, "hasTableauEx", form_list)
		return res, new_form_list
	case Search.RuleReintro: 
		new_form_list := Lib.NewList[Lib.List[int]]()
		l1 := form_list.Copy(func(i int) int {return i})
		l1.Append(-1)
		new_form_list.Append(l1)
		return "", new_form_list
	default:
		return "Error Admit.", Lib.NewList[Lib.List[int]]()
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

	form_list := Lib.MkListV(prf.AppliedOn().GetIndex())

	return res + makeProofAux(prf, form_list)
}

func makeProofAux(prf Search.IProof, form_list Lib.List[int]) string {
	res, generated_formulas := makeStepInProof(prf, form_list) 
	for i, s := range prf.Children().GetSlice() {
		res_child := makeProofAux(s, generated_formulas.At(i))
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

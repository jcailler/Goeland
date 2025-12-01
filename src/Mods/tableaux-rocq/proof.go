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

	if f_not, ok := prf.AppliedOn().(AST.Not); ok {
		res := FormToTR(f_not.GetForm())
		return fmt.Sprintf("	%v \n", res)
	} else {
		Glob.Anomaly("TableauxRocq — makeFormula", "The proof does not start by a refutation")
		return "Error"
	}
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
func findIndexClosureRule(index_f int, f AST.Form, form_list Lib.List[AST.Form]) (int, int) {
	f_pos := -1
	f_neg := -1

	var other_form AST.Form


	switch f_t := f.(type) {
		case AST.Pred:
			f_pos = index_f
			other_form = AST.MakerNot(f_t)
			for index_other_f, f_candidate := range form_list.GetSlice() {
			if f_candidate.Equals(other_form) {
				f_neg = form_list.Len() - 1 - index_other_f
			}
		}
		case AST.Not:
			f_neg = index_f
			other_form = f_t.GetForm()
			for index_other_f, f_candidate := range form_list.GetSlice() {
			if f_candidate.Equals(other_form) {
				f_pos = form_list.Len() - 1 - index_other_f
			}
		}
	}

	if (f_pos == -1) || (f_neg == -1) {
		Glob.Anomaly("findIndexClosureRule", "Complementary literal not found")
	}

	return f_pos, f_neg
}

// TODO : to delete
func manageUnaryRule(s Search.IProof, index int, rule_name string, form_list Lib.List[AST.Form], full_line ...string) (string, Lib.List[Lib.List[AST.Form]]) {
	new_form_list := Lib.NewList[Lib.List[AST.Form]]()
	l1 := form_list.Copy(func(i AST.Form) AST.Form {return i})

	res := ""
	if len(full_line) > 0 {
		res = full_line[0]
	} else {
		res = fmt.Sprintf("eapply %v with (i := %v).\n", rule_name, index)
	}

	for _, child := range s.ResultFormulas().At(0).GetSlice() {
		l1.Append(child)
	}
	new_form_list.Append(l1)
	return res, new_form_list
}

// TODO : to delete
func manageBinaryRule(s Search.IProof, index int, rule_name string, form_list Lib.List[AST.Form], full_line ...string) (string, Lib.List[Lib.List[AST.Form]]) {
	new_form_list := Lib.NewList[Lib.List[AST.Form]]()
	l1 := form_list.Copy(func(i AST.Form) AST.Form {return i})
	l2 := form_list.Copy(func(i AST.Form) AST.Form {return i})

	res := ""
	if len(full_line) > 0 {
		res = full_line[0]
	} else {
		res = fmt.Sprintf("eapply %v with (i := %v).\n", rule_name, index)
	}

	for _, child := range s.ResultFormulas().At(0).GetSlice() {
		l1.Append(child)
	}

	for _, child := range s.ResultFormulas().At(1).GetSlice() {
		l2.Append(child)
	}
	new_form_list.Append(l1)
	new_form_list.Append(l2)
	return res, new_form_list
}

func getRealGeneratedTerm(s Search.IProof) AST.Term {
	var real_generated_term AST.Term
	switch generated_term_t := s.TermGenerated().(type) {
		case Lib.Some[Lib.Either[AST.Ty, AST.Term]]:
			switch generated_term_t2 := generated_term_t.Val.(type) {
				case Lib.Left[AST.Ty, AST.Term]:
					Glob.Fatal("MakeStep", "Not implemented yet")
				case Lib.Right[AST.Ty, AST.Term]:
					real_generated_term = generated_term_t2.Val
				}
		case Lib.None[AST.Term]:
			Glob.Anomaly("MakeStep", "Generated term not found")
	}
	return real_generated_term
}

func getRealIndex(s Search.IProof, form_list Lib.List[AST.Form]) int {
	index := form_list.IndexOf(s.AppliedOn(), func(i1, i2 AST.Form) bool {return i1.Equals(i2)})
	real_index := -1

	// Find the index of the current formula
	switch index_t := index.(type) {
		case Lib.Some[int]:
			real_index = form_list.Len() - 1 - index_t.Val
		case Lib.None[int]:
			Glob.Anomaly("TR", "Index not found in MakeStep")
	}
	return real_index
}

func printSkosAndMetas(metas, skos Lib.Set[AST.Term]) {

	Glob.PrintInfo("MakeStep", "Metas: ")
	for _, v := range metas.Elements().GetSlice() {
        Glob.PrintInfo("MakeStep", fmt.Sprintf("%v ", v.ToString()))
    }
	Glob.PrintInfo("MakeStep", "")

	Glob.PrintInfo("MakeStep", "Skos: ")
	for _, v := range skos.Elements().GetSlice() {
        Glob.PrintInfo("MakeStep", fmt.Sprintf("%v ", v.ToString()))
    }
	Glob.PrintInfo("MakeStep", "")
}

func makeProofAux(s Search.IProof, form_list Lib.List[AST.Form]) (string, Lib.List[Lib.List[AST.Form]], Lib.Set[AST.Term], Lib.Set[AST.Term]) {
	
	// List of formula (for each branch)
	new_form_list := Lib.NewList[Lib.List[AST.Form]]()
	l1 := form_list.Copy(func(i AST.Form) AST.Form {return i})
	// l2 := form_list.Copy(func(i AST.Form) AST.Form {return i})

	// Set of metas generated below this node
	metas := Lib.EmptySet[AST.Term]()

	// Set of Skolem terms generated below this node
	skos := Lib.EmptySet[AST.Term]()

	// Index of the current formula
	index := getRealIndex(s, form_list)
	
	// Debug
	Glob.PrintInfo("MakeStep", "-----------------------------")
	Glob.PrintInfo("MakeStep", fmt.Sprintf("[%v][%v] : %v", s.(Search.TableauxProof)[0].Rule_name, s.AppliedOn().GetIndex(), s.AppliedOn().ToString()))
	Glob.PrintInfo("MakeStep", " ")
	Glob.PrintInfo("MakeStep", "Form list: ")
	for _, v := range form_list.GetSlice() {
        Glob.PrintInfo("MakeStep", fmt.Sprintf("[%v] %v ",v.GetIndex(), v.ToString()))
    }
	Glob.PrintInfo("MakeStep", "")

	Glob.PrintInfo("MakeStep", fmt.Sprintf("Real index: %v", index))
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

	// Todo : copie sets when branching
	switch s.RuleApplied()  {
	case Search.RuleClosure: // F, neg F
		index_pos, index_neg := findIndexClosureRule(index, s.AppliedOn(), form_list)
		res := fmt.Sprintf("eapply hasTableauContr with (i := %v) (j := %v).\n", index_pos, index_neg)
		res += "1: { reflexivity. }\n"
		res += "1: { reflexivity. }\n"
		res += "esimpl.\n"
		res += "reflexivity.\n"
		
		new_form_list := Lib.NewList[Lib.List[AST.Form]]()
		l1 := form_list.Copy(func(i AST.Form) AST.Form {return i})
		l1.Append(s.AppliedOn())
		new_form_list.Append(l1)

		return res, new_form_list, metas, skos
	case Search.RuleNotNot:
		res, new_form_list := manageUnaryRule(s, index, "hasTableauNegNeg", form_list)
		return res, new_form_list, metas, skos
	case Search.RuleNotOr:
		res, new_form_list := manageUnaryRule(s, index, "hasTableauNegOr", form_list)
		res += "1: { reflexivity. }\n"
		return res, new_form_list, metas, skos
	case Search.RuleNotImp: // Neg (F -> G) -> Neg Neg F, Neg G, F	
		tmp_form := AST.MakerNot(AST.MakerNot(s.ResultFormulas().At(0).At(0)))
		l1.Append(tmp_form)
		l1.Append(s.ResultFormulas().At(0).At(1))
		l1.Append(s.ResultFormulas().At(0).At(0))
		
		next_res, next_form, next_metas, next_skos := makeProofAux(s.Children().At(0), l1)
		
		res := fmt.Sprintf("eapply %v with (i := %v).\n", "hasTableauNegImp", index)
		res += "1: { reflexivity. }\n"
		res += next_res
		
		return res, next_form, next_metas, next_skos
	case Search.RuleAnd:
		res, new_form_list := manageUnaryRule(s, index, "hasTableauAnd", form_list)
		return res, new_form_list, metas, skos
	case Search.RuleNotAnd: // TODO
		res, new_form_list := manageBinaryRule(s, index, "hasTableauNegAnd", form_list)
		res += "1: { reflexivity. }\n"
		return res, new_form_list, metas, skos
	case Search.RuleNotEqu:
		res, new_form_list := manageBinaryRule(s, index, "hasTableauNegEqu", form_list)
		return res, new_form_list, metas, skos
	case Search.RuleOr:
		res, new_form_list := manageBinaryRule(s, index, "hasTableauOr", form_list)
		return res, new_form_list, metas, skos
	case Search.RuleImp:
		res, new_form_list := manageBinaryRule(s, index, "hasTableauImp", form_list)
		return res, new_form_list, metas, skos
	case Search.RuleEqu:
		res, new_form_list := manageBinaryRule(s, index, "hasTableauEqu", form_list)
		return res, new_form_list, metas, skos
	case Search.RuleNotEx: // Neg (Ex x F[x]) -> All x (neg F[x]), neg F[x -> t]
		tmp_form := AST.MakerAll(Lib.MkListV(s.AppliedOn().(AST.Not).GetForm().(AST.Ex).GetVarList().At(0)), AST.MakerNot(s.AppliedOn().(AST.Not).GetForm().(AST.Ex).GetForm()))
		l1.Append(tmp_form)
		l1.Append(s.ResultFormulas().At(0).At(0))
		
		next_res, next_form, next_metas, next_skos := makeProofAux(s.Children().At(0), l1)
		real_generated_term := getRealGeneratedTerm(s)
		new_metas := next_metas.Copy()
		
		if meta_generated, ok := real_generated_term.(AST.Meta); ok {
			new_metas = new_metas.Add(meta_generated)
		}

		res := fmt.Sprintf("eapply %v with (i := %v).\n", "hasTableauNegEx", index)
		res += "1: { reflexivity. }\n"
		res += "1: { set_decide. }\n"
		res += next_res
	
		return res, next_form, new_metas, next_skos
	case Search.RuleAll: // All x F[x] -> F[x -> t]
		l1.Append(s.ResultFormulas().At(0).At(0))
		
		next_res, next_form, next_metas, next_skos := makeProofAux(s.Children().At(0), l1)
		real_generated_term := getRealGeneratedTerm(s)
		new_metas := next_metas.Copy()
		
		if meta_generated, ok := real_generated_term.(AST.Meta); ok {
			new_metas = new_metas.Add(meta_generated)
		}

		res := fmt.Sprintf("eapply %v with (i := %v).\n", "hasTableauAll", index)
		res += "1: { reflexivity. }\n"
		res += "1: { set_decide. }\n"
		res += next_res
	
		return res, next_form, new_metas, next_skos
	case Search.RuleNotAll: // Neg (All x F[x]) -> neg (F[x-> t])
		l1.Append(s.ResultFormulas().At(0).At(0))

		next_res, next_form, next_metas, next_skos := makeProofAux(s.Children().At(0), l1)

		sko := "OuterSkolemization"
		if Glob.IsInnerSko() {
			sko = "InnerSkolemization"
		}

		real_generated_term := getRealGeneratedTerm(s)
		new_skos := next_skos.Copy()
		
		if skos_generated, ok := real_generated_term.(AST.Fun); ok {
			new_skos = new_skos.Add(skos_generated.GetID())
		}

		res := fmt.Sprintf("unshelve eapply hasTableauNegAll with (sko := %v) (i := %v).\n", sko, index)
		res += "1, 2: shelve.\n"
		res += fmt.Sprintf("1: exact (%v).\n", TermToTR(real_generated_term))
		res += "2, 3: reflexivity.\n"
		res += "1: { set_decide. }\n"
		res += next_res

		return res, next_form, next_metas, new_skos
	case Search.RuleEx: // Ex x F[x] -> neg (neg (Ex x F[x -> t])), F[x -> t]
		tmp_form := AST.MakerNot(AST.MakerNot(s.AppliedOn().(AST.Ex).GetForm()))
		l1.Append(tmp_form)
		l1.Append(s.ResultFormulas().At(0).At(0))

		next_res, next_form, next_metas, next_skos := makeProofAux(s.Children().At(0), l1)

		sko := "OuterSkolemization"
		if Glob.IsInnerSko() {
			sko = "InnerSkolemization"
		}

		real_generated_term := getRealGeneratedTerm(s)
		new_skos := next_skos.Copy()
		
		if skos_generated, ok := real_generated_term.(AST.Fun); ok {
			new_skos = new_skos.Add(skos_generated.GetID())
		}

		res := fmt.Sprintf("unshelve eapply hasTableauEx with (sko := %v) (i := %v).\n", sko, index)
		res += "1, 2: shelve.\n"
		res += fmt.Sprintf("1: exact (%v).\n", TermToTR(real_generated_term))
		res += "2, 3: reflexivity.\n"
		res += "1: { set_decide. }\n"
		res += next_res

		return res, next_form, next_metas, new_skos
	case Search.RuleReintro: // Skip
		return makeProofAux(s.Children().At(0), form_list)
	default:
		return "Error Admit.", new_form_list, metas, skos
	}
}

func makeProof(prf Search.IProof, sub Unif.Substitutions) string {
	res := ""
	var_list, sko_list := extractTermsFromSubstList(sub)

	var_str := ""
	for i, v := range var_list.GetSlice() {
		var_str += fmt.Sprintf(" \"%v\" ", v.ToString())
		if (i < var_list.Len()-1) {
			var_str += ","
		}
	}

	sko_str := ""
	for i, s := range sko_list.GetSlice() {
		sko_str += fmt.Sprintf(" \"%v\" ", s.GetName())
		if (i < sko_list.Len()-1) {
			sko_str += ","
		}
	}

	res += fmt.Sprintf("exists \\{%v\\}, \\{%v\\}.\n", var_str, sko_str)

	form_list := Lib.MkListV(prf.AppliedOn())
	res2, _, _, _ := makeProofAux(prf, form_list)

	return res + res2
}
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
* This file provides poulet's output
**/

package poulet

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

var dummy_FV = AST.MakerMeta("Goeland_I", -1, AST.TIndividual())

/************ Axiom and Conjecture ************/
// Processes the formula that was proven by Goéland.
func processMainFormula(form AST.Form) (Lib.List[AST.Form], AST.Form) {
	formList := Lib.NewList[AST.Form]()
	switch nf := form.(type) {
	case AST.Not:
		form = nf.GetForm()
	case AST.And:
		last := nf.GetChildFormulas().Len() - 1
		formList = Lib.MkListV(nf.GetChildFormulas().Get(0, last)...)
		form = nf.GetChildFormulas().At(last).(AST.Not).GetForm()
	}
	return formList, form
}

func makeAxioms(axioms Lib.List[AST.Form]) string {
	res := ""
	for i, ax := range axioms.GetSlice() {
		res += makeContextAxiomBegin(i)
		res += fmt.Sprintf("	%v \n", FormToTR(ax))
		res += makeContextAxiomEnd()
	}
	return res
}

func makeConjecture(f AST.Form) string {
	return fmt.Sprintf("	%v \n", FormToTR(f))
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

func contextUnaryNode(s string) string {
	return fmt.Sprintf("apply (mkUnaryNode ( %v ) ).\n", s)
}

func contextBinaryNode(s string) string {
	return fmt.Sprintf("apply (mkBinaryNode ( %v ) ).\n", s)
}

// Return a pair of indexes of complementary predicate (positive, negative) among a list of formulas
func findIndexClosureRule(index_f int, sub Unif.Substitutions, f AST.Form, form_list Lib.List[AST.Form]) (int, int) {
	f_pos := -1
	f_neg := -1

	var other_form AST.Form
	new_f := Core.ApplySubstitutionsOnFormula(Unif.FromSubstitutions(sub), f)
	new_form_list := Lib.NewList[AST.Form]()
	
	for _, form := range form_list.GetSlice() {
		new_form_list.Append(Core.ApplySubstitutionsOnFormula(Unif.FromSubstitutions(sub), form))
	}

	switch f_t := new_f.(type) {
		case AST.Pred:
			f_pos = index_f
			other_form = AST.MakerNot(f_t)
			for index_other_f, f_candidate := range new_form_list.GetSlice() {
			if f_candidate.Equals(other_form) {
				f_neg = new_form_list.Len() - 1 - index_other_f
			}
		}
		case AST.Not:
			f_neg = index_f
			other_form = f_t.GetForm()
			for index_other_f, f_candidate := range new_form_list.GetSlice() {
			if f_candidate.Equals(other_form) {
				f_pos = new_form_list.Len() - 1 - index_other_f
			}
		}
	}


	if (f_pos == -1) || (f_neg == -1) {
		Glob.Anomaly("findIndexClosureRule", "Complementary literal not found")
	}

	return f_pos, f_neg
}


func findComplementaryLiteral(f AST.Form, form_list Lib.List[AST.Form], sub Unif.Substitutions) (AST.Form, AST.Form) {
	var other_form AST.Form
	// Glob.PrintInfo("findComplementaryLiteral", fmt.Sprintf("f: %v", f.ToString()))
	new_f := Core.ApplySubstitutionsOnFormula(Unif.FromSubstitutions(sub), f)
	// Glob.PrintInfo("findComplementaryLiteral", fmt.Sprintf("S(f): %v", new_f.ToString()))
	new_form_list := Lib.NewList[AST.Form]()
	
	for _, form := range form_list.GetSlice() {
		new_form_list.Append(Core.ApplySubstitutionsOnFormula(Unif.FromSubstitutions(sub), form))
	}

	// for _, form := range new_form_list.GetSlice() {
	// 	Glob.PrintInfo("findComplementaryLiteral", fmt.Sprintf("\t%v", form.ToString()))
	// }

	switch f_t := new_f.(type) {
		case AST.Pred:
			other_form = AST.MakerNot(f_t)
			for index_other_f, f_candidate := range new_form_list.GetSlice() {
				if f_candidate.Equals(other_form) {
					other_form = form_list.At(index_other_f)
					return f, other_form
				}
		}
		case AST.Not:
			other_form = f_t.GetForm()
			for index_other_f, f_candidate := range new_form_list.GetSlice() {
				if f_candidate.Equals(other_form) {
					other_form = form_list.At(index_other_f)
					return f, other_form
				}
		}
	}

	Glob.Anomaly("findIndexClosureRule", "Complementary literal not found")
	return f, other_form
}

func isLit(f AST.Form) bool {
	switch f_t := f.(type) {
		case AST.Pred:
			return true
		case AST.Not:
			return isLit(f_t.GetForm())
		}
	return false
}

func AppendIfLit(l Lib.List[AST.Form], f AST.Form) Lib.List[AST.Form] {
	if isLit(f){
		l.Append(f)
	}
	return l
}

func getRealGeneratedTerm(s Search.IProof) AST.Term {
	var real_generated_term AST.Term
	switch generated_term_t := s.TermGenerated().(type) {
		case Lib.Some[Lib.Either[AST.Ty, AST.Term]]:
			switch generated_term_t2 := generated_term_t.Val.(type) {
				case Lib.Left[AST.Ty, AST.Term]:
					Glob.Fatal("getRealGeneratedTerm", "Not implemented yet")
				case Lib.Right[AST.Ty, AST.Term]:
					real_generated_term = generated_term_t2.Val
				}
		case Lib.None[AST.Term]:
			// Glob.Anomaly("getRealGeneratedTerm", "Generated term not found")
			return dummy_FV
	}
	return real_generated_term
}

func getRealIndex(s Search.IProof, form_list Lib.List[AST.Form], sub Unif.Substitutions) int {
	
	fl_after_subst := Lib.NewList[AST.Form]()
	for _, f := range form_list.GetSlice() {
		fl_after_subst.Append(Core.ApplySubstitutionsOnFormula(Unif.FromSubstitutions(sub), f))
	}
	index := fl_after_subst.IndexOf(Core.ApplySubstitutionsOnFormula(Unif.FromSubstitutions(sub), s.AppliedOn()), func(i1, i2 AST.Form) bool {return i1.Equals(i2)})
	real_index := -1

	// Find the index of the current formula
	switch index_t := index.(type) {
		case Lib.Some[int]:
			real_index = form_list.Len() - 1 - index_t.Val
		case Lib.None[int]:
			Glob.Anomaly("getRealIndex", "Index not found in MakeStep")
	}
	return real_index
}

func manageMetasFromChild(metas Lib.Set[AST.Term]) string {
	res := "@empty_set string _"
	if metas.Cardinal() > 0 {
		res = "\\{"
		for i, meta := range metas.Elements().GetSlice() {
			res += "\"" + meta.ToString() + "\""
			if i < (metas.Cardinal()-1) {
				res += ", "
			}
		}
		res += "\\}"
	}
	return res
}

func manageSkolemsFromChild(skolems Lib.Set[AST.Term]) string {
	res := "empty_record"
	if skolems.Cardinal() > 0 {
		res = "\\{"
		for i, sko := range skolems.Elements().GetSlice() {
			res += fmt.Sprintf(" \"%v\" ", sko.GetName())
			if i < (skolems.Cardinal()-1) {
				res += ", "
			}
		}
		res += "\\}"
	}
	return res
}

func printSkosAndMetas(metas, skos Lib.Set[AST.Term]) {

	Glob.PrintWarn("MakeStep", "Metas: ")
	for _, v := range metas.Elements().GetSlice() {
        Glob.PrintWarn("MakeStep", fmt.Sprintf("%v ", v.ToString()))
    }
	Glob.PrintWarn("MakeStep", "")

	Glob.PrintWarn("MakeStep", "Skos: ")
	for _, v := range skos.Elements().GetSlice() {
        Glob.PrintWarn("MakeStep", fmt.Sprintf("%v ", v.ToString()))
    }
	Glob.PrintWarn("MakeStep", "")
}

func makeProofAux(s Search.IProof, sub Unif.Substitutions, form_list Lib.List[AST.Form]) string {

	// List of formula (for each branch)
	l1 := form_list.Copy(func(i AST.Form) AST.Form {return i})
	l2 := form_list.Copy(func(i AST.Form) AST.Form {return i})

	// Debug
	// Glob.PrintInfo("MakeStep", "-----------------------------")
	// Glob.PrintInfo("MakeStep", fmt.Sprintf("[%v][%v] : %v", s.(Search.TableauxProof)[0].Rule_name, s.AppliedOn().GetIndex(), s.AppliedOn().ToString()))
	// Glob.PrintInfo("MakeStep", " ")
	// Glob.PrintInfo("MakeStep", "Form list: ")
	// for _, v := range form_list.GetSlice() {
    //     Glob.PrintInfo("MakeStep", fmt.Sprintf("[%v] %v ",v.GetIndex(), v.ToString()))
    // }
	// Glob.PrintInfo("MakeStep", "")
	// Glob.PrintInfo("MakeStep"," ")
	// Glob.PrintInfo("MakeStep", fmt.Sprintf(fmt.Sprintf("Children: %v", s.Children().Len())))
	// if s.Children().Len() > 0 {
	// 	for i, branch := range s.Children().GetSlice() {
	// 		Glob.PrintInfo("MakeStep", fmt.Sprintf("Child %v: %v", i, branch.AppliedOn().ToString()))
	// 	}
	// 	Glob.PrintInfo("MakeStep"," ")
	// 	Glob.PrintInfo("MakeStep","Result Forms:")
	// 	for i, rfl := range s.ResultFormulas().GetSlice() {
	// 		Glob.PrintInfo("MakeStep", fmt.Sprintf("Rf %v:", i))
	// 		for _, rf := range rfl.GetSlice() {
	// 			Glob.PrintInfo("MakeStep", fmt.Sprintf("[%v] %v", rf.GetIndex(), rf.ToString()))
	// 		}
	// 	}
	// }

	switch s.RuleApplied()  {
	case Search.RuleClosure: 
		if _, ok :=  s.AppliedOn().(AST.Bot); ok {
			return "exact mkTrivialClosure.\n"
		} 

		if s2, ok :=  s.AppliedOn().(AST.Not); ok {
			if _, ok2 :=  s2.GetForm().(AST.Top); ok2 {
				return "exact mkTrivialClosure.\n"
			} 
		} 
	
		f, comp_f := findComplementaryLiteral(s.AppliedOn(), form_list, sub)
		return fmt.Sprintf("exact (mkClosure [[ %v ]] [[ %v ]]).\n", FormToTR(f), FormToTR(comp_f))
	case Search.RuleNotNot:  
		rule_name := "AlphaNegNeg"
		current_form_TR := FormToTR(s.AppliedOn().(AST.Not).GetForm().(AST.Not).GetForm())

		f := s.ResultFormulas().At(0).At(0)
		l1 = AppendIfLit(l1, f)
		next_res := makeProofAux(s.Children().At(0), sub, l1)

		res := contextUnaryNode(fmt.Sprintf("%v (Neg (Neg [[ %v ]]))", rule_name, current_form_TR))
		res += next_res 
	
		return res
	case Search.RuleNotOr: 
		rule_name := "AlphaNegOr"
		current_form_TR := FormToTR(s.AppliedOn().(AST.Not).GetForm())

		idx_b1 := 0
		idx_neg_f := 0
		idx_neg_g := 1
		neg_f := s.ResultFormulas().At(idx_b1).At(idx_neg_f)
		neg_g := s.ResultFormulas().At(idx_b1).At(idx_neg_g)
		l1 = AppendIfLit(l1, neg_f)
		l1 = AppendIfLit(l1, neg_g)
		next_res := makeProofAux(s.Children().At(0), sub, l1)

		res := contextUnaryNode(fmt.Sprintf("%v (Neg [[ %v ]])", rule_name, current_form_TR))
		res += next_res 
	
		return res
	case Search.RuleNotImp:
		rule_name := "AlphaNegImp"
		current_form_TR := FormToTR(s.AppliedOn().(AST.Not).GetForm())

		idx_b1 := 0
		idx_f := 0
		idx_neg_g := 1
		f := s.ResultFormulas().At(idx_b1).At(idx_f)
		neg_g := s.ResultFormulas().At(idx_b1).At(idx_neg_g)
		l1 = AppendIfLit(l1, f)
		l1 = AppendIfLit(l1, neg_g)
		
		next_res := makeProofAux(s.Children().At(0), sub, l1)

		res := contextUnaryNode(fmt.Sprintf("%v (Neg [[ %v ]])", rule_name, current_form_TR))
		res += next_res 
	
		return res
	case Search.RuleAnd: 
		rule_name := "AlphaAnd"
		current_form_TR := FormToTR(s.AppliedOn())

		idx_b1 := 0
		idx_f := 0
		idx_g := 1
		f := s.ResultFormulas().At(idx_b1).At(idx_f)
		g := s.ResultFormulas().At(idx_b1).At(idx_g)
		l1 = AppendIfLit(l1, f)
		l1 = AppendIfLit(l1, g)
		next_res := makeProofAux(s.Children().At(0), sub, l1)

		res := contextUnaryNode(fmt.Sprintf("%v [[ %v ]]", rule_name, current_form_TR))
		res += next_res 
	
		return res
	case Search.RuleNotAnd:
		rule_name := "BetaNegAnd"
		current_form_TR := FormToTR(s.AppliedOn().(AST.Not).GetForm())

		idx_b1 := 0
		idx_b2 := 1
		idx_neg_f := 0
		idx_neg_g := 0
		neg_f := s.ResultFormulas().At(idx_b1).At(idx_neg_f)
		neg_g := s.ResultFormulas().At(idx_b2).At(idx_neg_g)
		l1 = AppendIfLit(l1, neg_f)
		l2 = AppendIfLit(l2, neg_g)
		next_res1 := makeProofAux(s.Children().At(idx_b1), sub, l1)
		next_res2 := makeProofAux(s.Children().At(idx_b2), sub, l2)



		res := contextBinaryNode(fmt.Sprintf("%v (Neg [[ %v ]])", rule_name, current_form_TR))
		res += fmt.Sprintf("{\n%v}\n", next_res1)
		res += fmt.Sprintf("{\n%v}\n", next_res2)

		return res
	case Search.RuleNotEqu: 
		rule_name := "BetaNegEqu"
		current_form_TR := FormToTR(s.AppliedOn().(AST.Not).GetForm())
		
		idx_b1 := 0
		idx_b2 := 1
		idx_f := 0
		idx_g := 1
		idx_neg_f := 0
		idx_neg_g := 1

		neg_f := s.ResultFormulas().At(idx_b1).At(idx_neg_f)
		g := s.ResultFormulas().At(idx_b1).At(idx_g)
		f := s.ResultFormulas().At(idx_b2).At(idx_f)
		neg_g := s.ResultFormulas().At(idx_b2).At(idx_neg_g)
		l1 = AppendIfLit(l1, neg_f)
		l1 = AppendIfLit(l1, g)
		l2 = AppendIfLit(l2, f)
		l2 = AppendIfLit(l2, neg_g)


		next_res1 := makeProofAux(s.Children().At(idx_b1), sub, l1)
		next_res2 := makeProofAux(s.Children().At(idx_b2), sub, l2)

		res := contextBinaryNode(fmt.Sprintf("%v (Neg [[ %v ]])", rule_name, current_form_TR))
		res += fmt.Sprintf("{\n%v}\n", next_res2)
		res += fmt.Sprintf("{\n%v}\n", next_res1)

		return res
	case Search.RuleOr: 
		rule_name := "BetaOr"
		current_form_TR := FormToTR(s.AppliedOn())
		
		idx_b1 := 0
		idx_b2 := 1
		idx_f := 0
		idx_g := 0
		f := s.ResultFormulas().At(idx_b1).At(idx_f)
		g := s.ResultFormulas().At(idx_b2).At(idx_g)
		l1 = AppendIfLit(l1, f)
		l2 = AppendIfLit(l2, g)
		next_res1 := makeProofAux(s.Children().At(idx_b1), sub, l1)
		next_res2 := makeProofAux(s.Children().At(idx_b2), sub, l2)

		res := contextBinaryNode(fmt.Sprintf("%v [[ %v ]]", rule_name, current_form_TR))
		res += fmt.Sprintf("{\n%v}\n", next_res1)
		res += fmt.Sprintf("{\n%v}\n", next_res2)

		return res
	case Search.RuleImp:
		rule_name := "BetaImp"
		current_form_TR := FormToTR(s.AppliedOn())
		
		idx_b1 := 0
		idx_b2 := 1
		idx_neg_f := 0
		idx_g := 0
		neg_f := s.ResultFormulas().At(idx_b1).At(idx_neg_f)
		g := s.ResultFormulas().At(idx_b2).At(idx_g)
		l1 = AppendIfLit(l1, neg_f)
		l2 = AppendIfLit(l2, g)
		next_res1 := makeProofAux(s.Children().At(idx_b1), sub, l1)
		next_res2 := makeProofAux(s.Children().At(idx_b2), sub, l2)

		res := contextBinaryNode(fmt.Sprintf("%v [[ %v ]]", rule_name, current_form_TR))
		res += fmt.Sprintf("{\n%v}\n", next_res1)
		res += fmt.Sprintf("{\n%v}\n", next_res2)

		return res
	case Search.RuleEqu: 
		rule_name := "BetaEqu"
		current_form_TR := FormToTR(s.AppliedOn())
		
		idx_b1 := 0
		idx_b2 := 1
		idx_f := 0
		idx_g := 1
		idx_neg_f := 0
		idx_neg_g := 1

		neg_f := s.ResultFormulas().At(idx_b1).At(idx_neg_f)
		neg_g := s.ResultFormulas().At(idx_b1).At(idx_neg_g)
		f := s.ResultFormulas().At(idx_b2).At(idx_f)
		g := s.ResultFormulas().At(idx_b2).At(idx_g)
		l1 = AppendIfLit(l1, neg_f)
		l1 = AppendIfLit(l1, neg_g)
		l2 = AppendIfLit(l2, f)
		l2 = AppendIfLit(l2, g)

		next_res1 := makeProofAux(s.Children().At(idx_b1), sub, l1)
		next_res2 := makeProofAux(s.Children().At(idx_b2), sub, l2)

		res := contextBinaryNode(fmt.Sprintf("%v [[ %v ]]", rule_name, current_form_TR))
		res += fmt.Sprintf("{\n%v}\n", next_res1)
		res += fmt.Sprintf("{\n%v}\n", next_res2)

		return res
	case Search.RuleNotEx: 
		rule_name := "GammaNegEx"
		current_form_TR := FormToTR(s.AppliedOn().(AST.Not).GetForm())
		generated_term := getRealGeneratedTerm(s)
		
		f := s.ResultFormulas().At(0).At(0)
		l1 = AppendIfLit(l1, f)
		next_res := makeProofAux(s.Children().At(0), sub, l1)

		res := contextUnaryNode(fmt.Sprintf("%v (Neg [[ %v ]]) \"%v\"", rule_name, current_form_TR, generated_term.ToString()))
		res += next_res 
	
		return res
	case Search.RuleAll: 
		rule_name := "GammaAll"
		current_form_TR := FormToTR(s.AppliedOn())
		generated_term := getRealGeneratedTerm(s)
		
		f := s.ResultFormulas().At(0).At(0)
		l1 = AppendIfLit(l1, f)
		next_res := makeProofAux(s.Children().At(0), sub, l1)

		res := contextUnaryNode(fmt.Sprintf("%v [[ %v ]] \"%v\"", rule_name, current_form_TR, generated_term.ToString()))
		res += next_res 
	
		return res
	case Search.RuleNotAll: 
		rule_name := "DeltaNegAll"
		current_form_TR := FormToTR(s.AppliedOn().(AST.Not).GetForm())
		generated_term := TermToTR(getRealGeneratedTerm(s))
		
		f := s.ResultFormulas().At(0).At(0)
		l1 = AppendIfLit(l1, f)
		next_res := makeProofAux(s.Children().At(0), sub, l1)

		res := contextUnaryNode(fmt.Sprintf("%v (Neg [[ %v ]]) [[ %v ]]", rule_name, current_form_TR, generated_term))
		res += next_res 
	
		return res
	case Search.RuleEx: 
		rule_name := "DeltaEx"
		current_form_TR := FormToTR(s.AppliedOn())
		generated_term := TermToTR(getRealGeneratedTerm(s))
		
		f := s.ResultFormulas().At(0).At(0)
		l1 = AppendIfLit(l1, f)
		next_res := makeProofAux(s.Children().At(0), sub, l1)

		res := contextUnaryNode(fmt.Sprintf("%v [[ %v ]] [[ %v ]]", rule_name, current_form_TR, generated_term))
		res += next_res 
	
		return res
	case Search.RuleReintro: 
		return makeProofAux(s.Children().At(0), sub, form_list)
	default:
		return "Error Admit."
	}	
}

func makeProof(prf Search.IProof, sub Unif.Substitutions, form_list Lib.List[AST.Form]) string {
	new_form_list := Lib.NewList[AST.Form]()
	for _, f := range form_list.GetSlice() {
		new_form_list = AppendIfLit(new_form_list, f)
	}
	return makeProofAux(prf, sub, new_form_list)
}


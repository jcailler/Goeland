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
			res += sko.ToString()
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

func makeProofAux(s Search.IProof, form_list Lib.List[AST.Form], sub Unif.Substitutions) (string, Lib.Set[AST.Term], Lib.Set[AST.Term]) {
	
	// List of formula (for each branch)
	l1 := form_list.Copy(func(i AST.Form) AST.Form {return i})
	l2 := form_list.Copy(func(i AST.Form) AST.Form {return i})

	// Set of metas generated below this node
	metas := Lib.EmptySet[AST.Term]()

	// Set of Skolem terms generated below this node
	skos := Lib.EmptySet[AST.Term]()

	// Index of the current formula
	index := getRealIndex(s, form_list)
	
	// Debug
	// Glob.PrintInfo("MakeStep", "-----------------------------")
	// Glob.PrintInfo("MakeStep", fmt.Sprintf("[%v][%v] : %v", s.(Search.TableauxProof)[0].Rule_name, s.AppliedOn().GetIndex(), s.AppliedOn().ToString()))
	// Glob.PrintInfo("MakeStep", " ")
	// Glob.PrintInfo("MakeStep", "Form list: ")
	// for _, v := range form_list.GetSlice() {
    //     Glob.PrintInfo("MakeStep", fmt.Sprintf("[%v] %v ",v.GetIndex(), v.ToString()))
    // }
	// Glob.PrintInfo("MakeStep", "")
	// Glob.PrintInfo("MakeStep", fmt.Sprintf("Real index: %v", index))
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
	case Search.RuleClosure: // F, neg F, ~Top or Bot
		res := ""
		if _, ok :=  s.AppliedOn().(AST.Bot); ok {
			res += fmt.Sprintf("eapply hasTableauBot with (i := %v).\n", index)
			res += "reflexivity.\n"
		} else {
			if s2, ok :=  s.AppliedOn().(AST.Not); ok {
				if _, ok2 :=  s2.GetForm().(AST.Top); ok2 {
					res += fmt.Sprintf("eapply hasTableauNegTop with (i := %v).\n", index)
					res += "reflexivity.\n"
				} else {
					index_pos, index_neg := findIndexClosureRule(index, sub, s.AppliedOn(), form_list)
					res += fmt.Sprintf("eapply hasTableauContr with (i := %v) (j := %v).\n", index_pos, index_neg)
					res += "1: reflexivity. \n"
					res += "1: reflexivity. \n"
					res += "reflexivity.\n"
				}
			} else {
				index_pos, index_neg := findIndexClosureRule(index, sub, s.AppliedOn(), form_list)
				res += fmt.Sprintf("eapply hasTableauContr with (i := %v) (j := %v).\n", index_pos, index_neg)
				res += "1: reflexivity. \n"
				res += "1: reflexivity. \n"
				res += "reflexivity.\n"
			}
		}
		
		new_form_list := Lib.NewList[Lib.List[AST.Form]]()
		l1 := form_list.Copy(func(i AST.Form) AST.Form {return i})
		l1.Append(s.AppliedOn())
		new_form_list.Append(l1)

		return res, metas, skos
	case Search.RuleNotNot: // Neg (Neg F) -> F``
		f := s.ResultFormulas().At(0).At(0)
		// neg_neg_f := AST.MakerNot(AST.MakerNot(f))
		// l1.Append(neg_neg_f)
		l1.Append(f)
		
		next_res, next_metas, next_skos := makeProofAux(s.Children().At(0), l1, sub)
		
		res := fmt.Sprintf("eapply %v with (i := %v).\n", "hasTableauNegNeg", index)
		res += "1: reflexivity. \n"
		res += next_res
		
		return res, next_metas, next_skos
	case Search.RuleNotOr: // Neg (F \/ G) -> Neg F, Neg G
		idx_b1 := 0
		idx_neg_f := 0
		idx_neg_g := 1
		neg_f := s.ResultFormulas().At(idx_b1).At(idx_neg_f)
		neg_g := s.ResultFormulas().At(idx_b1).At(idx_neg_g)
		l1.Append(neg_f)
		l1.Append(neg_g)
		
		next_res, next_metas, next_skos := makeProofAux(s.Children().At(idx_b1), l1, sub)
		
		res := fmt.Sprintf("eapply %v with (i := %v).\n", "hasTableauNegOr", index)
		res += "1: reflexivity. \n"
		res += next_res
		
		return res, next_metas, next_skos
	case Search.RuleNotImp: // Neg (F -> G) -> Neg Neg F, Neg G, F	
		idx_b1 := 0
		idx_f := 0
		idx_neg_g := 1
		f := s.ResultFormulas().At(idx_b1).At(idx_f)
		neg_g := s.ResultFormulas().At(idx_b1).At(idx_neg_g)
		neg_neg_f := AST.MakerNot(AST.MakerNot(f))
		l1.Append(neg_neg_f)
		l1.Append(neg_g)
		l1.Append(f)
		
		next_res, next_metas, next_skos := makeProofAux(s.Children().At(idx_b1), l1, sub)
		
		res := fmt.Sprintf("eapply %v with (i := %v).\n", "hasTableauNegImp", index)
		res += "1: reflexivity.\n"
		res += next_res
		
		return res, next_metas, next_skos
	case Search.RuleAnd: // (F /\ G) -> Neg (Neg F)), Neg(Neg G), F, G
		idx_b1 := 0
		idx_f := 0
		idx_g := 1
		f := s.ResultFormulas().At(idx_b1).At(idx_f)
		g := s.ResultFormulas().At(idx_b1).At(idx_g)
		neg_neg_f := AST.MakerNot(f)
		neg_neg_g := AST.MakerNot(g)
		l1.Append(neg_neg_f)
		l1.Append(neg_neg_g)
		l1.Append(f)
		l1.Append(g)
		
		next_res, next_metas, next_skos := makeProofAux(s.Children().At(idx_b1), l1, sub)
		
		res := fmt.Sprintf("eapply %v with (i := %v).\n", "hasTableauAnd", index)
		res += "1: reflexivity. \n"
		res += next_res
		
		return res, next_metas, next_skos
	case Search.RuleNotAnd: // Neg (F /\ G) -> [Neg F \/ Neg G, Neg F] [Neg F \/ Neg G, Neg G]
		idx_b1 := 0
		idx_b2 := 1
		idx_neg_f := 0
		idx_neg_g := 0
		neg_f := s.ResultFormulas().At(idx_b1).At(idx_neg_f)
		neg_g := s.ResultFormulas().At(idx_b2).At(idx_neg_g)
		tmp_list := Lib.NewList[AST.Form]()
		tmp_list.Append(neg_f)
		tmp_list.Append(neg_g)
		neg_f_or_g := AST.MakerOr(tmp_list)

		l1.Append(neg_f_or_g)
		l1.Append(neg_f)
		l2.Append(neg_f_or_g)
		l2.Append(neg_g)
		
		next_res1, next_metas1, next_skos1 := makeProofAux(s.Children().At(idx_b1), l1, sub)
		next_res2, next_metas2, next_skos2 := makeProofAux(s.Children().At(idx_b2), l2, sub)
		
		s1, s2, sf1, sf2 := manageMetasFromChild(next_metas1), manageMetasFromChild(next_metas2), manageSkolemsFromChild(next_skos1), manageSkolemsFromChild(next_skos2)

		res := fmt.Sprintf("eapply hasTableauNegAnd with (S1 := %v) (S2 := %v) (Sf1 := %v) (Sf2 := %v) (i := %v).\n", s1, s2, sf1, sf2, index)
		res += "1: reflexivity.\n"
		res += "3: now esimpl. \n"
		res += "3: now esimpl. \n"
		res += "3: now esimpl. \n"
		res += fmt.Sprintf("{\n%v}\n", next_res1)
		res += fmt.Sprintf("{\n%v}\n", next_res2)

		
		new_metas := next_metas1.Union(next_metas2)
		new_skos := next_skos1.Union(next_skos2)
		
		return res, new_metas, new_skos
	case Search.RuleNotEqu:  // Neg (F <-> G) -> 
	// [ (Neg (F -> G) \/ (Neg (G -> F)), Neg (F -> G), Neg Neg F, Neg G, F] 
	// [ (Neg (F -> G) \/ (Neg (G -> F)), Neg (G -> F), Neg Neg G, Neg F, G]
		idx_b1 := 1
		idx_b2 := 0
		idx_f := 1
		idx_g := 0
		idx_neg_f := 1
		idx_neg_g := 0

		neg_f := s.ResultFormulas().At(idx_b1).At(idx_neg_f)
		g := s.ResultFormulas().At(idx_b1).At(idx_g)
		f := s.ResultFormulas().At(idx_b2).At(idx_f)
		neg_g := s.ResultFormulas().At(idx_b2).At(idx_neg_g)

		neg_neg_f := AST.MakerNot(neg_f)
		neg_neg_g := AST.MakerNot(neg_g)
		f_imp_g := AST.MakerImp(f, g)
		g_imp_f := AST.MakerImp(g, f)
		neg_f_imp_g := AST.MakerNot(f_imp_g)
		neg_g_imp_f := AST.MakerNot(g_imp_f)
		tmp_list := Lib.NewList[AST.Form]()
		tmp_list.Append(neg_f_imp_g)
		tmp_list.Append(neg_g_imp_f)
		neg_f_imp_g_or_neg_g_imp_f := AST.MakerOr(tmp_list)

		l1.Append(neg_f_imp_g_or_neg_g_imp_f)
		l1.Append(neg_f_imp_g)
		l1.Append(neg_neg_f)
		l1.Append(neg_g)
		l1.Append(f)

		l2.Append(neg_f_imp_g_or_neg_g_imp_f)
		l2.Append(neg_g_imp_f)
		l2.Append(neg_neg_g)
		l2.Append(neg_f)
		l2.Append(g)
	
		next_res1, next_metas1, next_skos1 := makeProofAux(s.Children().At(idx_b1), l2, sub)
		next_res2, next_metas2, next_skos2 := makeProofAux(s.Children().At(idx_b2), l1, sub)
		
		s1, s2, sf1, sf2 := manageMetasFromChild(next_metas1), manageMetasFromChild(next_metas2), manageSkolemsFromChild(next_skos1), manageSkolemsFromChild(next_skos2)

		res := fmt.Sprintf("eapply hasTableauNegEqu with (S1 := %v) (S2 := %v) (Sf1 := %v) (Sf2 := %v) (i := %v).\n", s1, s2, sf1, sf2, index)
		res += "1: reflexivity.\n"
		res += "3: now esimpl. \n"
		res += "3: now esimpl. \n"
		res += "3: now esimpl. \n"
		res += fmt.Sprintf("{\n%v}\n", next_res1)
		res += fmt.Sprintf("{\n%v}\n", next_res2)

		
		new_metas := next_metas1.Union(next_metas2)
		new_skos := next_skos1.Union(next_skos2)
		
		return res, new_metas, new_skos
	case Search.RuleOr: // (F \/ G) -> [F] [G]
		idx_b1 := 0
		idx_b2 := 1
		idx_f := 0
		idx_g := 0
		f := s.ResultFormulas().At(idx_b1).At(idx_f)
		g := s.ResultFormulas().At(idx_b2).At(idx_g)
		l1.Append(f)
		l2.Append(g)
		
		next_res1, next_metas1, next_skos1 := makeProofAux(s.Children().At(idx_b1), l1, sub)
		next_res2, next_metas2, next_skos2 := makeProofAux(s.Children().At(idx_b2), l2, sub)
		
		s1, s2, sf1, sf2 := manageMetasFromChild(next_metas1), manageMetasFromChild(next_metas2), manageSkolemsFromChild(next_skos1), manageSkolemsFromChild(next_skos2)

		res := fmt.Sprintf("eapply hasTableauOr with (S1 := %v) (S2 := %v) (Sf1 := %v) (Sf2 := %v) (i := %v).\n", s1, s2, sf1, sf2, index)
		res += "1: reflexivity.\n"
		res += "3: now esimpl. \n"
		res += "3: now esimpl. \n"
		res += "3: now esimpl. \n"
		res += fmt.Sprintf("{\n%v}\n", next_res1)
		res += fmt.Sprintf("{\n%v}\n", next_res2)

		
		new_metas := next_metas1.Union(next_metas2)
		new_skos := next_skos1.Union(next_skos2)
		
		return res, new_metas, new_skos
	case Search.RuleImp: // (F -> G) -> [neg F] [G]
		idx_b1 := 0
		idx_b2 := 1
		idx_neg_f := 0
		idx_g := 0
		neg_f := s.ResultFormulas().At(idx_b1).At(idx_neg_f)
		g := s.ResultFormulas().At(idx_b2).At(idx_g)
		l1.Append(neg_f)
		l2.Append(g)
		
		next_res1, next_metas1, next_skos1 := makeProofAux(s.Children().At(idx_b1), l1, sub)
		next_res2, next_metas2, next_skos2 := makeProofAux(s.Children().At(idx_b2), l2, sub)
		
		s1, s2, sf1, sf2 := manageMetasFromChild(next_metas1), manageMetasFromChild(next_metas2), manageSkolemsFromChild(next_skos1), manageSkolemsFromChild(next_skos2)

		res := fmt.Sprintf("eapply hasTableauImp with (S1 := %v) (S2 := %v) (Sf1 := %v) (Sf2 := %v) (i := %v).\n", s1, s2, sf1, sf2, index)
		res += "1: reflexivity.\n"
		res += "3: now esimpl. \n"
		res += "3: now esimpl. \n"
		res += "3: now esimpl. \n"
		res += fmt.Sprintf("{\n%v}\n", next_res1)
		res += fmt.Sprintf("{\n%v}\n", next_res2)

		
		new_metas := next_metas1.Union(next_metas2)
		new_skos := next_skos1.Union(next_skos2)
		
		return res, new_metas, new_skos
	case Search.RuleEqu: // (F <-> G) -> 
	// [ Neg (Neg (F -> G)), Neg (Neg (G -> F)), F -> G, G -> F, Neg F, Neg G] 
	// [ Neg (Neg (F -> G)), Neg (Neg (G -> F)), F -> G, G -> F, G, F]
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

		f_imp_g := AST.MakerImp(f, g)
		g_imp_f := AST.MakerImp(g, f)
		neg_neg_f_imp_g := AST.MakerNot(AST.MakerNot(f_imp_g))
		neg_neg_g_imp_f := AST.MakerNot(AST.MakerNot(g_imp_f))

		common_forms := []AST.Form{neg_neg_f_imp_g, neg_neg_g_imp_f, f_imp_g, g_imp_f}
		l1.Append3(common_forms)
		l1.Append(neg_f)
		l1.Append(neg_g)

		l2.Append3(common_forms)
		l2.Append(g)
		l2.Append(f)

		next_res1, next_metas1, next_skos1 := makeProofAux(s.Children().At(idx_b1), l1, sub)
		next_res2, next_metas2, next_skos2 := makeProofAux(s.Children().At(idx_b2), l2, sub)
		
		s1, s2, sf1, sf2 := manageMetasFromChild(next_metas1), manageMetasFromChild(next_metas2), manageSkolemsFromChild(next_skos1), manageSkolemsFromChild(next_skos2)

		res := fmt.Sprintf("eapply hasTableauEqu with (S1 := %v) (S2 := %v) (Sf1 := %v) (Sf2 := %v) (i := %v).\n", s1, s2, sf1, sf2, index)
		res += "1: reflexivity.\n"
		res += "3: now esimpl. \n"
		res += "3: now esimpl. \n"
		res += "3: now esimpl. \n"
		res += fmt.Sprintf("{\n%v}\n", next_res1)
		res += fmt.Sprintf("{\n%v}\n", next_res2)

		new_metas := next_metas1.Union(next_metas2)
		new_skos := next_skos1.Union(next_skos2)
		
		return res, new_metas, new_skos
	case Search.RuleNotEx: // Neg (Ex x F[x]) -> All x (neg F[x]), neg F[x -> t]
		all_f := AST.MakerAll(Lib.MkListV(s.AppliedOn().(AST.Not).GetForm().(AST.Ex).GetVarList().At(0)), AST.MakerNot(s.AppliedOn().(AST.Not).GetForm().(AST.Ex).GetForm()))
		l1.Append(all_f)
		f := s.ResultFormulas().At(0).At(0)
		l1.Append(f)

		real_generated_term := getRealGeneratedTerm(s)
		next_res, next_metas, next_skos := makeProofAux(s.Children().At(0), l1, sub)
		new_metas := next_metas.Copy()
		
		if meta_generated, ok := real_generated_term.(AST.Meta); ok {
			new_metas = new_metas.Add(meta_generated)
		} else {
			Glob.PrintError("MakeProofAux - TR", fmt.Sprintf("The generated term %v is not a meta", real_generated_term.ToString()))
		}

		res := fmt.Sprintf("unshelve eapply hasTableauNegEx with (i := %v).\n", index)
		res += "1-3: shelve.\n"
		res += fmt.Sprintf("1: exact \"%v\".\n", real_generated_term.ToString())
		res += "1: reflexivity.\n"
		res += "1: now esimpl.\n"
		res += "1: reflexivity.\n"
		res += "1: now esimpl.\n"
		res += next_res
	
		return res, new_metas, next_skos
	case Search.RuleAll: // All x F[x] -> F[x -> t]
		f := s.ResultFormulas().At(0).At(0)
		l1.Append(f)

		real_generated_term := getRealGeneratedTerm(s)
		next_res, next_metas, next_skos := makeProofAux(s.Children().At(0), l1, sub)
		new_metas := next_metas.Copy()
		
		if meta_generated, ok := real_generated_term.(AST.Meta); ok {
			new_metas = new_metas.Add(meta_generated)
		}

		res := fmt.Sprintf("unshelve eapply %v with (i := %v).\n", "hasTableauAll", index)
		res += "1-3: shelve.\n"
		res += fmt.Sprintf("1: exact \"%v\".\n", real_generated_term.ToString())
		res += "1: reflexivity.\n"
		res += "1: now esimpl.\n"
		res += "1: reflexivity.\n"
		res += "1: now esimpl.\n"
		res += next_res
	
		return res, new_metas, next_skos
	case Search.RuleNotAll: // Neg (All x F[x]) -> neg (F[x-> t])
		f := s.ResultFormulas().At(0).At(0)
		l1.Append(f)

		real_generated_term := getRealGeneratedTerm(s)
		next_res, next_metas, next_skos := makeProofAux(s.Children().At(0), l1, sub)

		sko := "OuterSkolemization"
		if Glob.IsInnerSko() {
			sko = "InnerSkolemization"
		}

		new_skos := next_skos.Copy()
		
		if skos_generated, ok := real_generated_term.(AST.Fun); ok {
			new_skos = new_skos.Add(skos_generated.GetID())
		}

		res := fmt.Sprintf("unshelve eapply hasTableauNegAll with (sko := %v) (i := %v).\n", sko, index)
		res += "1-3: shelve.\n"
		res += fmt.Sprintf("1: exact (%v).\n", TermToTR(real_generated_term))
		res += "2, 3: reflexivity.\n"
		res += "1: now esimpl.\n"
		res += "1: now esimpl.\n"
		res += next_res

		return res, next_metas, new_skos
	case Search.RuleEx: // Ex x F[x] -> neg (neg (Ex x F[x -> t])), F[x -> t]
		neg_neg_ex := AST.MakerNot(AST.MakerNot(s.AppliedOn().(AST.Ex).GetForm()))
		l1.Append(neg_neg_ex)
		f := s.ResultFormulas().At(0).At(0)
		l1.Append(f)

		real_generated_term := getRealGeneratedTerm(s)
		next_res, next_metas, next_skos := makeProofAux(s.Children().At(0), l1, sub)

		sko := "OuterSkolemization"
		if Glob.IsInnerSko() {
			sko = "InnerSkolemization"
		}

		new_skos := next_skos.Copy()
		
		if skos_generated, ok := real_generated_term.(AST.Fun); ok {
			new_skos = new_skos.Add(skos_generated.GetID())
		}

		res := fmt.Sprintf("unshelve eapply hasTableauEx with (sko := %v) (i := %v).\n", sko, index)
		res += "1-3: shelve.\n"
		res += fmt.Sprintf("1: exact (%v).\n", TermToTR(real_generated_term))
		res += "2, 3: reflexivity.\n"
		res += "1: now esimpl.\n"
		res += "1: now esimpl.\n"
		res += next_res

		return res, next_metas, new_skos
	case Search.RuleReintro: // Skip
		return makeProofAux(s.Children().At(0), form_list, sub)
	default:
		return "Error Admit.", metas, skos
	}
}

func makeProof(prf Search.IProof, sub Unif.Substitutions, form_list Lib.List[AST.Form]) string {
	res := ""	
	new_form_list := Lib.ListAdd(form_list, prf.AppliedOn())
	res_aux, metas_set, skos_set := makeProofAux(prf, new_form_list, sub)

	var_str := ""
	for i, v := range metas_set.Elements().GetSlice() {
		var_str += fmt.Sprintf(" \"%v\" ", v.ToString())
		if (i < metas_set.Cardinal()-1) {
			var_str += ","
		}
	}

	sko_str := ""
	for i, s := range skos_set.Elements().GetSlice() {
		sko_str += fmt.Sprintf(" \"%v\" ", s.GetName())
		if (i < skos_set.Cardinal()-1) {
			sko_str += ","
		}
	}

	
	res += fmt.Sprintf("exists \\{%v\\}, \\{%v\\}.\n", var_str, sko_str) + res

	return res + res_aux
}


// make && ./_build/goeland -otableauxrocq ../example/branching.p | grep -v '^%' | sed 's/\x1b\[[0-9;]*m//g' | grep -Ev '^\[[^]]+\]' > ../example/proof.v && rocq c ../example/proof.v          
package cc

import (
	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Core"
	"github.com/GoelandProver/Goeland/Glob"
	"github.com/GoelandProver/Goeland/Lib"
	"github.com/GoelandProver/Goeland/Mods/equality/eqStruct"
	"github.com/GoelandProver/Goeland/Search"
	"github.com/GoelandProver/Goeland/Unif"
)

var debug Glob.Debugger

func InitDebugger() {
	debug = Glob.CreateDebugger("plugin.equality")
}

func Enable() {
	SetTryEquality()
	eqStruct.NewEqStruct = eqStruct.NewEqStruct
}

func SetTryEquality() {
	Search.TryEquality = TryEquality
}

// TryEquality: entry point for equality reasoning on a leaf node
func TryEquality(atomics_for_dmt Core.FormAndTermsList, st Search.State, new_atomics Core.FormAndTermsList, father_id uint64, cha Search.Communication, node_id int, original_node_id int) bool {
	debug(Lib.MkLazy(func() string { return "TryEquality called" }))

	if len(atomics_for_dmt) == 0 && len(st.GetLF()) == 0 {
		return false
	}

	// Gather all atomic formulas for equality reasoning
	allAtomics := append(st.GetAtomic(), atomics_for_dmt...)

	// Run congruence closure on all atomic equalities
	success, subst := EqualityReasoning(st.GetEqStruct(), allAtomics.ExtractForms())

	if success {
		// Prepare substitution to send to proof search
		send_to_proof_search := Lib.NewList[Lib.List[Unif.MixedSubstitution]]()
		for _, s := range subst {
			local := Lib.NewList[Unif.MixedSubstitution]()
			for _, m := range s {
				local.Append(Unif.MkMixedFromSubst(m))
			}
			send_to_proof_search.Append(local)
		}

		Search.UsedSearch.ManageClosureRule(
			father_id,
			&st,
			cha,
			send_to_proof_search,
			Core.MakeFormAndTerm(AST.EmptyPredEq, Lib.NewList[AST.Term]()),
			node_id,
			original_node_id,
		)
		return true
	}

	return false
}

// EqualityReasoning: extract equalities and run congruence closure
func EqualityReasoning(eqStructInst eqStruct.EqualityStruct, atomics Lib.List[AST.Form]) (bool, []Unif.Substitutions) {
	debug(Lib.MkLazy(func() string { return "EqualityReasoning called" }))

	pairs := extractTermPairs(atomics)
	cc := NewCC()

	for _, pair := range pairs {
		cc.addTerm(pair.GetT1())
		cc.addTerm(pair.GetT2())
		if !cc.union(pair.GetT1(), pair.GetT2()) {
			return false, []Unif.Substitutions{}
		}
	}

	// Extract metavariable substitutions
	subst := deriveMetaSubst(cc, pairs)

	return true, []Unif.Substitutions{subst}
}

// extractTermPairs converts atomic equalities into eqStruct.TermPair
func extractTermPairs(atomics Lib.List[AST.Form]) []eqStruct.TermPair {
	res := []eqStruct.TermPair{}
	for _, f := range atomics.GetSlice() {
		if pred, ok := f.(AST.Pred); ok {
			if pred.GetID().Equals(AST.Id_eq) && pred.GetArgs().Len() == 2 {
				res = append(res, eqStruct.MakeTermPair(pred.GetArgs().At(0), pred.GetArgs().At(1)))
			}
		}
	}
	return res
}

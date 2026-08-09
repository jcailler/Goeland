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
* This file plugs the ground congruence closure into the proof search, in front
* of the rigid basic superposition procedure.
*
* Rigid basic superposition handles metavariables, which congruence closure
* cannot, but it pays for that generality even when there is nothing to
* instantiate: on a chain a0 = a1, ..., a(n-1) = an it explores the rewrite
* orderings one by one and blows up around n = 16. Congruence closure decides
* the ground fragment in near-linear time, so it is tried first and superposition
* is only reached when the ground fragment alone is not contradictory.
**/

package cc

import (
	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Core"
	"github.com/GoelandProver/Goeland/Glob"
	"github.com/GoelandProver/Goeland/Lib"
	equality "github.com/GoelandProver/Goeland/Mods/equality/bse"
	"github.com/GoelandProver/Goeland/Search"
	"github.com/GoelandProver/Goeland/Unif"
)

var debug Glob.Debugger

func InitDebugger() {
	debug = Glob.CreateDebugger("plugin.cc")
}

func Enable() {
	// Superposition remains the general procedure; congruence closure is only a
	// shortcut for the ground fragment.
	equality.Enable()
	Search.TryEquality = TryEquality
}

func TryEquality(
	atomics_for_dmt Core.FormAndTermsList,
	st Search.State,
	new_atomics Core.FormAndTermsList,
	father_id uint64,
	cha Search.Communication,
	node_id int,
	original_node_id int,
) bool {
	atomics := append(st.GetAtomic(), atomics_for_dmt...).ExtractForms()

	if GroundContradiction(atomics) {
		debug(Lib.MkLazy(func() string { return "Ground contradiction found by congruence closure" }))

		// The contradiction only involves ground literals, so it holds for every
		// instantiation of the branch's metavariables: the branch closes with no
		// substitution, and nothing has to be reported to the father.
		Search.UsedSearch.ManageClosureRule(
			father_id,
			&st,
			cha,
			Lib.NewList[Lib.List[Unif.MixedSubstitution]](),
			Core.MakeFormAndTerm(AST.EmptyPredEq, Lib.NewList[AST.Term]()),
			node_id,
			original_node_id,
		)
		return true
	}

	return equality.TryEquality(
		atomics_for_dmt, st, new_atomics, father_id, cha, node_id, original_node_id,
	)
}

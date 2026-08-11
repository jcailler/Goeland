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
 * This file tests the base functionnalities of DMT plugin :
 *	- Axioms of format : forall x.P(x)
 *	- Checks if it doesn't break the proof
 **/

package dmt_test

import (
	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Lib"
	"testing"

	"github.com/GoelandProver/Goeland/Mods/dmt"
)

/**
 * This function tests if : forall x.P(x) is rewritten as T/¬T
 **/
func TestAxiomRewriting(t *testing.T) {
	initDMT()

	// forall x.P(x)
	axiom := AST.MakerAll(Lib.MkListV[AST.TypedVar](x), AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar())))

	if dmt.RegisterAxiom(axiom) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it shouldn't.", axiom.ToString())
	}

	// Top
	// form := AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a))
	// substs, err := dmt.Rewrite(form)

	// if err != nil {
	// 	t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	// }

	// if len(substs) > 1 ||
	// 	!substs[0].GetSubst().Equals(Unif.MakeEmptySubstitution()) ||
	// 	len(substs[0].GetForm()) > 1 ||
	// 	!substs[0].GetForm()[0].Equals(AST.MakerTop()) {
	// 	t.Fatalf("Error: %s has not been rewritten as expected. Expected: %s, actual: %s.", form.ToString(), AST.MakerTop().ToString(), substs[0].GetForm()[0].ToString())
	// }

	// // ¬Top
	// form2 := AST.MakerNot(AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a)))
	// substs, err = dmt.Rewrite(form2)

	// if err != nil {
	// 	t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	// }

	// if len(substs) > 1 ||
	// 	!substs[0].GetSubst().Equals(Unif.MakeEmptySubstitution()) ||
	// 	len(substs[0].GetForm()) > 1 ||
	// 	!substs[0].GetForm()[0].Equals(AST.MakerNot(AST.MakerTop())) {
	// 	t.Fatalf("Error: %s has not been rewritten as expected. Expected: %s, actual: %s.", form2.ToString(), AST.MakerNot(AST.MakerTop()).ToString(), substs[0].GetForm()[0].ToString())
	// }
}

/**
 * This function tests if : forall x.¬P(x) is rewritten as Bot/¬Bot
 **/
func TestAxiomRewriting2(t *testing.T) {
	initDMT()

	// forall x.¬P(x)
	axiom := AST.MakerAll(Lib.MkListV[AST.TypedVar](x), AST.MakerNot(AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar()))))

	if dmt.RegisterAxiom(axiom) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it shouldn't.", axiom.ToString())
	}

	// Bot
	// form := AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a))
	// substs, err := dmt.Rewrite(form)

	// if err != nil {
	// 	t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	// }

	// if len(substs) > 1 ||
	// 	!substs[0].GetSubst().Equals(Unif.MakeEmptySubstitution()) ||
	// 	len(substs[0].GetForm()) > 1 ||
	// 	!substs[0].GetForm()[0].Equals(AST.MakerBot()) {
	// 	t.Fatalf("Error: %s has not been rewritten as expected. Expected: %s, actual: %s.", form.ToString(), AST.MakerBot().ToString(), substs[0].GetForm()[0].ToString())
	// }

	// // ¬Bot
	// form2 := AST.MakerNot(AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a)))
	// substs, err = dmt.Rewrite(form2)

	// if err != nil {
	// 	t.Fatalf("Error: %s not found in the rewrite tree when it should.", form2.ToString())
	// }

	// if len(substs) > 1 ||
	// 	!substs[0].GetSubst().Equals(Unif.MakeEmptySubstitution()) ||
	// 	len(substs[0].GetForm()) > 1 ||
	// 	!substs[0].GetForm()[0].Equals(AST.MakerNot(AST.MakerBot())) {
	// 	t.Fatalf("Error: %s has not been rewritten as expected. Expected: %s, actual: %s.", form2.ToString(), AST.MakerNot(AST.MakerBot()).ToString(), substs[0].GetForm()[0].ToString())
	// }
}

/**
 * This function tests if : forall x.P(x, x) is rewritten as T/¬T with the right substitutions
 **/
func TestAxiomRewriting3(t *testing.T) {
	initDMT()

	// forall x.P(x)
	axiom := AST.MakerAll(Lib.MkListV[AST.TypedVar](x), AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), x.ToBoundVar())))

	if dmt.RegisterAxiom(axiom) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it shouldn't.", axiom.ToString())
	}

	// X := AST.MakerMeta("X", 1, AST.TIndividual())
	// Y := AST.MakerMeta("Y", 1, AST.TIndividual())
	// // Top
	// form := AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](X, Y))
	// substs, err := dmt.Rewrite(form)

	// if err != nil {
	// 	t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	// }

	// Z1, _ := substs[0].GetSubst().Get(X)
	// Z2, _ := substs[0].GetSubst().Get(Y)

	// if len(substs) > 1 ||
	// 	!(Z1.Equals(Y) || Z2.Equals(X)) ||
	// 	len(substs[0].GetForm()) > 1 ||
	// 	!substs[0].GetForm()[0].Equals(AST.MakerTop()) {
	// 	t.Fatalf("Error: %s has not been rewritten as expected. Expected: %s, actual: %s.", form.ToString(), AST.MakerTop().ToString(), substs[0].GetForm()[0].ToString())
	// }

	// // ¬Top
	// form2 := AST.MakerNot(AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](X, Y)))
	// substs, err = dmt.Rewrite(form2)

	// if err != nil {
	// 	t.Fatalf("Error: %s not found in the rewrite tree when it should.", form2.ToString())
	// }

	// Z1, _ = substs[0].GetSubst().Get(X)
	// Z2, _ = substs[0].GetSubst().Get(Y)

	// if len(substs) > 1 ||
	// 	!(Z1.Equals(Y) || Z2.Equals(X)) ||
	// 	len(substs[0].GetForm()) > 1 ||
	// 	!substs[0].GetForm()[0].Equals(AST.MakerNot(AST.MakerTop())) {
	// 	t.Fatalf("Error: %s has not been rewritten as expected. Expected: %s, actual: %s.", form2.ToString(), AST.MakerNot(AST.MakerTop()).ToString(), substs[0].GetForm()[0].ToString())
	// }

	// // Top with subst
	// form3 := AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, Y))
	// substs, err = dmt.Rewrite(form3)

	// if err != nil {
	// 	t.Fatalf("Error: %s not found in the rewrite tree when it should.", form3.ToString())
	// }

	// Z2, _ = substs[0].GetSubst().Get(Y)

	// if len(substs) > 1 ||
	// 	!Z2.Equals(a) ||
	// 	len(substs[0].GetForm()) > 1 ||
	// 	!substs[0].GetForm()[0].Equals(AST.MakerTop()) {
	// 	t.Fatalf("Error: %s has not been rewritten as expected. Expected: %s, actual: %s.", form3.ToString(), AST.MakerTop().ToString(), substs[0].GetForm()[0].ToString())
	// }

	// // Should fail
	// form4 := AST.MakerPred(P, Lib.MkListV[AST.Term](a, AST.MakerConst(AST.MakerId("b"))), Lib.NewList[AST.Ty]())
	// substs, err = dmt.Rewrite(form4)

	// if err != nil {
	// 	t.Fatalf("Error: %s found in the rewrite tree when it shouldn't.", form4.ToString())
	// }

	// if len(substs) > 1 || !substs[0].GetSubst().Equals(Unif.Failure()) {
	// 	t.Fatalf("Error: error not triggered when searching for something not in the rewrite tree.")
	// }
}

/**
 * This function tests if : forall x.x = x & forall x.x != x
 **/
func TestAxiomRewriting4(t *testing.T) {
	initDMT()

	// forall x.x = x
	axiom := AST.MakerAll(Lib.MkListV[AST.TypedVar](x), AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), x.ToBoundVar())))

	if dmt.RegisterAxiom(axiom) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it's an equality.", axiom.ToString())
	}

	// forall x.x != x
	axiom = AST.MakerAll(Lib.MkListV[AST.TypedVar](x), AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), x.ToBoundVar())))

	if dmt.RegisterAxiom(axiom) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it's an equality.", axiom.ToString())
	}

	// forall x.¬(x = x)
	axiom = AST.MakerAll(Lib.MkListV[AST.TypedVar](x), AST.MakerNot(AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), x.ToBoundVar()))))

	if dmt.RegisterAxiom(axiom) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it's an equality.", axiom.ToString())
	}

	// forall x.¬(x != x)
	axiom = AST.MakerAll(Lib.MkListV[AST.TypedVar](x), AST.MakerNot(AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), x.ToBoundVar()))))

	if dmt.RegisterAxiom(axiom) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it's an equality.", axiom.ToString())
	}
}

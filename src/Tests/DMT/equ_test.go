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
 * This file tests the base functionalities of DMT plugin :
 *	- equivalence-only initialisation
 *	- feeding of equivalence axioms in the code-tree and rewrite test
 *	- feeding of non-equivalence axioms in the code-tree
 *	- feeding multiple versions of the same atom
 *	- feeding multiple versions of the same atom with a constant
 **/

package dmt_test

import (
	"fmt"
	"os"
	"testing"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Core"
	"github.com/GoelandProver/Goeland/Glob"
	"github.com/GoelandProver/Goeland/Mods/dmt"
	"github.com/GoelandProver/Goeland/Unif"
)

var a AST.Fun
var x AST.Var
var y AST.Var
var z AST.Var
var P AST.Id
var Q AST.Id
var f AST.Id

// Init variables for test
func TestMain(m *testing.M) {
	AST.Init()
	a = AST.MakerConst(AST.MakerId("a"))
	x = AST.MakerVar("x")
	y = AST.MakerVar("y")
	z = AST.MakerVar("z")
	P = AST.MakerId("P")
	Q = AST.MakerId("Q")
	f = AST.MakerId("f")
	os.Exit(m.Run())
}

// Makers a plugin manager and inits the DMT for equivalences tests
func initDMT() {
	dmt.InitPluginTests(false, false)
}

/******************************************************************************
 * TEST AXIOM REGISTRATION
 ******************************************************************************/

/**
 * This function tests that equivalence axioms are registered in the rewrite tree.
 **/
func TestEquRegistration(t *testing.T) {
	initDMT()

	// forall x.P(x) <=> forall y.Q(x, y)
	equPred := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerEqu(
			AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{}),
			AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(x, y), []AST.TypeApp{})),
		),
	)

	if !dmt.RegisterAxiom(equPred) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred.ToString())
	}

	// Something without forall should also be registered.

	// P(a) <=> forall y.Q(a, y)
	equPred2 := AST.MakerEqu(
		AST.MakerPred(P, AST.NewTermList(a), []AST.TypeApp{}),
		AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(a, y), []AST.TypeApp{})),
	)

	if !dmt.RegisterAxiom(equPred2) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred2.ToString())
	}

	// If the two formulas are atomic, it shouldn't be registered

	// forall x.P(x) <=> Q(x, a)
	equPred3 := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerEqu(
			AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{}),
			AST.MakerPred(Q, AST.NewTermList(x, a), []AST.TypeApp{}),
		),
	)

	if dmt.RegisterAxiom(equPred3) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it shouldn't (the two formulas are atomic).", equPred3.ToString())
	}

	// The right-side is atomic, and not the left !

	// forall x.(P(x) => Q(x, a)) <=> Q(a, x)
	equPred4 := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerEqu(
			AST.MakerImp(AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{}), AST.MakerPred(Q, AST.NewTermList(x, a), []AST.TypeApp{})),
			AST.MakerPred(Q, AST.NewTermList(a, x), []AST.TypeApp{}),
		),
	)

	if !dmt.RegisterAxiom(equPred4) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred4.ToString())
	}

	// Inside forall

	// forall x.(forall y.Q(x, y)) <=> P(x)
	equPred5 := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerEqu(
			AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(x, y), []AST.TypeApp{})),
			AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{}),
		),
	)

	if !dmt.RegisterAxiom(equPred5) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred5.ToString())
	}

	// Outside forall

	// forall x.forall y.Q(x, y) <=> P(x)
	equPred6 := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerAll(
			[]AST.Var{y},
			AST.MakerEqu(
				AST.MakerPred(Q, AST.NewTermList(x, y), []AST.TypeApp{}),
				AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{}),
			),
		),
	)

	if dmt.RegisterAxiom(equPred6) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it shouldn't.", equPred6.ToString())
	}

	// Negative atom

	// forall x.¬P(x) <=> forall y.Q(x, y)
	equPred7 := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerEqu(
			AST.RefuteForm(AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{})),
			AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(x, y), []AST.TypeApp{})),
		),
	)

	if !dmt.RegisterAxiom(equPred7) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred7.ToString())
	}

	// Negative atom & negative equivalence

	// forall x.¬P(x) <=> ¬forall y.Q(x, y)
	equPred8 := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerEqu(
			AST.RefuteForm(AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{})),
			AST.RefuteForm(AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(x, y), []AST.TypeApp{}))),
		),
	)

	if !dmt.RegisterAxiom(equPred8) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred8.ToString())
	}

	// (x = x) => forall x. P(x) shouldn't be registered (because equality and dmt are managed separately)
	neqPred := AST.MakerPred(AST.Id_eq, AST.NewTermList(x, x), []AST.TypeApp{})
	eqPred9 := AST.MakerEqu(
		neqPred,
		AST.MakerAll([]AST.Var{x}, AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{})),
	)
	if dmt.RegisterAxiom(eqPred9) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it shouldn't (equalities are not registered).", eqPred9.ToString())
	}

	// (Vx (x = x)) => forall x. P(x) shouldn't be registered
	neqPred2 := AST.MakerAll([]AST.Var{x}, AST.MakerPred(AST.Id_eq, AST.NewTermList(x, x), []AST.TypeApp{}))
	eqPred10 := AST.MakerEqu(
		neqPred2,
		AST.MakerAll([]AST.Var{x}, AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{})),
	)
	if dmt.RegisterAxiom(eqPred10) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it shouldn't (equalities are not registered).", eqPred10.ToString())
	}

	// forall x.¬(x = x) <=> forall y. Q(x, y) shouldn't be registered
	eqPred11 := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerEqu(
			AST.MakerNot(AST.MakerPred(AST.Id_eq, AST.NewTermList(x, x), []AST.TypeApp{})),
			AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(x, y), []AST.TypeApp{})),
		),
	)
	if dmt.RegisterAxiom(eqPred11) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it shouldn't (equalities are not registered).", eqPred11.ToString())
	}

}

/**
 * This function tests that simple axioms are registered in the rewrite tree.
 **/
func TestSimpleAxiomRegistration(t *testing.T) {
	initDMT()
	// forall x.P(x)
	simplePred := AST.MakerAll([]AST.Var{x}, AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{}))

	if dmt.RegisterAxiom(simplePred) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it shouldn't.", simplePred.ToString())
	}

	// If it's a fact, it shouldn't be registered

	// P(a)
	simplePred2 := AST.MakerPred(P, AST.NewTermList(a), []AST.TypeApp{})

	if dmt.RegisterAxiom(simplePred2) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it shouldn't (a fact has to be kept).", simplePred2.ToString())
	}

	// forall x.¬P(x)
	simplePred3 := AST.MakerAll([]AST.Var{x}, AST.RefuteForm(AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{})))

	if dmt.RegisterAxiom(simplePred3) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it shouldn't.", simplePred3.ToString())
	}

	// a = b shouldn't be registered (because equality and dmt are managed separately)
	eqPred := AST.MakerAll([]AST.Var{x}, AST.MakerPred(AST.Id_eq, AST.NewTermList(x, x), []AST.TypeApp{}))

	if dmt.RegisterAxiom(eqPred) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it shouldn't (equalities are not registered).", eqPred.ToString())
	}

	// a != b shouldn't be registered (because equality and dmt are managed separately)
	neqPred := AST.MakerAll([]AST.Var{x}, AST.MakerPred(AST.Id_eq, AST.NewTermList(x, x), []AST.TypeApp{}))

	if dmt.RegisterAxiom(neqPred) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it shouldn't (equalities are not registered).", neqPred.ToString())
	}
}

/**
 * This function tests that => axioms are registered in the rewrite tree.
 **/
func TestImpRegistration(t *testing.T) {
	initDMT()
	// forall x.P(x) => forall y.Q(x, y)
	impPred := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerImp(
			AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{}),
			AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(x, y), []AST.TypeApp{})),
		),
	)

	if dmt.RegisterAxiom(impPred) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when polarization isn't activated.", impPred.ToString())
	}
}

/******************************************************************************
 * TEST REWRITING
 ******************************************************************************/

/**
 * This function tests a simple rewrite with equivalence
 **/
func TestEquRewrite1(t *testing.T) {
	initDMT()
	// forall x.P(x) <=> forall y.Q(x, y)
	equPred := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerEqu(
			AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{}),
			AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(x, y), []AST.TypeApp{})),
		),
	)

	if !dmt.RegisterAxiom(equPred) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred.ToString())
	}

	form := AST.MakerPred(P, AST.NewTermList(a), []AST.TypeApp{})
	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	}

	if len(substs) > 1 {
		t.Fatalf("Error: more than one rewrite rule found for %s when it should have only one.", form.ToString())
	}

	forms := substs[0].GetSaf().GetForm()
	subst := substs[0].GetSaf().GetSubst()

	if forms.Len() > 1 {
		t.Fatalf("Error: %s can be rewritten by more than one formula when it should be rewritten by only one.", form.ToString())
	}

	if !forms.Get(0).Equals(AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(a, y), []AST.TypeApp{}))) ||
		subst.GetMeta().Len() > 0 {
		t.Fatalf("Error: %s has not been rewritten as expected. Actual: %s.", form.ToString(), forms.Get(0).ToString())
	}
}

/**
 * This function tests a negative rewrite with equivalence
 **/
func TestEquRewrite2(t *testing.T) {
	initDMT()
	// forall x.P(x) <=> forall y.Q(x, y)
	equPred := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerEqu(
			AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{}),
			AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(x, y), []AST.TypeApp{})),
		),
	)

	if !dmt.RegisterAxiom(equPred) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred.ToString())
	}

	form := AST.MakerNot(AST.MakerPred(P, AST.NewTermList(a), []AST.TypeApp{}))
	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	}

	if len(substs) > 1 {
		t.Fatalf("Error: more than one rewrite rule found for %s when it should have only one.", form.ToString())
	}

	forms := substs[0].GetSaf().GetForm()
	subst := substs[0].GetSaf().GetSubst()

	if forms.Len() > 1 {
		t.Fatalf("Error: %s can be rewritten by more than one formula when it should be rewritten by only one.", form.ToString())
	}

	if !forms.Get(0).Equals(AST.MakerNot(AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(a, y), []AST.TypeApp{})))) ||
		subst.GetMeta().Len() > 0 {
		t.Fatalf("Error: %s has not been rewritten as expected. Actual: %s.", form.ToString(), forms.Get(0).ToString())
	}
}

/**
 * Insertion of a negative atom
 **/
func TestEquRewrite3(t *testing.T) {
	initDMT()
	// forall x.¬P(x) <=> forall y.Q(x, y)
	equPred := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerEqu(
			AST.MakerNot(AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{})),
			AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(x, y), []AST.TypeApp{})),
		),
	)

	if !dmt.RegisterAxiom(equPred) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred.ToString())
	}

	form := AST.MakerPred(P, AST.NewTermList(a), []AST.TypeApp{})
	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	}

	if len(substs) > 1 {
		t.Fatalf("Error: more than one rewrite rule found for %s when it should have only one.", form.ToString())
	}

	forms := substs[0].GetSaf().GetForm()
	subst := substs[0].GetSaf().GetSubst()

	if forms.Len() > 1 {
		t.Fatalf("Error: %s can be rewritten by more than one formula when it should be rewritten by only one.", form.ToString())
	}

	if !forms.Get(0).Equals(AST.MakerNot(AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(a, y), []AST.TypeApp{})))) ||
		subst.GetMeta().Len() > 0 {
		t.Fatalf("Error: %s has not been rewritten as expected. Actual: %s.", form.ToString(), forms.Get(0).ToString())
	}
}

/**
 * Insertion of a negative atom
 **/
func TestEquRewrite4(t *testing.T) {
	initDMT()
	// forall x.¬P(x) <=> forall y.Q(x, y)
	equPred := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerEqu(
			AST.MakerNot(AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{})),
			AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(x, y), []AST.TypeApp{})),
		),
	)

	if !dmt.RegisterAxiom(equPred) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred.ToString())
	}

	form := AST.MakerNot(AST.MakerPred(P, AST.NewTermList(a), []AST.TypeApp{}))
	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	}

	if len(substs) > 1 {
		t.Fatalf("Error: more than one rewrite rule found for %s when it should have only one.", form.ToString())
	}

	forms := substs[0].GetSaf().GetForm()
	subst := substs[0].GetSaf().GetSubst()

	if forms.Len() > 1 {
		t.Fatalf("Error: %s can be rewritten by more than one formula when it should be rewritten by only one.", form.ToString())
	}

	if !forms.Get(0).Equals(AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(a, y), []AST.TypeApp{}))) ||
		subst.GetMeta().Len() > 0 {
		t.Fatalf("Error: %s has not been rewritten as expected. Actual: %s.", form.ToString(), forms.Get(0).ToString())
	}
}

/**
 * Insertion of a negative atom with negative equivalence
 **/
func TestEquRewrite5(t *testing.T) {
	initDMT()
	// forall x.¬P(x) <=> ¬forall y.Q(x, y)
	equPred := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerEqu(
			AST.MakerNot(AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{})),
			AST.MakerNot(AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(x, y), []AST.TypeApp{}))),
		),
	)

	if !dmt.RegisterAxiom(equPred) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred.ToString())
	}

	form := AST.MakerPred(P, AST.NewTermList(a), []AST.TypeApp{})
	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	}

	if len(substs) > 1 {
		t.Fatalf("Error: more than one rewrite rule found for %s when it should have only one.", form.ToString())
	}

	forms := substs[0].GetSaf().GetForm()
	subst := substs[0].GetSaf().GetSubst()

	if forms.Len() > 1 {
		t.Fatalf("Error: %s can be rewritten by more than one formula when it should be rewritten by only one.", form.ToString())
	}

	expected_rewrite := AST.MakerNot(AST.MakerNot(AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(a, y), []AST.TypeApp{}))))
	if !forms.Get(0).Equals(expected_rewrite) ||
		subst.GetMeta().Len() > 0 {
		t.Fatalf("Error: %s has not been rewritten as expected. Expected : %v — Actual: %s.", form.ToString(), expected_rewrite.ToString(), forms.Get(0).ToString())
	}
}

/**
 * Insertion of a negative atom with negative equivalence
 **/
func TestEquRewrite6(t *testing.T) {
	initDMT()
	// forall x.¬P(x) <=> ¬forall y.Q(x, y)
	equPred := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerEqu(
			AST.MakerNot(AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{})),
			AST.MakerNot(AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(x, y), []AST.TypeApp{}))),
		),
	)

	if !dmt.RegisterAxiom(equPred) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred.ToString())
	}

	form := AST.MakerNot(AST.MakerPred(P, AST.NewTermList(a), []AST.TypeApp{}))
	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	}

	if len(substs) > 1 {
		t.Fatalf("Error: more than one rewrite rule found for %s when it should have only one.", form.ToString())
	}

	forms := substs[0].GetSaf().GetForm()
	subst := substs[0].GetSaf().GetSubst()

	if forms.Len() > 1 {
		t.Fatalf("Error: %s can be rewritten by more than one formula when it should be rewritten by only one.", form.ToString())
	}

	if !forms.Get(0).Equals(AST.MakerNot(AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(a, y), []AST.TypeApp{})))) ||
		subst.GetMeta().Len() > 0 {
		t.Fatalf("Error: %s has not been rewritten as expected. Actual: %s.", form.ToString(), forms.Get(0).ToString())
	}
}

/**
 * Test subst
 **/
func TestSubst1(t *testing.T) {
	initDMT()
	Glob.EnableDebug()
	// forall x.P(x, x) <=> P(x, x) ^ Q(x, x)
	equPred := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerEqu(
			AST.MakerPred(P, AST.NewTermList(x, x), []AST.TypeApp{}),
			AST.MakerAnd(AST.NewFormList(AST.MakerPred(Q, AST.NewTermList(x, x), []AST.TypeApp{}), AST.MakerPred(P, AST.NewTermList(x, x), []AST.TypeApp{}))),
		),
	)
	Glob.PrintDebug("TS1", fmt.Sprintf("equ_pred : %v", equPred.ToString()))

	if !dmt.RegisterAxiom(equPred) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred.ToString())
	}

	Y := AST.MakerMeta("Y", 1)
	Z := AST.MakerMeta("Z", 1)

	form := AST.MakerPred(P, AST.NewTermList(Y, Z), []AST.TypeApp{})
	Glob.PrintDebug("TS1", fmt.Sprintf("form : %v", form.ToString()))

	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	}

	if len(substs) > 1 {
		t.Fatalf("Error: more than one rewrite rule found for %s when it should have only one.", form.ToString())
	}

	Glob.PrintDebug("TS1", fmt.Sprintf("after form : %v", form.ToString()))
	forms := substs[0].GetSaf().GetForm()
	subst := substs[0].GetSaf().GetSubst()

	if forms.Len() > 1 {
		t.Fatalf("Error: %s can be rewritten by more than one formula when it should be rewritten by only one.", form.ToString())
	}

	if !(forms.Get(0).Equals(AST.MakerAnd(AST.NewFormList(AST.MakerPred(Q, AST.NewTermList(Y, Y), []AST.TypeApp{}), AST.MakerPred(P, AST.NewTermList(Y, Y), []AST.TypeApp{})))) ||
		forms.Get(0).Equals(AST.MakerAnd(AST.NewFormList(AST.MakerPred(Q, AST.NewTermList(Z, Z), []AST.TypeApp{}), AST.MakerPred(P, AST.NewTermList(Z, Z), []AST.TypeApp{}))))) ||
		len(subst) != 1 {
		t.Fatalf("Error: %s has not been rewritten as expected. Actual: %s.", form.ToString(), forms.Get(0).ToString())
	}
}

/**
 * Test subst
 **/
func TestSubst2(t *testing.T) {
	initDMT()
	// P(a) <=> forall y.Q(a, y)
	equPred := AST.MakerEqu(
		AST.MakerPred(P, AST.NewTermList(a), []AST.TypeApp{}),
		AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(a, y), []AST.TypeApp{})),
	)

	if !dmt.RegisterAxiom(equPred) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred.ToString())
	}

	X := AST.MakerMeta("X", 1)

	form := AST.MakerPred(P, AST.NewTermList(X), []AST.TypeApp{})
	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	}

	if len(substs) > 1 {
		t.Fatalf("Error: more than one rewrite rule found for %s when it should have only one.", form.ToString())
	}

	forms := substs[0].GetSaf().GetForm()
	subst := substs[0].GetSaf().GetSubst()

	if forms.Len() > 1 {
		t.Fatalf("Error: %s can be rewritten by more than one formula when it should be rewritten by only one.", form.ToString())
	}

	Y, _ := subst.Get(X)

	if !forms.Get(0).Equals(AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(a, y), []AST.TypeApp{}))) ||
		!(len(subst) == 1 && Y.Equals(a)) {
		t.Fatalf("Error: %s has not been rewritten as expected. Actual: %s.", form.ToString(), forms.Get(0).ToString())
	}
}

func TestSubst3(t *testing.T) {
	initDMT()
	axiom := AST.MakerAll(
		[]AST.Var{x, y},
		AST.MakerEqu(
			AST.MakerPred(P, AST.NewTermList(x, AST.MakerFun(f, AST.NewTermList(y), []AST.TypeApp{})), []AST.TypeApp{}),
			AST.MakerAnd(AST.NewFormList(AST.MakerPred(Q, AST.NewTermList(x, y), []AST.TypeApp{}), AST.MakerPred(Q, AST.NewTermList(x, y), []AST.TypeApp{}))),
		),
	)

	if !dmt.RegisterAxiom(axiom) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", axiom.ToString())
	}

	X := AST.MakerMeta("X2", 1)
	Y := AST.MakerMeta("Y2", 1)

	form := AST.MakerPred(P, AST.NewTermList(X, Y), []AST.TypeApp{})
	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	}

	if len(substs) != 1 && !substs[0].GetSaf().GetSubst().Equals(Unif.Failure()) {
		t.Fatalf("Error: %s has not been rewritten as expected. Actual: %s - %v.", form.ToString(), substs[0].GetSaf().GetForm().Get(0).ToString(), substs[0].GetSaf().GetSubst().ToString())
	}
}

/******************************************************************************
 * TEST MULTIPLE VERSIONS OF ONE AXIOM
 ******************************************************************************/

func TestMultipleAxiomDefinition(t *testing.T) {
	initDMT()
	Glob.InitLogs()
	// P(a) <=> forall y.Q(a, y)
	equPred := AST.MakerEqu(
		AST.MakerPred(P, AST.NewTermList(a), []AST.TypeApp{}),
		AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(a, y), []AST.TypeApp{})),
	)
	// P(a) <=> forall y.Q(y, a)
	equPred2 := AST.MakerEqu(
		AST.MakerPred(P, AST.NewTermList(a), []AST.TypeApp{}),
		AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(y, a), []AST.TypeApp{})),
	)

	if !dmt.RegisterAxiom(equPred) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred.ToString())
	}
	if !dmt.RegisterAxiom(equPred2) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred2.ToString())
	}

	form := AST.MakerPred(P, AST.NewTermList(a), []AST.TypeApp{})
	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	}

	fmt.Printf("%v\n", Core.IntSubstAndFormListToString(substs))

	if len(substs) != 2 {
		t.Fatalf("Error: more than one rewrite rule found for %s when it should have only one.", form.ToString())
	}

	forms := substs[0].GetSaf().GetForm()
	forms.Append(substs[1].GetSaf().GetForm().Slice()...)

	if forms.Len() != 2 {
		t.Fatalf("Error: %s can be rewritten by more than two formulas when it should be rewritten by only two.", form.ToString())
	}

	rewrite1 := AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(a, y), []AST.TypeApp{}))
	rewrite2 := AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(y, a), []AST.TypeApp{}))
	if !forms.Contains(rewrite1) || !forms.Contains(rewrite2) {
		t.Fatalf("Error: %s has not been rewritten as expected. Expected: %v and %v. Actual: %s.", form.ToString(), rewrite1.ToString(), rewrite2.ToString(), forms.ToString())
	}
}

func TestMultipleAxiomDefinition2(t *testing.T) {
	initDMT()
	Glob.EnableDebug()
	// forall x.P(x) <=> forall y.Q(x, y)
	equPred := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerEqu(
			AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{}),
			AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(x, y), []AST.TypeApp{})),
		),
	)
	// forall x.P(x) <=> forall y.Q(y, a)
	equPred2 := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerEqu(
			AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{}),
			AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(y, x), []AST.TypeApp{})),
		),
	)

	if !dmt.RegisterAxiom(equPred) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred.ToString())
	}
	if !dmt.RegisterAxiom(equPred2) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred2.ToString())
	}

	form := AST.MakerPred(P, AST.NewTermList(a), []AST.TypeApp{})
	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	}

	if len(substs) != 2 {
		t.Fatalf("Error: more than one rewrite rule found for %s when it should have only one.", form.ToString())
	}

	forms := substs[0].GetSaf().GetForm()
	forms.Append(substs[1].GetSaf().GetForm().Slice()...)

	if forms.Len() != 2 {
		t.Fatalf("Error: %s can be rewritten by more than two formulas when it should be rewritten by only two.", form.ToString())
	}

	if !forms.Contains(AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(a, y), []AST.TypeApp{}))) ||
		!forms.Contains(AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(y, a), []AST.TypeApp{}))) {
		t.Fatalf("Error: %s has not been rewritten as expected. Actual: %s.", form.ToString(), forms.ToString())
	}
}

func TestMultipleAxiomDefinition3(t *testing.T) {
	initDMT()
	// forall x.P(x) <=> forall y.Q(x, y)
	equPred := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerEqu(
			AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{}),
			AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(x, y), []AST.TypeApp{})),
		),
	)
	// P(a) <=> forall y.Q(y, a)
	equPred2 :=
		AST.MakerEqu(
			AST.MakerPred(P, AST.NewTermList(a), []AST.TypeApp{}),
			AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(y, a), []AST.TypeApp{})))

	if !dmt.RegisterAxiom(equPred) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred.ToString())
	}
	if !dmt.RegisterAxiom(equPred2) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred2.ToString())
	}

	form := AST.MakerPred(P, AST.NewTermList(a), []AST.TypeApp{})
	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	}

	if len(substs) != 2 {
		t.Fatalf("Error: more than one rewrite rule found for %s when it should have only one.", form.ToString())
	}

	forms := substs[0].GetSaf().GetForm()
	forms.Append(substs[1].GetSaf().GetForm().Slice()...)

	if forms.Len() != 2 {
		t.Fatalf("Error: %s can be rewritten by more than two formulas when it should be rewritten by only two.", form.ToString())
	}

	if !forms.Contains(AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(a, y), []AST.TypeApp{}))) ||
		!forms.Contains(AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(y, a), []AST.TypeApp{}))) {
		t.Fatalf("Error: %s has not been rewritten as expected. Actual: %s.", form.ToString(), forms.ToString())
	}
}

/**
 * This function tests the error that should be returned if something is not in the rewrite tree
 **/
func TestError(t *testing.T) {
	initDMT()
	form := AST.MakerPred(P, AST.NewTermList(a), []AST.TypeApp{})
	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s found in rewrite tree when it's empty.", form.ToString())
	}

	if len(substs) > 1 || !substs[0].GetSaf().GetSubst().Equals(Unif.Failure()) {
		t.Fatalf("Error: error not triggered when searching for something not in the rewrite tree.")
	}
}

/**
 * Sorting test : top/bot formulas should be first in line
 **/
func TestSort(t *testing.T) {
	initDMT()
	equPred := AST.MakerAll(
		[]AST.Var{x},
		AST.MakerEqu(
			AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{}),
			AST.MakerAll([]AST.Var{y}, AST.MakerPred(Q, AST.NewTermList(x, y), []AST.TypeApp{})),
		),
	)

	if !dmt.RegisterAxiom(equPred) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", equPred.ToString())
	}

	axiom := AST.MakerAll([]AST.Var{x}, AST.MakerPred(P, AST.NewTermList(x), []AST.TypeApp{}))

	if dmt.RegisterAxiom(axiom) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it shouldn't.", axiom.ToString())
	}

	// forall x.P(x) and forall x.P(x) <=> forall y.Q(x, y) are in the rewrite tree.

	form := AST.MakerPred(P, AST.NewTermList(a), []AST.TypeApp{})
	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	}

	if len(substs) != 1 {
		t.Fatal("Error: substs size should be 1.")
	}

	others := substs[0].GetSaf().GetForm()

	if others.Len() > 1 {
		t.Fatal("Error: rewritten formulas are not properly sorted (2).")
	}
}

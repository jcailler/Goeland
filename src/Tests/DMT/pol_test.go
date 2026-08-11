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
 * This file tests the polarized functionnalities of the DMT plugin :
 *	- Axioms of format : (forall x).P => Q
 **/

package dmt_test

import (
	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Lib"
	"github.com/GoelandProver/Goeland/Unif"
	"testing"

	"github.com/GoelandProver/Goeland/Mods/dmt"
)

// Makers a plugin manager and inits the DMT for polarized tests
func initPolarizedDMT() {
	dmt.InitPluginTests(true, false)
}

/**
 * Tests if polarized insertion works properly (P => Q with P or Q or both atomics)
 **/
func TestPolarizedInsertion(t *testing.T) {
	initPolarizedDMT()

	polPred := AST.MakerAll(
		Lib.MkListV[AST.TypedVar](x),
		AST.MakerImp(
			AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar())),
			AST.MakerAll(Lib.MkListV[AST.TypedVar](y), AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), y.ToBoundVar()))),
		),
	)

	if !dmt.RegisterAxiom(polPred) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", polPred.ToString())
	}

	polPred2 := AST.MakerAll(
		Lib.MkListV[AST.TypedVar](x),
		AST.MakerImp(
			AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar())),
			AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), a)),
		),
	)

	if !dmt.RegisterAxiom(polPred2) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", polPred2.ToString())
	}

	polPred3 := AST.MakerAll(
		Lib.MkListV[AST.TypedVar](x),
		AST.MakerImp(
			AST.MakerAll(Lib.MkListV[AST.TypedVar](y), AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), y.ToBoundVar()))),
			AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar())),
		),
	)

	if !dmt.RegisterAxiom(polPred3) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", polPred3.ToString())
	}

	polPred4 := AST.MakerImp(
		AST.MakerAll(Lib.MkListV[AST.TypedVar](x), AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar()))),
		AST.MakerAll(Lib.MkListV[AST.TypedVar](x, y), AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), y.ToBoundVar()))),
	)

	if dmt.RegisterAxiom(polPred4) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it shouldn't be.", polPred4.ToString())
	}

	polPred5 := AST.MakerImp(
		AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a)),
		AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, a)),
	)

	if !dmt.RegisterAxiom(polPred5) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", polPred5.ToString())
	}

	polPred6 := AST.MakerAll(
		Lib.MkListV[AST.TypedVar](x),
		AST.MakerImp(
			AST.MakerNot(AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar()))),
			AST.MakerNot(AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), a))),
		),
	)

	if !dmt.RegisterAxiom(polPred6) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", polPred5.ToString())
	}

	// (x = x) => forall x. P(x) shouldn't be registered (because equality and dmt are managed separately)
	neqPred := AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), x.ToBoundVar()))
	polPred7 := AST.MakerImp(
		neqPred,
		AST.MakerAll(Lib.MkListV[AST.TypedVar](x), AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar()))),
	)
	if dmt.RegisterAxiom(polPred7) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it shouldn't (equalities are not registered).", polPred7.ToString())
	}

	// (Vx (x = x)) => forall x. P(x) shouldn't be registered
	neqPred2 := AST.MakerAll(Lib.MkListV[AST.TypedVar](x), AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), x.ToBoundVar())))
	polPred8 := AST.MakerImp(
		neqPred2,
		AST.MakerAll(Lib.MkListV[AST.TypedVar](x), AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar()))),
	)
	if dmt.RegisterAxiom(polPred8) {
		t.Fatalf("Error: %s has been registered as a rewrite rule when it shouldn't (equalities are not registered).", polPred8.ToString())
	}

	polPred9 := AST.MakerAll(
		Lib.MkListV[AST.TypedVar](x, y),
		AST.MakerImp(
			AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), y.ToBoundVar())),
			AST.MakerAnd(
				Lib.MkListV[AST.Form](
					AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), y.ToBoundVar())),
					AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), y.ToBoundVar())),
				),
			),
		),
	)

	if !dmt.RegisterAxiom(polPred9) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", polPred9.ToString())
	}
}

/**
 * Tests if polarized rewrite works properly
 **/
func TestPolarizedRewrite1(t *testing.T) {
	initPolarizedDMT()

	polPred := AST.MakerAll(
		Lib.MkListV[AST.TypedVar](x),
		AST.MakerImp(
			AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar())),
			AST.MakerAll(Lib.MkListV[AST.TypedVar](y), AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), y.ToBoundVar()))),
		),
	)

	if !dmt.RegisterAxiom(polPred) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", polPred.ToString())
	}

	// Only rewrites on positive occurrences of P
	form := AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a))
	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should have been.", form.ToString())
	}

	expected := AST.MakerAll(
		Lib.MkListV[AST.TypedVar](y),
		AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, y.ToBoundVar())),
	)

	if len(substs) > 1 ||
		substs[0].GetSaf().GetSubst().Len() != 0 ||
		substs[0].GetSaf().GetForm().Len() > 1 ||
		!substs[0].GetSaf().GetForm().At(0).Equals(expected) {
		t.Fatalf("Error: %s has not been rewritten as expected. Expected: %s, actual: %s.", form.ToString(), expected.ToString(), substs[0].GetSaf().GetForm().At(0).ToString())
	}

	form2 := AST.MakerNot(AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a)))
	substs, err = dmt.Rewrite(form2)

	if err != nil {
		t.Fatalf("Error: %s found in rewrite tree when it shouldn't be.", form2.ToString())
	}

	if len(substs) > 1 || substs[0].GetSaf().GetSubst().Len() != 0 {
		t.Fatalf("Error: error not triggered when searching for something not in the rewrite tree.")
	}

	// ¬forall y... should not have been inserted in the rewrite tree

	form3 := AST.MakerNot(expected)
	substs, err = dmt.Rewrite(form3)

	if err != nil {
		t.Fatalf("Error: %s found in rewrite tree when it shouldn't be.", form3.ToString())
	}

	if len(substs) > 1 || substs[0].GetSaf().GetSubst().Len() != 0 {
		t.Fatalf("Error: error not triggered when searching for something not in the rewrite tree.")
	}
}

/**
 * Tests if polarized rewrite works properly (atoms)
 **/
func TestPolarizedRewrite2(t *testing.T) {
	initPolarizedDMT()

	polPred := AST.MakerAll(
		Lib.MkListV[AST.TypedVar](x),
		AST.MakerImp(
			AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar())),
			AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), a)),
		),
	)

	if !dmt.RegisterAxiom(polPred) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", polPred.ToString())
	}

	// Only rewrites on positive occurrences of P
	form := AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a))
	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should have been.", form.ToString())
	}

	expected := AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, a))

	if len(substs) > 1 ||
		substs[0].GetSaf().GetSubst().Len() != 0 ||
		substs[0].GetSaf().GetForm().Len() > 1 ||
		!substs[0].GetSaf().GetForm().At(0).Equals(expected) {
		t.Fatalf("Error: %s has not been rewritten as expected. Expected: %s, actual: %s.", form.ToString(), expected.ToString(), substs[0].GetSaf().GetForm().At(0).ToString())
	}

	form2 := AST.MakerNot(AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a)))
	substs, err = dmt.Rewrite(form2)

	if err != nil {
		t.Fatalf("Error: %s found in rewrite tree when it shouldn't be.", form2.ToString())
	}

	if len(substs) > 1 || substs[0].GetSaf().GetSubst().Len() != 0 {
		t.Fatalf("Error: error not triggered when searching for something not in the rewrite tree.")
	}

	// Only rewrites negative occurrences of Q

	form3 := AST.MakerNot(AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, a)))
	substs, err = dmt.Rewrite(form3)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should have been.", form3.ToString())
	}

	expectedNeg := AST.MakerNot(AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a)))

	if len(substs) > 1 ||
		substs[0].GetSaf().GetSubst().Len() != 0 ||
		substs[0].GetSaf().GetForm().Len() > 1 ||
		!substs[0].GetSaf().GetForm().At(0).Equals(expectedNeg) {
		t.Fatalf("Error: %s has not been rewritten as expected. Expected: %s, actual: %s.", form3.ToString(), expectedNeg.ToString(), substs[0].GetSaf().GetForm().At(0).ToString())
	}

	form4 := AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, a))
	substs, err = dmt.Rewrite(form4)

	if err != nil {
		t.Fatalf("Error: %s found in rewrite tree when it shouldn't be.", form4.ToString())
	}

	if len(substs) > 1 || substs[0].GetSaf().GetSubst().Len() != 0 {
		t.Fatalf("Error: error not triggered when searching for something not in the rewrite tree.")
	}
}

/**
 * Tests if polarized rewrite works properly (negative atoms)
 **/
func TestPolarizedRewrite3(t *testing.T) {
	initPolarizedDMT()

	polPred := AST.MakerAll(
		Lib.MkListV[AST.TypedVar](x),
		AST.MakerImp(
			AST.MakerNot(AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar()))),
			AST.MakerNot(AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), a))),
		),
	)

	if !dmt.RegisterAxiom(polPred) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", polPred.ToString())
	}

	// Only rewrites on negative occurrences of P
	form := AST.MakerNot(AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a)))
	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should have been.", form.ToString())
	}

	expected := AST.MakerNot(AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, a)))

	if len(substs) > 1 ||
		substs[0].GetSaf().GetSubst().Len() != 0 ||
		substs[0].GetSaf().GetForm().Len() > 1 ||
		!substs[0].GetSaf().GetForm().At(0).Equals(expected) {
		t.Fatalf("Error: %s has not been rewritten as expected. Expected: %s, actual: %s.", form.ToString(), expected.ToString(), substs[0].GetSaf().GetForm().At(0).ToString())
	}

	form2 := AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a))
	substs, err = dmt.Rewrite(form2)

	if err != nil {
		t.Fatalf("Error: %s found in rewrite tree when it shouldn't be.", form2.ToString())
	}

	if len(substs) > 1 || substs[0].GetSaf().GetSubst().Len() != 0 {
		t.Fatalf("Error: error not triggered when searching for something not in the rewrite tree.")
	}

	// Only rewrites negative occurrences of Q

	form3 := AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, a))
	substs, err = dmt.Rewrite(form3)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should have been.", form3.ToString())
	}

	expectedNeg := AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a))

	if len(substs) > 1 ||
		substs[0].GetSaf().GetSubst().Len() != 0 ||
		substs[0].GetSaf().GetForm().Len() > 1 ||
		!substs[0].GetSaf().GetForm().At(0).Equals(expectedNeg) {
		t.Fatalf("Error: %s has not been rewritten as expected. Expected: %s, actual: %s.", form3.ToString(), expectedNeg.ToString(), substs[0].GetSaf().GetForm().At(0).ToString())
	}

	form4 := AST.MakerNot(AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, a)))
	substs, err = dmt.Rewrite(form4)

	if err != nil {
		t.Fatalf("Error: %s found in rewrite tree when it shouldn't be.", form4.ToString())
	}

	if len(substs) > 1 || substs[0].GetSaf().GetSubst().Len() != 0 {
		t.Fatalf("Error: error not triggered when searching for something not in the rewrite tree.")
	}
}

/**
 * Tests if polarized rewrite works properly (Bad unification)
 **/
func TestPolarizedRewrite4(t *testing.T) {
	initPolarizedDMT()

	axiom := AST.MakerAll(
		Lib.MkListV[AST.TypedVar](x, y),
		AST.MakerImp(
			AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), AST.MakerFun(f, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](y.ToBoundVar())))),
			AST.MakerAnd(Lib.MkListV[AST.Form](AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), y.ToBoundVar())), AST.MakerPred(Q, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), y.ToBoundVar()))))))

	if !dmt.RegisterAxiom(axiom) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", axiom.ToString())
	}

	X := AST.MakerMeta("X2", 1, AST.TIndividual())
	Y := AST.MakerMeta("Y2", 1, AST.TIndividual())

	form := AST.MakerPred(P, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](X, Y))
	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	}

	if len(substs) != 1 && substs[0].GetSaf().GetSubst().Len() != 0 {
		t.Fatalf("Error: %s has not been rewritten as expected. Actual: %s - %v.", form.ToString(), substs[0].GetSaf().GetForm().At(0).ToString(), substs[0].GetSaf().GetSubst().ToString(Unif.MixedSubstitution.ToString, ", ", "{}"))
	}
}

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
 * This file tests the preskolemized functionnalities of the DMT plugin.
 **/

package dmt_test

import (
	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Lib"
	"reflect"
	"testing"

	"github.com/GoelandProver/Goeland/Mods/dmt"
)

// Makers a plugin manager and inits the DMT for presko tests
func initPreskoDMT() {
	dmt.InitPluginTests(false, true)
}

func TestPreskolemization(t *testing.T) {
	initPreskoDMT()

	b := AST.MakerConst(AST.MakerId("b"))
	z := AST.MakerTypedVar("z", AST.TIndividual())
	subset := AST.MakerId("subset")
	in := AST.MakerId("in")

	// forall x, y. subset(x, y) <=> forall z. in(z, x) => in(z, y)
	axiom := AST.MakerAll(
		Lib.MkListV[AST.TypedVar](x, y),
		AST.MakerEqu(
			AST.MakerPred(subset, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), y.ToBoundVar())),
			AST.MakerAll(
				Lib.MkListV[AST.TypedVar](z),
				AST.MakerImp(
					AST.MakerPred(in, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](z.ToBoundVar(), x.ToBoundVar())),
					AST.MakerPred(in, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](z.ToBoundVar(), y.ToBoundVar())),
				),
			),
		),
	)

	if !dmt.RegisterAxiom(axiom) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", axiom.ToString())
	}

	// Positive occurrences should be rewritten normally
	form := AST.MakerPred(subset, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, b))
	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	}

	expected := AST.MakerAll(
		Lib.MkListV[AST.TypedVar](z),
		AST.MakerImp(
			AST.MakerPred(in, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](z.ToBoundVar(), a)),
			AST.MakerPred(in, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](z.ToBoundVar(), b)),
		),
	)

	if len(substs) > 1 ||
		substs[0].GetSaf().GetSubst().Len() != 0 ||
		substs[0].GetSaf().GetForm().Len() > 1 ||
		!substs[0].GetSaf().GetForm().At(0).Equals(expected) {
		t.Fatalf("Error: %s has not been rewritten as expected. Expected: %s, actual: %s.", form.ToString(), expected.ToString(), substs[0].GetSaf().GetForm().At(0).ToString())
	}

	// Negative occurrences should be skolemized
	form2 := AST.MakerNot(AST.MakerPred(subset, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, b)))
	substs, err = dmt.Rewrite(form2)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should.", form2.ToString())
	}

	if len(substs) > 1 ||
		substs[0].GetSaf().GetSubst().Len() != 0 ||
		substs[0].GetSaf().GetForm().Len() > 1 ||
		reflect.TypeOf(substs[0].GetSaf().GetForm().At(0)) != reflect.TypeOf(AST.Not{}) ||
		reflect.TypeOf(substs[0].GetSaf().GetForm().At(0).(AST.Not).GetForm()) != reflect.TypeOf(AST.Imp{}) ||
		!substs[0].GetSaf().GetForm().At(0).(AST.Not).GetForm().(AST.Imp).GetF1().(AST.Pred).GetArgs().At(0).IsFun() ||
		!substs[0].GetSaf().GetForm().At(0).(AST.Not).GetForm().(AST.Imp).GetF2().(AST.Pred).GetArgs().At(0).IsFun() {
		t.Fatalf("Error: %s has not been rewritten as expected. Actual: %s.", form2.ToString(), substs[0].GetSaf().GetForm().At(0).ToString())
	}
}

func TestPreskolemization2(t *testing.T) {
	initPreskoDMT()

	b := AST.MakerConst(AST.MakerId("b"))
	z := AST.MakerTypedVar("z", AST.TIndividual())
	subset := AST.MakerId("subset")
	in := AST.MakerId("in")

	// forall x, y. subset(x, y) <=> forall z. in(z, x) => in(z, y)
	axiom := AST.MakerAll(
		Lib.MkListV[AST.TypedVar](x, y),
		AST.MakerEqu(
			AST.MakerPred(subset, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x.ToBoundVar(), y.ToBoundVar())),
			AST.MakerEx(
				Lib.MkListV[AST.TypedVar](z),
				AST.MakerImp(
					AST.MakerPred(in, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](z.ToBoundVar(), x.ToBoundVar())),
					AST.MakerPred(in, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](z.ToBoundVar(), y.ToBoundVar())),
				),
			),
		),
	)

	if !dmt.RegisterAxiom(axiom) {
		t.Fatalf("Error: %s hasn't been registered as a rewrite rule.", axiom.ToString())
	}

	// Positive occurrences should be skolemized
	form := AST.MakerPred(subset, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, b))
	substs, err := dmt.Rewrite(form)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should.", form.ToString())
	}

	if len(substs) > 1 ||
		substs[0].GetSaf().GetSubst().Len() != 0 ||
		substs[0].GetSaf().GetForm().Len() > 1 ||
		reflect.TypeOf(substs[0].GetSaf().GetForm().At(0)) != reflect.TypeOf(AST.Imp{}) ||
		!substs[0].GetSaf().GetForm().At(0).(AST.Imp).GetF1().(AST.Pred).GetArgs().At(0).IsFun() ||
		!substs[0].GetSaf().GetForm().At(0).(AST.Imp).GetF2().(AST.Pred).GetArgs().At(0).IsFun() {
		t.Fatalf("Error: %s has not been rewritten as expected. Actual: %s.", form.ToString(), substs[0].GetSaf().GetForm().At(0).ToString())
	}

	// Negative occurrences should be rewritten normally
	form2 := AST.MakerNot(AST.MakerPred(subset, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, b)))
	substs, err = dmt.Rewrite(form2)

	if err != nil {
		t.Fatalf("Error: %s not found in the rewrite tree when it should.", form2.ToString())
	}

	expected := AST.MakerNot(AST.MakerEx(
		Lib.MkListV[AST.TypedVar](z),
		AST.MakerImp(
			AST.MakerPred(in, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](z.ToBoundVar(), a)),
			AST.MakerPred(in, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](z.ToBoundVar(), b)),
		),
	))

	if len(substs) > 1 ||
		substs[0].GetSaf().GetSubst().Len() != 0 ||
		substs[0].GetSaf().GetForm().Len() > 1 ||
		!substs[0].GetSaf().GetForm().At(0).Equals(expected) {
		t.Fatalf("Error: %s has not been rewritten as expected. Expected: %s, actual: %s.", form2.ToString(), expected.ToString(), substs[0].GetSaf().GetForm().At(0).ToString())
	}
}

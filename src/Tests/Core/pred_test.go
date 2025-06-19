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
 * This file tests predicates methods.
 **/

package basictypes_test

import (
	"os"
	"testing"

	"github.com/GoelandProver/Goeland/AST"
)

func TestMain(m *testing.M) {
	AST.Init()
	code := m.Run()
	os.Exit(code)
}

func TestConstantsPredicatesEquality(t *testing.T) {
	// Testing with constants
	a := AST.MakerConst(AST.MakerId("a"))
	p := AST.MakerId("P")

	p1 := AST.MakerPred(p, AST.NewTermList(a), []AST.TypeApp{})
	p2 := AST.MakerPred(p, AST.NewTermList(a), []AST.TypeApp{})

	if !p1.Equals(p2) {
		t.Errorf("%s != %s when it should be equal.", p1.ToString(), p2.ToString())
	}
}

func TestVariablesPredicatesEquality(t *testing.T) {
	// Testing with variables
	x := AST.MakerVar("x")
	p := AST.MakerId("P")

	p1 := AST.MakerPred(p, AST.NewTermList(x), []AST.TypeApp{})
	p2 := AST.MakerPred(p, AST.NewTermList(x), []AST.TypeApp{})

	if !p1.Equals(p2) {
		t.Errorf("%s != %s when it should be equal.", p1.ToString(), p2.ToString())
	}
}

func TestFunctionsPredicatesEquality(t *testing.T) {
	// Testing with functions
	x := AST.MakerVar("x")
	f := AST.MakerFun(AST.MakerId("f"), AST.NewTermList(x), []AST.TypeApp{})
	p := AST.MakerId("P")

	p1 := AST.MakerPred(p, AST.NewTermList(f), []AST.TypeApp{})
	p2 := AST.MakerPred(p, AST.NewTermList(f), []AST.TypeApp{})

	if !p1.Equals(p2) {
		t.Errorf("%s != %s when it should be equal.", p1.ToString(), p2.ToString())
	}
}

func TestTypedPredicatesEquality(t *testing.T) {
	x := AST.MakerVar("x", AST.MkTypeHint("int"))
	p := AST.MakerId("P")

	p1 := AST.MakerPred(p, AST.NewTermList(x), []AST.TypeApp{AST.MkTypeHint("int")})
	p2 := AST.MakerPred(p, AST.NewTermList(x), []AST.TypeApp{AST.MkTypeHint("int")})

	if !p1.Equals(p2) {
		t.Errorf("%s != %s when it should be equal.", p1.ToString(), p2.ToString())
	}
}

// Copy & Meta tests should be added

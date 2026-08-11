package basictypes_test

import (
	"testing"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Lib"
)

/* Two predicates built the same way have to be equal. */

func noTy() Lib.List[AST.Ty] { return Lib.NewList[AST.Ty]() }

func TestConstantsPredicatesEquality(t *testing.T) {
	a := AST.MakerConst(AST.MakerId("a"))
	p := AST.MakerId("P")

	p1 := AST.MakerPred(p, noTy(), Lib.MkListV[AST.Term](a))
	p2 := AST.MakerPred(p, noTy(), Lib.MkListV[AST.Term](a))

	if !p1.Equals(p2) {
		t.Errorf("%s != %s when it should be equal.", p1.ToString(), p2.ToString())
	}
}

func TestVariablesPredicatesEquality(t *testing.T) {
	x := AST.MakerVar("x")
	p := AST.MakerId("P")

	p1 := AST.MakerPred(p, noTy(), Lib.MkListV[AST.Term](x))
	p2 := AST.MakerPred(p, noTy(), Lib.MkListV[AST.Term](x))

	if !p1.Equals(p2) {
		t.Errorf("%s != %s when it should be equal.", p1.ToString(), p2.ToString())
	}
}

func TestFunctionsPredicatesEquality(t *testing.T) {
	x := AST.MakerVar("x")
	f := AST.MakerFun(AST.MakerId("f"), noTy(), Lib.MkListV[AST.Term](x))
	p := AST.MakerId("P")

	p1 := AST.MakerPred(p, noTy(), Lib.MkListV[AST.Term](f))
	p2 := AST.MakerPred(p, noTy(), Lib.MkListV[AST.Term](f))

	if !p1.Equals(p2) {
		t.Errorf("%s != %s when it should be equal.", p1.ToString(), p2.ToString())
	}
}

func TestTypedPredicatesEquality(t *testing.T) {
	x := AST.MakerVar("x")
	p := AST.MakerId("P")
	tys := Lib.MkListV(AST.MkTyConst("int"))

	p1 := AST.MakerPred(p, tys, Lib.MkListV[AST.Term](x))
	p2 := AST.MakerPred(p, tys, Lib.MkListV[AST.Term](x))

	if !p1.Equals(p2) {
		t.Errorf("%s != %s when it should be equal.", p1.ToString(), p2.ToString())
	}
}

func TestDifferentPredicatesDiffer(t *testing.T) {
	a := AST.MakerConst(AST.MakerId("a"))
	b := AST.MakerConst(AST.MakerId("b"))
	p := AST.MakerId("P")

	if AST.MakerPred(p, noTy(), Lib.MkListV[AST.Term](a)).
		Equals(AST.MakerPred(p, noTy(), Lib.MkListV[AST.Term](b))) {
		t.Errorf("P(a) and P(b) are reported equal.")
	}
}

package tests_origin

import (
	"testing"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Core"
	"github.com/GoelandProver/Goeland/Lib"
	"github.com/GoelandProver/Goeland/Unif"
)

func cst(name string) AST.Term {
	return AST.MakerFun(AST.MakerId(name), Lib.NewList[AST.Ty](), Lib.NewList[AST.Term]())
}

func fn(name string, args ...AST.Term) AST.Term {
	l := Lib.NewList[AST.Term]()
	l.Append(args...)
	return AST.MakerFun(AST.MakerId(name), Lib.NewList[AST.Ty](), l)
}

func substOf(m AST.Meta, t AST.Term) Lib.List[Unif.MixedSubstitution] {
	res := Lib.NewList[Unif.MixedSubstitution]()
	res.Append(Unif.MkMixedFromSubst(Unif.MakeSubstitution(m, t)))
	return res
}

// A term produced by a substitution remembers the metavariable it replaced.
func TestSubstitutedTermRemembersItsMeta(t *testing.T) {
	AST.Init()
	x := AST.MakerMeta("X", 1, AST.TIndividual())
	a := cst("a")

	got := AST.SubstituteMeta(x, x, a)
	if !got.Equals(a) {
		t.Fatalf("the term itself must read as the substituted one, got %v", got.ToString())
	}
	if !AST.Origin(got).Equals(x) {
		t.Fatalf("Origin should give X back, got %v", AST.Origin(got).ToString())
	}
}

// Everything but the proof output reads the substituted term: a term that
// replaced nothing is its own origin.
func TestUntouchedTermIsItsOwnOrigin(t *testing.T) {
	AST.Init()
	a := cst("a")
	if !AST.Origin(a).Equals(a) {
		t.Fatal("a term that replaced nothing is its own origin")
	}
}

// Substitutions compose: X |-> Y then Y |-> a must still point back at X.
func TestOriginFollowsComposition(t *testing.T) {
	AST.Init()
	x := AST.MakerMeta("X", 1, AST.TIndividual())
	y := AST.MakerMeta("Y", 2, AST.TIndividual())
	a := cst("a")

	viaY := AST.SubstituteMeta(x, x, y)    // X |-> Y
	viaA := AST.SubstituteMeta(viaY, y, a) // Y |-> a
	if !viaA.Equals(a) {
		t.Fatalf("expected a, got %v", viaA.ToString())
	}
	if !AST.Origin(viaA).Equals(x) {
		t.Fatalf("Origin should follow back to X, got %v", AST.Origin(viaA).ToString())
	}
}

// The origin survives the copies the proof search makes everywhere.
func TestOriginSurvivesCopy(t *testing.T) {
	AST.Init()
	x := AST.MakerMeta("X", 1, AST.TIndividual())
	got := AST.SubstituteMeta(x, x, fn("sk", cst("a")))
	if !AST.Origin(got.Copy()).Equals(x) {
		t.Fatal("Copy must carry the origin over")
	}
}

// And through the formula-level entry point used by the proof search.
func TestOriginThroughFormulaSubstitution(t *testing.T) {
	AST.Init()
	Core.InitDebugger()

	x := AST.MakerMeta("X", 1, AST.TIndividual())
	a := cst("a")
	args := Lib.NewList[AST.Term]()
	args.Append(x)
	form := AST.MakerPred(AST.MakerId("p"), Lib.NewList[AST.Ty](), args)

	res := Core.ApplySubstitutionsOnFormula(substOf(x, a), form)
	pred, ok := res.(AST.Pred)
	if !ok {
		t.Fatalf("expected a predicate, got %T", res)
	}
	arg := pred.GetArgs().At(0)
	if !arg.Equals(a) {
		t.Fatalf("the formula must read p(a), got %v", res.ToString())
	}
	if !AST.Origin(arg).Equals(x) {
		t.Fatalf("Origin of the argument should be X, got %v", AST.Origin(arg).ToString())
	}
}

package tests_subst

import (
	"testing"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Core"
	"github.com/GoelandProver/Goeland/Lib"
	"github.com/GoelandProver/Goeland/Unif"
)

func fn(name string, args ...AST.Term) AST.Term {
	l := Lib.NewList[AST.Term]()
	l.Append(args...)
	return AST.MakerFun(AST.MakerId(name), Lib.NewList[AST.Ty](), l)
}

func pred(name string, args ...AST.Term) AST.Form {
	l := Lib.NewList[AST.Term]()
	l.Append(args...)
	return AST.MakerPred(AST.MakerId(name), Lib.NewList[AST.Ty](), l)
}

func substOf(m AST.Meta, t AST.Term) Lib.List[Unif.MixedSubstitution] {
	res := Lib.NewList[Unif.MixedSubstitution]()
	res.Append(Unif.MkMixedFromSubst(Unif.MakeSubstitution(m, t)))
	return res
}

// Applying {X |-> a} must replace *every* X, including repeated occurrences
// nested inside a single argument. ReplaceSubTermBy stops at the first one,
// which is right for a superposition rewrite but wrong for a substitution.
func TestSubstitutionReplacesRepeatedOccurrencesInATerm(t *testing.T) {
	AST.Init()

	x := AST.MakerMeta("X", 1, AST.TIndividual())
	a := fn("a")

	got := AST.SubstituteMeta(fn("sk", x, x, fn("g", x)), x, a)
	want := fn("sk", a, a, fn("g", a))

	if !got.Equals(want) {
		t.Fatalf("sk(X,X,g(X)) with X |-> a: got %v", got.ToString())
	}
}

// Same, through the formula-level entry point used by the proof search.
func TestApplySubstitutionOnFormulaReplacesEveryOccurrence(t *testing.T) {
	AST.Init()
	Core.InitDebugger()

	x := AST.MakerMeta("X", 1, AST.TIndividual())
	a := fn("a")

	// This is the shape that broke SYN361+1: a metavariable repeated inside a
	// skolem term, itself an argument of the predicate.
	form := pred("q", fn("sk", x, x, fn("h")), x)
	got := Core.ApplySubstitutionsOnFormula(substOf(x, a), form)
	want := pred("q", fn("sk", a, a, fn("h")), a)

	if !got.Equals(want) {
		t.Fatalf("q(sk(X,X,h),X) with X |-> a: got %v", got.ToString())
	}
}

// And through the term-level entry point.
func TestApplySubstitutionOnTermReplacesEveryOccurrence(t *testing.T) {
	AST.Init()
	Core.InitDebugger()

	x := AST.MakerMeta("X", 1, AST.TIndividual())
	a := fn("a")

	got := Core.ApplySubstitutionsOnTerm(substOf(x, a), fn("sk", x, x))
	want := fn("sk", a, a)

	if !got.Equals(want) {
		t.Fatalf("sk(X,X) with X |-> a: got %v", got.ToString())
	}
}

// A metavariable that is not the one being substituted must be left alone.
func TestSubstitutionLeavesOtherMetasAlone(t *testing.T) {
	AST.Init()

	x := AST.MakerMeta("X", 1, AST.TIndividual())
	y := AST.MakerMeta("Y", 2, AST.TIndividual())
	a := fn("a")

	got := AST.SubstituteMeta(fn("sk", x, y, x), x, a)
	want := fn("sk", a, y, a)

	if !got.Equals(want) {
		t.Fatalf("sk(X,Y,X) with X |-> a: got %v", got.ToString())
	}
}

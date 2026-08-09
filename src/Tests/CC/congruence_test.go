package tests_cc

import (
	"fmt"
	"testing"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Lib"
	"github.com/GoelandProver/Goeland/Mods/equality/cc"
)

func cst(name string) AST.Term {
	return AST.MakerFun(AST.MakerId(name), Lib.NewList[AST.Ty](), Lib.NewList[AST.Term]())
}

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

func eq(l, r AST.Term) AST.Form {
	args := Lib.NewList[AST.Term]()
	args.Append(l, r)
	return AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), args)
}

func not(f AST.Form) AST.Form { return AST.MakerNot(f) }

func branch(forms ...AST.Form) Lib.List[AST.Form] {
	l := Lib.NewList[AST.Form]()
	l.Append(forms...)
	return l
}

func TestTransitivityOfEquality(t *testing.T) {
	c := cc.NewClosure()
	c.Assert(cst("a"), cst("b"))
	c.Assert(cst("b"), cst("c"))
	if !c.Equivalent(cst("a"), cst("c")) {
		t.Fatal("a = b and b = c should give a = c")
	}
	if c.Equivalent(cst("a"), cst("d")) {
		t.Fatal("a and d are unrelated")
	}
}

func TestCongruence(t *testing.T) {
	c := cc.NewClosure()
	c.Add(fn("f", cst("a")))
	c.Add(fn("f", cst("b")))
	c.Assert(cst("a"), cst("b"))
	if !c.Equivalent(fn("f", cst("a")), fn("f", cst("b"))) {
		t.Fatal("a = b should give f(a) = f(b)")
	}
}

// Congruence must also fire for terms nested several levels deep, and for
// arguments merged after the terms were registered.
func TestDeepCongruence(t *testing.T) {
	c := cc.NewClosure()
	left := fn("g", fn("f", cst("a")), cst("c"))
	right := fn("g", fn("f", cst("b")), cst("d"))
	c.Add(left)
	c.Add(right)
	c.Assert(cst("a"), cst("b"))
	if c.Equivalent(left, right) {
		t.Fatal("c = d has not been asserted yet")
	}
	c.Assert(cst("c"), cst("d"))
	if !c.Equivalent(left, right) {
		t.Fatal("a = b and c = d should give g(f(a),c) = g(f(b),d)")
	}
}

// Metavariables are opaque to congruence closure: a term containing one must be
// rejected rather than silently treated as a constant.
func TestNonGroundTermsAreRejected(t *testing.T) {
	c := cc.NewClosure()
	meta := AST.MakerMeta("X", 1, AST.TIndividual())
	if _, ok := c.Add(fn("f", meta)); ok {
		t.Fatal("f(X) is not ground and must not be added")
	}
	if c.Assert(meta, cst("a")) {
		t.Fatal("X = a is not a ground equality and must not be asserted")
	}
}

func TestGroundContradictionOnDisequality(t *testing.T) {
	// a = b, b = c, a != c
	b := branch(eq(cst("a"), cst("b")), eq(cst("b"), cst("c")), not(eq(cst("a"), cst("c"))))
	if !cc.GroundContradiction(b) {
		t.Fatal("a = b, b = c and a != c is contradictory")
	}
}

func TestGroundContradictionOnComplementaryLiterals(t *testing.T) {
	// a = b, p(a), ~p(b)
	b := branch(eq(cst("a"), cst("b")), pred("p", cst("a")), not(pred("p", cst("b"))))
	if !cc.GroundContradiction(b) {
		t.Fatal("a = b, p(a) and ~p(b) is contradictory")
	}
}

func TestNoSpuriousContradiction(t *testing.T) {
	// a = b, p(a), ~p(c): nothing forces c to be a or b.
	b := branch(eq(cst("a"), cst("b")), pred("p", cst("a")), not(pred("p", cst("c"))))
	if cc.GroundContradiction(b) {
		t.Fatal("a = b, p(a) and ~p(c) is satisfiable")
	}
}

// A branch whose contradiction needs a metavariable to be instantiated must be
// left to superposition: reporting it here would close the branch with an empty
// substitution, without telling the father which instantiation was used.
func TestNonGroundContradictionIsNotReported(t *testing.T) {
	meta := AST.MakerMeta("X", 1, AST.TIndividual())
	b := branch(eq(cst("a"), cst("b")), pred("p", cst("a")), not(pred("p", meta)))
	if cc.GroundContradiction(b) {
		t.Fatal("closing on p(a) vs ~p(X) needs X |-> a and is not a ground contradiction")
	}
}

// Chains are what superposition chokes on; make sure the closure stays linear.
func TestLongChain(t *testing.T) {
	forms := []AST.Form{}
	for i := 0; i < 200; i++ {
		forms = append(forms, eq(cst(fmt.Sprintf("a%d", i)), cst(fmt.Sprintf("a%d", i+1))))
	}
	forms = append(forms, pred("p", cst("a0")), not(pred("p", cst("a200"))))
	if !cc.GroundContradiction(branch(forms...)) {
		t.Fatal("a chain of 200 equalities should close the branch")
	}
}

package tests_unif

import (
	"testing"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Lib"
	"github.com/GoelandProver/Goeland/Unif"
)

func init() {
	Unif.InitDebugger()
}

func mkFun(name string) AST.Term {
	return AST.MakerFun(AST.MakerId(name), Lib.NewList[AST.Ty](), Lib.NewList[AST.Term]())
}

// Substitutions.Set must overwrite an existing binding, not silently drop it.
func TestSetOverwritesExistingKey(t *testing.T) {
	x := AST.MakerMeta("X", 1, AST.TIndividual())
	a, b := mkFun("a"), mkFun("b")

	s := Unif.MakeEmptySubstitution()
	s.Set(x, a)
	s.Set(x, b)

	v, i := s.Get(x)
	if i == -1 {
		t.Fatalf("X not bound at all")
	}
	if !v.Equals(b) {
		t.Fatalf("Set(X,b) after Set(X,a) silently dropped the new binding (X still bound to a)")
	}
}

// Merging {X|->a} with {X|->b} must fail, not silently keep {X|->a}.
func TestMergeConflictingSubstitutionsFails(t *testing.T) {
	x := AST.MakerMeta("X", 1, AST.TIndividual())
	a, b := mkFun("a"), mkFun("b")

	s1 := Unif.MakeEmptySubstitution()
	s1.Set(x, a)
	s2 := Unif.MakeEmptySubstitution()
	s2.Set(x, b)

	merged, _ := Unif.MergeSubstitutions(s1, s2)
	if !merged.Equals(Unif.Failure()) {
		v, _ := merged.Get(x)
		got := "<unbound>"
		if v != nil {
			if v.Equals(a) {
				got = "a"
			} else if v.Equals(b) {
				got = "b"
			} else {
				got = "other"
			}
		}
		t.Fatalf("merge({X|->a},{X|->b}) must be Failure; got a substitution binding X to %s", got)
	}
}

func cst(name string) AST.Term {
	return AST.MakerFun(AST.MakerId(name), Lib.NewList[AST.Ty](), Lib.NewList[AST.Term]())
}

func fn(name string, args ...AST.Term) AST.Term {
	l := Lib.NewList[AST.Term]()
	l.Append(args...)
	return AST.MakerFun(AST.MakerId(name), Lib.NewList[AST.Ty](), l)
}

// Reproduces the exact unification performed by the BSE equality module on
// TPTP MGT038+1 (issue #75):
//     cardinality_at_time(S, skolem(S, T))   vs   cardinality_at_time(fm, T)
// T occurs inside the skolem term, so this must FAIL the occur-check.
// It must never return the empty substitution, which callers read as
// "unifiable with no bindings needed".
func TestUnifyAgainstSkolemContainingTheMeta(t *testing.T) {
	s := AST.MakerMeta("S", 22, AST.TIndividual())
	to := AST.MakerMeta("TO", 38, AST.TIndividual())
	fm := cst("first_movers")

	l := fn("cardinality_at_time", s, fn("skolem@T220", s, to))
	r := fn("cardinality_at_time", fm, to)

	res := Unif.AddUnification(l, r, Unif.MakeEmptySubstitution())

	if res.Equals(Unif.Failure()) {
		return // correct: occur-check rejects it
	}
	if res.IsEmpty() {
		t.Fatalf("AddUnification returned the EMPTY substitution: callers read this as " +
			"'unifiable, no binding required', which closes a tableau branch unconditionally")
	}
	t.Fatalf("AddUnification returned a non-empty unifier %v for an occur-check violation", res.ToString())
}

// Same shape, but without the occur-check problem: the unifier must be returned,
// not silently swallowed.
func TestUnifyReturnsTheActualBindings(t *testing.T) {
	s := AST.MakerMeta("S", 22, AST.TIndividual())
	to := AST.MakerMeta("TO", 38, AST.TIndividual())
	fm := cst("first_movers")
	c := cst("c")

	l := fn("cardinality_at_time", s, c)
	r := fn("cardinality_at_time", fm, to)

	res := Unif.AddUnification(l, r, Unif.MakeEmptySubstitution())
	if res.Equals(Unif.Failure()) {
		t.Fatalf("terms are unifiable but AddUnification failed")
	}
	if res.IsEmpty() {
		t.Fatalf("AddUnification lost the unifier {S|->first_movers, TO|->c} and returned the empty substitution")
	}
	vs, _ := res.Get(s)
	vt, _ := res.Get(to)
	if vs == nil || !vs.Equals(fm) {
		t.Errorf("S should be bound to first_movers")
	}
	if vt == nil || !vt.Equals(c) {
		t.Errorf("TO should be bound to c")
	}
}

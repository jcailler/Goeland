package tests_subst

import (
	"testing"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Core"
	"github.com/GoelandProver/Goeland/Lib"
	"github.com/GoelandProver/Goeland/Unif"
)

func init() {
	Core.InitDebugger()
	Unif.InitDebugger()
}

func cst(name string) AST.Term {
	return AST.MakerFun(AST.MakerId(name), Lib.NewList[AST.Ty](), Lib.NewList[AST.Term]())
}

func mixed(bindings ...[2]any) Lib.List[Unif.MixedSubstitution] {
	res := Lib.NewList[Unif.MixedSubstitution]()
	for _, b := range bindings {
		res.Append(Unif.MkMixedFromSubst(
			Unif.MakeSubstitution(b[0].(AST.Meta), b[1].(AST.Term)),
		))
	}
	return res
}

func bound(t *testing.T, subs Lib.List[Unif.MixedSubstitution], m AST.Meta) (AST.Term, bool) {
	t.Helper()
	for _, s := range subs.GetSlice() {
		switch single := s.Substitution().(type) {
		case Lib.Some[Unif.Substitution]:
			k, v := single.Val.Get()
			if k.Equals(m) {
				return v, true
			}
		}
	}
	return nil, false
}

// A binding of a mother meta must always reach the father: it is what lets the
// father detect that two children disagree. Dropping it closes both children
// happily on incompatible instantiations (issue #76).
func TestMotherMetaBoundToATermIsKept(t *testing.T) {
	AST.Init()

	x := AST.MakerMeta("X", 1, AST.TIndividual())
	mm := Lib.EmptySet[AST.Meta]().Add(x)

	kept := Core.RemoveElementWithoutMM(mixed([2]any{x, cst("a")}), mm)
	if v, ok := bound(t, kept, x); !ok || !v.Equals(cst("a")) {
		t.Fatalf("X |-> a must be reported to the father, got %v", kept.Len())
	}
}

// Same, when the mother meta is bound to a *local* meta rather than to a term.
// Both branches of the switch used to test the same condition, so this case was
// dead and the binding vanished.
func TestMotherMetaBoundToALocalMetaIsKept(t *testing.T) {
	AST.Init()

	x := AST.MakerMeta("X", 1, AST.TIndividual())
	y := AST.MakerMeta("Y", 2, AST.TIndividual())
	mm := Lib.EmptySet[AST.Meta]().Add(x)

	kept := Core.RemoveElementWithoutMM(mixed([2]any{x, y}), mm)
	if kept.Empty() {
		t.Fatal("X |-> Y was dropped: the father never learns X is constrained")
	}
}

// And the constraint has to travel: once X |-> Y is known, whatever binds Y is
// a constraint on X too. This is the chain that made NLP002+1 provable while
// being countersatisfiable: X |-> Y, Y |-> Z, Z |-> a.
func TestConstraintTravelsThroughMetaChain(t *testing.T) {
	AST.Init()

	x := AST.MakerMeta("X", 1, AST.TIndividual())
	y := AST.MakerMeta("Y", 2, AST.TIndividual())
	z := AST.MakerMeta("Z", 3, AST.TIndividual())
	mm := Lib.EmptySet[AST.Meta]().Add(x)

	kept := Core.RemoveElementWithoutMM(
		mixed([2]any{x, y}, [2]any{y, z}, [2]any{z, cst("a")}),
		mm,
	)

	if _, ok := bound(t, kept, z); !ok {
		t.Fatalf("Z |-> a must be reported: X is transitively bound to a, got %d bindings", kept.Len())
	}
}

// A binding that has nothing to do with the father must still be dropped,
// otherwise every local instantiation would be sent up.
func TestUnrelatedBindingIsDropped(t *testing.T) {
	AST.Init()

	x := AST.MakerMeta("X", 1, AST.TIndividual())
	w := AST.MakerMeta("W", 4, AST.TIndividual())
	mm := Lib.EmptySet[AST.Meta]().Add(x)

	kept := Core.RemoveElementWithoutMM(mixed([2]any{w, cst("a")}), mm)
	if !kept.Empty() {
		t.Fatalf("W |-> a does not concern the father and must be dropped, got %d", kept.Len())
	}
}

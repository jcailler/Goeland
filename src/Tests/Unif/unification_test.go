package tests_unif

import (
	"fmt"
	"sort"
	"testing"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Unif"
)

// describe renders a substitution as a sorted set of bindings, so two
// implementations can be compared without depending on insertion order.
func describe(s Unif.Substitutions) string {
	if s.Equals(Unif.Failure()) {
		return "FAILURE"
	}
	pairs := []string{}
	for _, single := range s {
		k, v := single.Get()
		pairs = append(pairs, fmt.Sprintf("%s|->%s", k.ToString(), v.ToString()))
	}
	sort.Strings(pairs)
	return fmt.Sprint(pairs)
}

func withDT[T any](enabled bool, f func() T) T {
	previous := Unif.DiscriminationTreesEnabled()
	Unif.SetDiscriminationTrees(enabled)
	defer Unif.SetDiscriminationTrees(previous)
	return f()
}

// Unifying through the code tree machine and unifying the terms directly must
// give the same answer: -dt swaps the whole term machinery, not just the index.
func TestDirectUnificationMatchesCodeTreeMachine(t *testing.T) {
	AST.Init()

	a, b := cst("a"), cst("b")
	x, y, z := meta("X"), meta("Y"), meta("Z")

	cases := [][2]AST.Term{
		{a, a},
		{a, b},
		{x, a},
		{a, x},
		{x, y},
		{x, x},
		{fn("f", a), fn("f", a)},
		{fn("f", a), fn("f", b)},
		{fn("f", x), fn("f", a)},
		{fn("f", x), fn("g", a)},
		{fn("f", x), fn("f", fn("g", y))},
		{fn("g", x, x), fn("g", a, a)},
		{fn("g", x, x), fn("g", a, b)},
		{fn("g", x, y), fn("g", y, a)},
		{fn("g", x, fn("h", y)), fn("g", fn("h", a), z)},
		{x, fn("f", x)}, // occur-check
		{fn("f", x), fn("f", fn("g", fn("h", x)))}, // nested occur-check
		{fn("g", a, fn("h", b)), fn("g", a, fn("h", b))},
		{fn("g", x, y), fn("h", x, y)},
		{fn("f", a), a},
	}

	for _, c := range cases {
		fromMachine := withDT(false, func() Unif.Substitutions {
			return Unif.AddUnification(c[0].Copy(), c[1].Copy(), Unif.MakeEmptySubstitution())
		})
		fromDirect := withDT(true, func() Unif.Substitutions {
			return Unif.AddUnification(c[0].Copy(), c[1].Copy(), Unif.MakeEmptySubstitution())
		})

		if describe(fromMachine) != describe(fromDirect) {
			t.Errorf("unifying %s with %s:\n  code tree machine -> %s\n  direct            -> %s",
				c[0].ToString(), c[1].ToString(), describe(fromMachine), describe(fromDirect))
		}
	}
}

// Same, but starting from a substitution that already binds something: that is
// where the machine and a naive direct implementation are most likely to drift.
func TestDirectUnificationUnderExistingBindings(t *testing.T) {
	AST.Init()

	a, b := cst("a"), cst("b")
	x, y := meta("X"), meta("Y")

	build := func(bindings ...[2]AST.Term) Unif.Substitutions {
		s := Unif.MakeEmptySubstitution()
		for _, bd := range bindings {
			s.Set(bd[0].(AST.Meta), bd[1])
		}
		return s
	}

	cases := []struct {
		start  Unif.Substitutions
		t1, t2 AST.Term
	}{
		{build([2]AST.Term{x, a}), x, a},
		{build([2]AST.Term{x, a}), x, b},
		{build([2]AST.Term{x, a}), fn("f", x), fn("f", a)},
		{build([2]AST.Term{x, a}), fn("f", x), fn("f", y)},
		{build([2]AST.Term{x, a}, [2]AST.Term{y, b}), fn("g", x, y), fn("g", a, b)},
		{build([2]AST.Term{x, a}, [2]AST.Term{y, b}), fn("g", x, y), fn("g", a, a)},
		{build([2]AST.Term{x, fn("f", y)}), x, fn("f", a)},
	}

	for i, c := range cases {
		fromMachine := withDT(false, func() Unif.Substitutions {
			return Unif.AddUnification(c.t1.Copy(), c.t2.Copy(), c.start.Copy())
		})
		fromDirect := withDT(true, func() Unif.Substitutions {
			return Unif.AddUnification(c.t1.Copy(), c.t2.Copy(), c.start.Copy())
		})

		if describe(fromMachine) != describe(fromDirect) {
			t.Errorf("case %d, unifying %s with %s under %s:\n  code tree machine -> %s\n  direct            -> %s",
				i, c.t1.ToString(), c.t2.ToString(), describe(c.start),
				describe(fromMachine), describe(fromDirect))
		}
	}
}

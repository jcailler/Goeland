package tests_unif

import (
	"fmt"
	"sort"
	"testing"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Lib"
	"github.com/GoelandProver/Goeland/Unif"
)

func meta(name string) AST.Term {
	return AST.MakerMeta(name, 1, AST.TIndividual())
}

func atom(name string, args ...AST.Term) AST.Form {
	l := Lib.NewList[AST.Term]()
	l.Append(args...)
	return AST.MakerPred(AST.MakerId(name), Lib.NewList[AST.Ty](), l)
}

func forms(fs ...AST.Form) Lib.List[AST.Form] {
	l := Lib.NewList[AST.Form]()
	l.Append(fs...)
	return l
}

// matched returns the names of the indexed formulas the query unified with,
// sorted so that two indexes can be compared regardless of traversal order.
func matched(t *testing.T, ds Unif.DataStructure, query AST.Form) []string {
	t.Helper()
	_, substs := ds.Unify(query)
	out := []string{}
	for _, s := range substs {
		out = append(out, s.GetForm().ToString())
	}
	sort.Strings(out)
	return out
}

func sameAnswers(t *testing.T, index Lib.List[AST.Form], query AST.Form) {
	t.Helper()
	code := Unif.NewNode().MakeDataStruct(index, true)
	disc := Unif.NewDiscriminationTree().MakeDataStruct(index, true)

	expected := matched(t, code, query)
	got := matched(t, disc, query)

	if fmt.Sprint(expected) != fmt.Sprint(got) {
		t.Errorf("query %s:\n  code tree          -> %v\n  discrimination tree -> %v",
			query.ToString(), expected, got)
	}
}

func TestDiscriminationTreeAgreesWithCodeTree(t *testing.T) {
	AST.Init()

	a, b := cst("a"), cst("b")
	fa, fb := fn("f", a), fn("f", b)
	x, y := meta("X"), meta("Y")

	index := forms(
		atom("p", a),
		atom("p", b),
		atom("p", fa),
		atom("p", x),
		atom("q", a, b),
		atom("q", x, b),
		atom("q", a, y),
		atom("q", fa, fb),
		atom("r"),
	)

	queries := []AST.Form{
		atom("p", a),                  // exact, plus the indexed p(X)
		atom("p", fb),                 // only p(X) can match
		atom("p", x),                  // a query variable matches every p
		atom("p", fn("g", a)),         // nothing but p(X)
		atom("q", a, b),               // exact plus both partially general entries
		atom("q", fa, fb),             // exact plus q(X,b)? no: b vs f(b)
		atom("q", x, y),               // matches every q
		atom("r"),                     // nullary
		atom("s", a),                  // unknown symbol
		atom("p", fn("f", meta("Z"))), // f(Z) against f(a) and X
	}

	for _, q := range queries {
		sameAnswers(t, index, q)
	}
}

// Nested wildcards on both sides at once are where a naive flattening breaks:
// the query variable has to swallow a whole indexed subterm and vice versa.
func TestDiscriminationTreeNestedWildcards(t *testing.T) {
	AST.Init()

	x, y, z := meta("X"), meta("Y"), meta("Z")
	a := cst("a")

	index := forms(
		atom("p", fn("g", x, a)),
		atom("p", fn("g", fn("h", a), y)),
		atom("p", fn("g", fn("h", x), fn("h", y))),
		atom("p", z),
	)

	queries := []AST.Form{
		atom("p", fn("g", fn("h", a), a)),
		atom("p", fn("g", x, fn("h", a))),
		atom("p", fn("g", a, a)),
		atom("p", x),
	}

	for _, q := range queries {
		sameAnswers(t, index, q)
	}
}

// Negative literals go to the negative index, positive ones to the positive
// index; both must partition the same way as the code tree.
func TestDiscriminationTreePolarity(t *testing.T) {
	AST.Init()

	a := cst("a")
	index := forms(atom("p", a), AST.MakerNot(atom("p", a)), atom("q", a))

	for _, isPos := range []bool{true, false} {
		code := Unif.NewNode().MakeDataStruct(index, isPos)
		disc := Unif.NewDiscriminationTree().MakeDataStruct(index, isPos)
		for _, q := range []AST.Form{atom("p", a), atom("q", a)} {
			expected := matched(t, code, q)
			got := matched(t, disc, q)
			if fmt.Sprint(expected) != fmt.Sprint(got) {
				t.Errorf("is_pos=%v, query %s: code tree -> %v, discrimination tree -> %v",
					isPos, q.ToString(), expected, got)
			}
		}
	}
}

func TestDiscriminationTreeIsEmptyAndCopy(t *testing.T) {
	AST.Init()

	dt := Unif.NewDiscriminationTree()
	if !dt.IsEmpty() {
		t.Fatal("a fresh discrimination tree is empty")
	}

	filled := dt.MakeDataStruct(forms(atom("p", cst("a"))), true)
	if filled.IsEmpty() {
		t.Fatal("a tree holding p(a) is not empty")
	}

	// A copy must not share structure with its source.
	clone := filled.Copy()
	filled.InsertFormulaListToDataStructure(forms(atom("p", cst("b"))))
	if len(matched(t, clone, atom("p", cst("b")))) != 0 {
		t.Fatal("inserting into the source leaked into the copy")
	}
}

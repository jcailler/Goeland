/*
Tests of the type system.

The ten files this replaces targeted the type system Goeland used to carry:
TypeHint, TypeVar, TypeArrow, TypeCross, QuantifiedType, ParameterizedType,
TypeScheme, ComparableList and the TypeApp interface over them. None of those
exist any more, and neither do the methods a good half of the tests exercised,
Size() among them. What follows keeps the intent -- build a type, print it,
compare it, substitute in it, and read it back out of the global environment --
against AST.Ty and its constructors.
*/

package polymorphism_test

import (
	"os"
	"testing"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Lib"
	typing "github.com/GoelandProver/Goeland/Typing"
)

func TestMain(m *testing.M) {
	// Same order as main: AST defines the TPTP native types, Typing registers them.
	AST.InitDebugger()
	typing.InitDebugger()
	AST.Init()
	typing.Init()
	os.Exit(m.Run())
}

/** Construction and printing **/

func TestConstantTypePrintsItsSymbol(t *testing.T) {
	for _, symbol := range []string{"set", "list", "array", "vector", "map"} {
		if got := AST.MkTyConst(symbol).ToString(); got != symbol {
			t.Errorf("MkTyConst(%q) prints %q", symbol, got)
		}
	}
}

func TestConstructedTypePrintsItsArguments(t *testing.T) {
	list := AST.MkTyConstr("list", Lib.MkListV(AST.TIndividual()))

	if got := list.ToString(); got == "list" {
		t.Errorf("a constructed type prints like a constant: %q", got)
	}
}

func TestFunctionTypeReadsItsArgumentsAndResult(t *testing.T) {
	i, o := AST.TIndividual(), AST.TProp()
	pred := AST.MkTyFunc(AST.MkTyProd(Lib.MkListV(i, i)), o)

	args := AST.GetArgsTy(pred)
	if args.Len() != 2 {
		t.Fatalf("expected two argument types, got %d", args.Len())
	}
	if !args.At(0).Equals(i) || !args.At(1).Equals(i) {
		t.Errorf("argument types read back wrong: %s", args.ToString(AST.Ty.ToString, ", ", "[]"))
	}
	if !AST.GetOutTy(pred).Equals(o) {
		t.Errorf("result type read back wrong: %s", AST.GetOutTy(pred).ToString())
	}
}

func TestDefaultTypesHaveTheRightArity(t *testing.T) {
	if got := AST.GetArgsTy(AST.MkDefaultPredType(3)).Len(); got != 3 {
		t.Errorf("a default predicate type of arity 3 reports %d arguments", got)
	}
	if !AST.GetOutTy(AST.MkDefaultPredType(2)).Equals(AST.TProp()) {
		t.Errorf("a default predicate type does not land in $o")
	}
	if !AST.GetOutTy(AST.MkDefaultFunctionType(2)).Equals(AST.TIndividual()) {
		t.Errorf("a default function type does not land in $i")
	}
}

/** Equality **/

func TestEqualityIsStructural(t *testing.T) {
	i := AST.TIndividual()

	if !AST.MkTyConst("set").Equals(AST.MkTyConst("set")) {
		t.Errorf("two constants of the same symbol differ")
	}
	if AST.MkTyConst("set").Equals(AST.MkTyConst("list")) {
		t.Errorf("two constants of different symbols are equal")
	}
	if AST.MkTyConstr("list", Lib.MkListV(i)).Equals(AST.MkTyConstr("list", Lib.MkListV(AST.TProp()))) {
		t.Errorf("two constructed types differing by an argument are equal")
	}
	if !AST.MkTyFunc(AST.MkTyProd(Lib.MkListV(i)), i).
		Equals(AST.MkTyFunc(AST.MkTyProd(Lib.MkListV(i)), i)) {
		t.Errorf("two identical function types differ")
	}
}

func TestNativeTypesAreDistinct(t *testing.T) {
	natives := []AST.Ty{AST.TInt(), AST.TRat(), AST.TReal(), AST.TIndividual(), AST.TProp()}

	for i, a := range natives {
		for j, b := range natives {
			if i != j && a.Equals(b) {
				t.Errorf("%s and %s are reported equal", a.ToString(), b.ToString())
			}
		}
	}
	if !AST.IsTType(AST.TType()) {
		t.Errorf("$tType is not recognised as the type of types")
	}
	if AST.IsTType(AST.TIndividual()) {
		t.Errorf("$i is taken for the type of types")
	}
}

/** Instantiation **/

func TestInstantiationReplacesTheQuantifiedVariable(t *testing.T) {
	// ! [a] : a > a, instantiated at $i, is $i > $i.
	scheme := AST.MkTyPi(Lib.MkListV("a"), AST.MkTyFunc(AST.MkTyProd(Lib.MkListV(AST.MkTyVar("a"))), AST.MkTyVar("a")))
	instance := AST.InstantiateTy(scheme, Lib.MkListV(AST.TIndividual()))

	if !AST.GetOutTy(instance).Equals(AST.TIndividual()) {
		t.Errorf("instantiating at $i leaves the result type as %s", AST.GetOutTy(instance).ToString())
	}
	if args := AST.GetArgsTy(instance); args.Len() != 1 || !args.At(0).Equals(AST.TIndividual()) {
		t.Errorf("instantiating at $i leaves the argument type wrong")
	}
}

/** The global environment **/

func TestGlobalEnvironmentGivesASymbolBackItsType(t *testing.T) {
	i := AST.TIndividual()
	pred := AST.MkTyFunc(AST.MkTyProd(Lib.MkListV(i, i)), AST.TProp())

	typing.AddToGlobalEnv("goeland_test_pred", pred)

	switch got := typing.QueryEnvInstance("goeland_test_pred", Lib.NewList[AST.Ty]()).(type) {
	case Lib.Some[AST.Ty]:
		if !got.Val.Equals(pred) {
			t.Errorf("the environment gives back %s", got.Val.ToString())
		}
	default:
		t.Errorf("a symbol declared in the environment is not found again")
	}
}

func TestUnknownSymbolIsNotFound(t *testing.T) {
	switch typing.QueryEnvInstance("goeland_test_never_declared", Lib.NewList[AST.Ty]()).(type) {
	case Lib.Some[AST.Ty]:
		t.Errorf("an undeclared symbol is found in the environment")
	}
}

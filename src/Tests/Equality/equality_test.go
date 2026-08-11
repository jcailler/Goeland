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
* This file contains the tests on equality.
**/

package tests_equality

import (
	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Glob"
	"github.com/GoelandProver/Goeland/Lib"
	"github.com/GoelandProver/Goeland/Mods/equality/eqStruct"
	typing "github.com/GoelandProver/Goeland/Typing"
	"github.com/GoelandProver/Goeland/Unif"
	"os"
	"testing"
	"time"

	equality "github.com/GoelandProver/Goeland/Mods/equality/bse"
)

// Code trees
var tp, tn Unif.DataStructure

// Id
var p_id AST.Id
var g_id AST.Id
var f_id AST.Id
var a_id AST.Id
var b_id AST.Id
var c_id AST.Id
var d_id AST.Id
var e_id AST.Id
var c1_id AST.Id
var c2_id AST.Id
var h_id AST.Id

// Meta
var x AST.Meta
var y AST.Meta
var z AST.Meta
var z1 AST.Meta
var z2 AST.Meta
var z3 AST.Meta

// Const
var a AST.Fun
var b AST.Fun
var c AST.Fun
var d AST.Fun
var e AST.Fun
var c1 AST.Fun
var c2 AST.Fun

// Fun
var gx AST.Fun
var gy AST.Fun
var ga AST.Fun
var fx AST.Fun
var fy AST.Fun
var fa AST.Fun
var fb AST.Fun
var fc AST.Fun
var hx AST.Fun

var ggx AST.Fun
var gga AST.Fun
var gfy AST.Fun
var gfa AST.Fun
var fxy AST.Fun
var fyz AST.Fun
var ffx AST.Fun
var fxa AST.Fun
var fay AST.Fun
var fab AST.Fun
var fbc AST.Fun
var fcd AST.Fun
var gab AST.Fun
var fgy AST.Fun
var ghx AST.Fun
var hfab AST.Fun
var hgxbffb AST.Fun
var gxb AST.Fun
var ffb AST.Fun
var fdc AST.Fun

var gggx AST.Fun

var f_fxy_z AST.Fun
var f_x_fyz AST.Fun
var f_fab_c AST.Fun
var f_a_fbc AST.Fun

// Equalities
var eq_x_y AST.Pred
var eq_x_a AST.Pred
var eq_y_a AST.Pred
var eq_z1_c1 AST.Pred
var eq_z1_c2 AST.Pred
var eq_z2_c1 AST.Pred
var eq_z3_c1 AST.Pred
var eq_gx_fx AST.Pred
var eq_ggx_fa AST.Pred
var eq_gfy_y AST.Pred
var eq_fa_a AST.Pred
var eq_b_c AST.Pred
var eq_a_b AST.Pred
var eq_a_c AST.Pred
var eq_b_d AST.Pred
var eq_x_d AST.Pred
var eq_fx_gab AST.Pred
var eq_fy_y AST.Pred
var eq_a_ffb AST.Pred
var eq_b_fb AST.Pred
var eq_fgy_gfy AST.Pred
var eq_fdc_a AST.Pred

// Inequalites
var neq_x_a AST.Form
var neq_y_a AST.Form
var neq_a_b AST.Form
var neq_a_d AST.Form
var neq_gggx_x AST.Form
var neq_fx_a AST.Form
var neq_fx_x AST.Form
var neq_fab_fcd AST.Form
var neq_fb_fc AST.Form
var neq_hfab_hgxbffb AST.Form
var neq_ffb_a AST.Form
var neq_x_y AST.Form
var neq_ghx_x AST.Form
var neq_b_e AST.Form
var neq_ga_a AST.Form

// Form
var pggab AST.Form
var not_pac AST.Form
var pa AST.Form
var pb AST.Form
var not_pc AST.Form
var pab AST.Form
var pax AST.Form
var not_pcd AST.Form

func initTestVariable() {
	// Id
	p_id = AST.MakerId("P")
	g_id = AST.MakerId("g")
	f_id = AST.MakerId("f")
	a_id = AST.MakerId("a")
	b_id = AST.MakerId("b")
	c_id = AST.MakerId("c")
	d_id = AST.MakerId("d")
	e_id = AST.MakerId("e")
	c1_id = AST.MakerId("c1")
	c2_id = AST.MakerId("c2")
	h_id = AST.MakerId("h")

	// Meta
	x = AST.MakerMeta("X", -1, AST.MkTyConst("$i"))
	y = AST.MakerMeta("Y", -1, AST.MkTyConst("$i"))
	z = AST.MakerMeta("Z", -1, AST.MkTyConst("$i"))
	z1 = AST.MakerMeta("Z1", -1, AST.MkTyConst("$i"))
	z2 = AST.MakerMeta("Z2", -1, AST.MkTyConst("$i"))
	z3 = AST.MakerMeta("Z3", -1, AST.MkTyConst("$i"))

	// Const
	a = AST.MakerConst(a_id)
	b = AST.MakerConst(b_id)
	c = AST.MakerConst(c_id)
	d = AST.MakerConst(d_id)
	e = AST.MakerConst(e_id)
	c1 = AST.MakerConst(c1_id)
	c2 = AST.MakerConst(c2_id)

	// Fun
	gx = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x))
	gy = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](y))
	ga = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a))
	fx = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x))
	fy = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](y))
	fa = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a))
	fb = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](b))
	fc = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](c))
	hx = AST.MakerFun(h_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x))

	ggx = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](gx))
	gga = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](ga))
	gfy = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fy))
	gfa = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fa))
	fxy = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x, y))
	fyz = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](y, z))
	ffx = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fx))
	fxa = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x, a))
	fay = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, y))
	fab = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, b))
	fbc = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](b, c))
	fcd = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](c, d))
	gab = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, b))
	hfab = AST.MakerFun(h_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fa, b))
	gxb = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x, b))
	ffb = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fb))
	fgy = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](gy))
	fdc = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](d, c))
	ghx = AST.MakerFun(h_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](hx))
	hgxbffb = AST.MakerFun(h_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](gxb, ffb))

	gggx = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](ggx))

	f_fxy_z = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fxy, z))
	f_x_fyz = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x, fyz))
	f_fab_c = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fab, c))
	f_a_fbc = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, fbc))

	// Equalities
	eq_x_y = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x, y))
	eq_x_a = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x, a))
	eq_y_a = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](y, a))
	eq_z1_c1 = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](z1, c1))
	eq_z1_c2 = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](z1, c2))
	eq_z2_c1 = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](z2, c1))
	eq_z3_c1 = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](z3, c1))

	eq_ggx_fa = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](ggx, fa))
	eq_gfy_y = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](gfy, y))
	eq_gx_fx = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](gx, fx))
	eq_fa_a = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fa, a))
	eq_a_b = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, b))
	eq_b_c = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](b, c))
	eq_a_c = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, c))
	eq_b_d = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](b, d))
	eq_x_d = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x, d))
	eq_fx_gab = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fx, gab))
	eq_fy_y = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fy, y))
	eq_a_ffb = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, ffb))
	eq_b_fb = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](b, fb))
	eq_fgy_gfy = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fgy, gfy))
	eq_fdc_a = AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fdc, a))

	// Inequalites
	neq_x_a = AST.MakerNot(AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x, a)))
	neq_y_a = AST.MakerNot(AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](y, a)))
	neq_a_b = AST.MakerNot(AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, b)))
	neq_a_d = AST.MakerNot(AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, d)))
	neq_gggx_x = AST.MakerNot(AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](gggx, x)))
	neq_fx_a = AST.MakerNot(AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fx, a)))
	neq_fx_x = AST.MakerNot(AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fx, x)))
	neq_fab_fcd = AST.MakerNot(AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fab, fcd)))
	neq_fb_fc = AST.MakerNot(AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fb, fc)))
	neq_hfab_hgxbffb = AST.MakerNot(AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](hfab, hgxbffb)))
	neq_ffb_a = AST.MakerNot(AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](ffb, a)))
	neq_x_y = AST.MakerNot(AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x, y)))
	neq_ghx_x = AST.MakerNot(AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](ghx, x)))
	neq_b_e = AST.MakerNot(AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](b, e)))
	neq_ga_a = AST.MakerNot(AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](ga, a)))

	// Predicates
	pggab = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](gga, b))
	not_pac = AST.MakerNot(AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, c)))
	pa = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a))
	pb = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](b))
	not_pc = AST.MakerNot(AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](c)))
	pab = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, b))
	pax = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, x))
	not_pcd = AST.MakerNot(AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](c, d)))
}

func initCodeTreesTests(lf Lib.List[AST.Form]) (Unif.DataStructure, Unif.DataStructure) {
	tp = Unif.NewNode()
	tn = Unif.NewNode()
	tp = tp.MakeDataStruct(lf, true)
	tn = tn.MakeDataStruct(lf, false)
	return tp, tn
}

var eqStructure = eqStruct.NewEqStruct()

func initEqualityTest() {
	Glob.SetStart(time.Now())
	typing.Init()
	AST.Init()
	equality.Enable()
	initTestVariable()
	Glob.EnableDebug()
}

func checkAllCompatibleWith(areCompatbile []Unif.Substitutions, with ...Unif.Substitutions) bool {
	for _, isCompatible := range areCompatbile {
		if !checkSubsIsCompatibleWith(isCompatible, with...) {
			return false
		}
	}

	return true
}

func checkSubsIsCompatibleWith(isCompatible Unif.Substitutions, with ...Unif.Substitutions) bool {
	for _, sub := range with {
		if isFirstIncludedInSecond(sub, isCompatible) {
			return true
		}
	}

	return false
}

func isFirstIncludedInSecond(first Unif.Substitutions, second Unif.Substitutions) bool {
	secondList := Glob.NewList(second...)

	for _, firstElement := range first {
		if !secondList.Contains(firstElement) {
			return false
		}
	}

	return true
}

func TestMain(m *testing.M) {
	// The AST and the typing context have to stand before any term is built:
	// the TPTP native types are resolved lazily and panic on a nil type.
	// Same order as main: AST first, it defines the TPTP native types that the
	// typing context then registers.
	AST.InitDebugger()
	typing.InitDebugger()
	Unif.InitDebugger()
	equality.InitDebugger()
	AST.Init()
	typing.Init()
	code := m.Run()
	os.Exit(code)
}

/** Tests equality problem ***/
func TestEQ1(t *testing.T) {
	initEqualityTest()
	/**
	* Eq :
	* fa = a
	* ggx = fa
	*
	* Problem : gggx != x
	*
	* Solutions : (X, g(a)), (X, g(f(a)))
	**/

	lf := Lib.MkListV[AST.Form](eq_fa_a, eq_ggx_fa, neq_gggx_x)
	tp, tn = initCodeTreesTests(lf)
	res, subst := equality.EqualityReasoning(eqStructure, tp, tn, lf, 0)

	expectedSubst1 := Unif.MakeEmptySubstitution()
	expectedSubst1.Set(x, ga)

	expectedSubst2 := Unif.MakeEmptySubstitution()
	expectedSubst2.Set(x, gfa)

	if !res || !checkAllCompatibleWith(subst, expectedSubst1, expectedSubst2) {
		t.Fatalf("Error: %v - %v is not the expected substitution. expected : %v or %v", res, Unif.SubstListToString(subst), expectedSubst1.ToString(), expectedSubst2.ToString())
	}
}

func TestEQ2(t *testing.T) {
	initEqualityTest()
	/**
	* Eq :
	* b = c
	* gx = fx
	* gfy = y
	*
	* Problem : pb, ~pc
	*
	* Solutions : {} or X = Y
	**/

	lf := Lib.MkListV[AST.Form](eq_b_c, eq_gx_fx, eq_gfy_y, pb, not_pc)
	tp, tn = initCodeTreesTests(lf)
	res, subst := equality.EqualityReasoning(eqStructure, tp, tn, lf, 0)

	expectedSubst1 := Unif.MakeEmptySubstitution()
	expectedSubst1.Set(x, y)

	expectedSubst2 := Unif.MakeEmptySubstitution()

	if !res || !checkAllCompatibleWith(subst, expectedSubst1, expectedSubst2) {
		t.Fatalf("Error: %v - %v is not the expected substitution. expected : %v or %v", res, Unif.SubstListToString(subst), expectedSubst1.ToString(), expectedSubst2.ToString())
	}
}

func TestEQ3(t *testing.T) {
	initEqualityTest()
	/**
	* Eq :
	* b = c
	* gx = fx
	* gfy = y
	*
	* Problem : pggab, ~pac
	*
	* Solutions : {(X,a) (Y,a)}, {(X, a) (Y, X)}, {(X, Y) (Y, a)}
	**/

	lf := Lib.MkListV[AST.Form](eq_b_c, eq_gx_fx, eq_gfy_y, pggab, not_pac)
	tp, tn = initCodeTreesTests(lf)
	res, subst := equality.EqualityReasoning(eqStructure, tp, tn, lf, 0)

	expectedSubst1 := Unif.MakeEmptySubstitution()
	expectedSubst1.Set(x, a)
	expectedSubst1.Set(y, a)
	expectedSubst2 := Unif.MakeEmptySubstitution()
	expectedSubst2.Set(x, a)
	expectedSubst2.Set(y, x)
	expectedSubst3 := Unif.MakeEmptySubstitution()
	expectedSubst3.Set(x, y)
	expectedSubst3.Set(y, a)

	if !res || !checkAllCompatibleWith(subst, expectedSubst1, expectedSubst2, expectedSubst3) {
		t.Fatalf("Error: %v - %v is not the expected substitution. expected : %v", res, Unif.SubstListToString(subst), expectedSubst1.ToString())
	}
}

func TestEQ3bis(t *testing.T) {
	initEqualityTest()
	/**
	* Eq :
	* gx = fx
	* fy = y
	*
	* Problem : ga != a
	*
	* Solutions : {(X,a) (Y,a)}, {(X, a) (Y, X)}, {(X, Y) (Y, a)}
	**/

	lf := Lib.MkListV[AST.Form](eq_gx_fx, eq_fy_y, neq_ga_a)
	tp, tn = initCodeTreesTests(lf)
	res, subst := equality.EqualityReasoning(eqStructure, tp, tn, lf, 0)

	expectedSubst1 := Unif.MakeEmptySubstitution()
	expectedSubst1.Set(x, a)
	expectedSubst1.Set(y, a)
	expectedSubst2 := Unif.MakeEmptySubstitution()
	expectedSubst2.Set(x, a)
	expectedSubst2.Set(y, x)
	expectedSubst3 := Unif.MakeEmptySubstitution()
	expectedSubst3.Set(x, y)
	expectedSubst3.Set(y, a)

	if !res || !checkAllCompatibleWith(subst, expectedSubst1, expectedSubst2, expectedSubst3) {
		t.Fatalf("Error: %v - %v is not the expected substitution. expected : %v", res, Unif.SubstListToString(subst), expectedSubst1.ToString())
	}
}

func TestEQ4(t *testing.T) {
	initEqualityTest()
	/**
	* Eq :
	* b = c
	* gfy = y
	* x != a
	*
	* Problem : pggab, ~pac
	*
	* Solutions : {(X,a)}
	**/

	lf := Lib.MkListV[AST.Form](eq_b_c, eq_gfy_y, neq_x_a, pggab, not_pac)
	tp, tn = initCodeTreesTests(lf)
	res, subst := equality.EqualityReasoning(eqStructure, tp, tn, lf, 0)

	expectedSubst := Unif.MakeEmptySubstitution()
	expectedSubst.Set(x, a)

	if !res || !checkAllCompatibleWith(subst, expectedSubst) {
		t.Fatalf("Error: %v - %v - %v is not the expected substitution. expected : %v", res, len(subst), Unif.SubstListToString(subst), expectedSubst.ToString())
	}
}

func TestEQ5(t *testing.T) {
	initEqualityTest()
	/**
	* Eq :
	* Z1 = c1
	* Z2 = c1
	*
	* Problem : a != b
	*
	* Solutions : {(Z1,a) (Z2,b)} ou {(Z1, b) (Z2, a)}
	**/

	lf := Lib.MkListV[AST.Form](eq_z1_c1, eq_z2_c1, neq_a_b)
	tp, tn = initCodeTreesTests(lf)
	res, subst := equality.EqualityReasoning(eqStructure, tp, tn, lf, 0)

	expectedSubst1 := Unif.MakeEmptySubstitution()
	expectedSubst1.Set(z1, a)
	expectedSubst1.Set(z2, b)

	expectedSubst2 := Unif.MakeEmptySubstitution()
	expectedSubst2.Set(z1, b)
	expectedSubst2.Set(z2, a)

	if !res || !checkAllCompatibleWith(subst, expectedSubst1, expectedSubst2) {
		t.Fatalf("Error: %v -  %v is not the expected substitution. expected : %v or %v", res, Unif.SubstListToString(subst), expectedSubst1.ToString(), expectedSubst2.ToString())
	}

}

func TestEQ6(t *testing.T) {
	initEqualityTest()
	/* 18 solutions si on les cherche toutes */
	/* {<[Z1 ≈ c2, Z2 ≈ c1, Z3 ≈ c1], b, c> • {}}
	 *  {<[Z1 ≈ c2, Z2 ≈ c1, Z3 ≈ c1], a, c> • {}}
	 * {<[Z1 ≈ c2, Z2 ≈ c1, Z3 ≈ c1], a, b> • {}}
	 *
	 * Eq :
	 * Z1 = c2
	 * Z2 = c1
	 * Z3 = c1
	 *
	 * Neq :
	 * a != b
	 *
	 * Form :
	 * P(a)
	 * P(b)
	 * ~P(c)
	 *
	 * 3 Solutions (1 par problème d'égalité): Z2 et Z3 font l'égalité (Z2 = a et Z3 = b si on cherche (a, b) par exemple, ou le contraire)
	 * (Z2 = b et Z3 = c) (ou l'inverse)
	 * (Z2 = a et Z3 = c) (ou l'inverse)
	 * (Z2 = a et Z3 = b) (ou l'inverse)
	 *
	 **/

	lf := Lib.MkListV[AST.Form](pa, pb, not_pc, neq_a_b, eq_z1_c2, eq_z2_c1, eq_z3_c1)
	tp, tn = initCodeTreesTests(lf)
	res, subst := equality.EqualityReasoning(eqStructure, tp, tn, lf, 0)

	expectedSubst1 := Unif.MakeEmptySubstitution()
	expectedSubst1.Set(z2, b)
	expectedSubst1.Set(z3, c)

	expectedSubst1Bis := Unif.MakeEmptySubstitution()
	expectedSubst1Bis.Set(z2, c)
	expectedSubst1Bis.Set(z3, b)

	expectedSubst2 := Unif.MakeEmptySubstitution()
	expectedSubst2.Set(z2, a)
	expectedSubst2.Set(z3, c)

	expectedSubst2Bis := Unif.MakeEmptySubstitution()
	expectedSubst2Bis.Set(z2, c)
	expectedSubst2Bis.Set(z3, a)

	expectedSubst3 := Unif.MakeEmptySubstitution()
	expectedSubst3.Set(z2, a)
	expectedSubst3.Set(z3, b)

	expectedSubst3Bis := Unif.MakeEmptySubstitution()
	expectedSubst3Bis.Set(z2, b)
	expectedSubst3Bis.Set(z3, a)

	if !res || len(subst) == 0 {
		t.Fatalf("Error: %v -  %v is not the expected substitution. Expected true and 3", res, len(subst))
	}

	if !checkAllCompatibleWith(subst, expectedSubst1, expectedSubst1Bis, expectedSubst2, expectedSubst2Bis, expectedSubst3, expectedSubst3Bis) {
		t.Fatalf("Error: %v is not the expected substitution. Expected : %v or %v or %v", subst[0].ToString(), expectedSubst1.ToString(), expectedSubst2.ToString(), expectedSubst3.ToString())
	}
}

func TestEQ7(t *testing.T) {
	initEqualityTest()
	/**
	* Eq :
	* a = b
	*
	* Problem : a != b
	*
	* Solutions : {}
	**/

	lf := Lib.MkListV[AST.Form](eq_a_b, neq_a_b)
	tp, tn = initCodeTreesTests(lf)
	res, subst := equality.EqualityReasoning(eqStructure, tp, tn, lf, 0)

	if !res || !checkAllCompatibleWith(subst, Unif.MakeEmptySubstitution()) {
		t.Fatalf("Error: %v - %v is not the expected substitution. Expected empty solution", res, Unif.SubstListToString(subst))
	}
}

func TestEQ8(t *testing.T) {
	initEqualityTest()
	/**
	* Eq :
	* a = b
	*
	* Problem : a != d
	*
	* Solution : N/A
	*
	**/
	lf := Lib.MkListV[AST.Form](eq_a_b, neq_a_d)
	tp, tn = initCodeTreesTests(lf)
	res, subst := equality.EqualityReasoning(eqStructure, tp, tn, lf, 0)

	if res {
		t.Fatalf("Error: %v - %v is not the expected solution. Expected no solution", res, Unif.SubstListToString(subst))
	}

}

func TestImpossible(t *testing.T) {
	initEqualityTest()
	/**
	* Eq :
	* x = d
	*
	* Problem : fx != a
	*
	* Solutions : N/A
	**/

	lf := Lib.MkListV[AST.Form](eq_x_d, neq_fx_a)
	tp, tn = initCodeTreesTests(lf)
	res, subst := equality.EqualityReasoning(eqStructure, tp, tn, lf, 0)

	if res {
		t.Fatalf("Error: %v - %v is not the expected solution. Expected no solution", res, Unif.SubstListToString(subst))
	}
}

func TestSimon(t *testing.T) {
	initEqualityTest()
	/**
	* Eq :
	* x = a
	*
	* Problem : fx != x
	*
	* Solutions : {x -> fa}
	**/

	lf := Lib.MkListV[AST.Form](eq_x_a, neq_fx_x)
	tp, tn = initCodeTreesTests(lf)
	res, subst := equality.EqualityReasoning(eqStructure, tp, tn, lf, 0)

	expectedSubst := Unif.MakeEmptySubstitution()
	expectedSubst.Set(x, fa)

	if !res || !checkAllCompatibleWith(subst, expectedSubst) {
		t.Fatalf("Error: %v - %v - %v is not the expected substitution. expected : %v", res, len(subst), Unif.SubstListToString(subst), expectedSubst.ToString())
	}
}

func TestSeparation(t *testing.T) {
	initEqualityTest()
	/**
	* Eq :
	* a = c
	* b = d
	*
	* Problem : P(a, b), ~P(c, d)
	*
	* Solutions : {}
	**/

	lf := Lib.MkListV[AST.Form](pab, eq_a_c, eq_b_d, not_pcd)
	tp, tn = initCodeTreesTests(lf)
	res, subst := equality.EqualityReasoning(eqStructure, tp, tn, lf, 0)

	if !res || !checkAllCompatibleWith(subst, Unif.MakeEmptySubstitution()) {
		t.Fatalf("Error: %v - %v is not the expected substitution. Expected empty solution", res, Unif.SubstListToString(subst))
	}
}

func TestDeuxiemeSeparation(t *testing.T) {
	initEqualityTest()
	/**
	* Eq :
	* P(a, x)
	* a = c
	* b = d
	*
	* Problem : ~P(c, d)
	*
	* Solutions : {x -> d}, {x -> b}
	**/

	lf := Lib.MkListV[AST.Form](pax, eq_a_c, eq_b_d, not_pcd)
	tp, tn = initCodeTreesTests(lf)
	res, subst := equality.EqualityReasoning(eqStructure, tp, tn, lf, 0)

	expectedSubst1 := Unif.MakeEmptySubstitution()
	expectedSubst1.Set(x, d)
	expectedSubst2 := Unif.MakeEmptySubstitution()
	expectedSubst2.Set(x, b)

	if !res || !checkAllCompatibleWith(subst, expectedSubst1, expectedSubst2) {
		t.Fatalf("Error: %v - %v - %v is not the expected substitution. expected : %v", res, len(subst), Unif.SubstListToString(subst), expectedSubst1.ToString())
	}
}

func TestMultiListes(t *testing.T) {
	initEqualityTest()
	/**
	* Eq :
	* P(a, x)
	* P(a, b)
	* a = c
	* b = d
	*
	* Problem : ~P(c, d)
	*
	* Solutions : {}, {x -> d}, {x -> b}
	**/

	lf := Lib.MkListV[AST.Form](pax, pab, eq_a_c, eq_b_d, not_pcd)
	tp, tn = initCodeTreesTests(lf)
	res, subst := equality.EqualityReasoning(eqStructure, tp, tn, lf, 0)

	expectedSubst1 := Unif.MakeEmptySubstitution()
	expectedSubst1.Set(x, d)
	expectedSubst2 := Unif.MakeEmptySubstitution()
	expectedSubst2.Set(x, b)
	expectedSubst3 := Unif.MakeEmptySubstitution()

	if !res || !checkAllCompatibleWith(subst, expectedSubst1, expectedSubst2, expectedSubst3) {
		t.Fatalf("Error: %v - %v - %v is not the expected substitution. expected : %v", res, len(subst), Unif.SubstListToString(subst), expectedSubst1.ToString())
	}
}

func TestSubsEnMeta(t *testing.T) {
	initEqualityTest()
	/**
	* Eq :
	* X = a
	*
	* Problem : a = Y
	*
	* Solutions : {X -> Y}, {Y -> X}, {Y -> a}
	**/

	lf := Lib.MkListV[AST.Form](eq_x_a, neq_y_a)
	tp, tn = initCodeTreesTests(lf)
	res, subst := equality.EqualityReasoning(eqStructure, tp, tn, lf, 0)

	expectedSubst1 := Unif.MakeEmptySubstitution()
	expectedSubst1.Set(x, y)
	expectedSubst2 := Unif.MakeEmptySubstitution()
	expectedSubst2.Set(y, x)
	expectedSubst3 := Unif.MakeEmptySubstitution()
	expectedSubst3.Set(y, a)

	if !res || !checkAllCompatibleWith(subst, expectedSubst1, expectedSubst2, expectedSubst3) {
		t.Fatalf("Error: %v - %v - %v is not the expected substitution. expected : %v", res, len(subst), Unif.SubstListToString(subst), expectedSubst1.ToString())
	}
}

func TestContreExemple(t *testing.T) {
	initEqualityTest()
	/**
	* Eq :
	* x = a
	* y = a
	* P(b)
	*
	* Problem : ~P(c)
	*
	* Solutions : {x -> b, y -> c}
	**/

	lf := Lib.MkListV[AST.Form](eq_x_a, eq_y_a, pb, not_pc)
	tp, tn = initCodeTreesTests(lf)
	res, subst := equality.EqualityReasoning(eqStructure, tp, tn, lf, 0)

	expectedSubst := Unif.MakeEmptySubstitution()
	expectedSubst.Set(x, b)
	expectedSubst.Set(y, c)
	expectedSubstBis := Unif.MakeEmptySubstitution()
	expectedSubstBis.Set(x, c)
	expectedSubstBis.Set(y, b)

	if !res || !checkAllCompatibleWith(subst, expectedSubst, expectedSubstBis) {
		t.Fatalf("Error: %v - %v - %v is not the expected substitution. expected : %v", res, len(subst), Unif.SubstListToString(subst), expectedSubst.ToString())
	}
}

func TestCycle(t *testing.T) {
	initEqualityTest()
	/**
	* Eq :
	* f(g(Y)) = g(f(y))
	*
	* Problem : g(h(X)) = X
	*
	* Solutions : N/A
	**/

	lf := Lib.MkListV[AST.Form](eq_fgy_gfy, neq_ghx_x)
	tp, tn = initCodeTreesTests(lf)
	res, subst := equality.EqualityReasoning(eqStructure, tp, tn, lf, 0)

	if res {
		t.Fatalf("Error: %v - %v is not the expected solution. Expected no solution", res, Unif.SubstListToString(subst))
	}
}

func TestTemp(t *testing.T) {
	initEqualityTest()
	/**
	* Eq :
	* f(d, c) = a
	* X = d
	*
	* Problem : b = e
	*
	* Solutions : N/A
	**/

	lf := Lib.MkListV[AST.Form](eq_fdc_a, eq_x_d, neq_b_e)
	tp, tn = initCodeTreesTests(lf)
	res, subst := equality.EqualityReasoning(eqStructure, tp, tn, lf, 0)

	if res {
		t.Fatalf("Error: %v - %v is not the expected solution. Expected no solution", res, Unif.SubstListToString(subst))
	}
}

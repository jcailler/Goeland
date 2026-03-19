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
* This file contains the type definition for equality reasonning.
**/

package equality

import (
	"fmt"
	"math"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Core"
	"github.com/GoelandProver/Goeland/Glob"
	"github.com/GoelandProver/Goeland/Lib"
	"github.com/GoelandProver/Goeland/Mods/equality/eqStruct"
	"github.com/GoelandProver/Goeland/Unif"
)

type Equalities []eqStruct.TermPair

type Inequalities []eqStruct.TermPair

func (e Equalities) ToString() string {
	res := "["
	for i, tp := range e {
		res += tp.ToString()
		if i < len(e)-1 {
			res += ", "
		}
	}
	return res + "]"
}
func (e Equalities) ToTPTPString() string {
	res := ""
	for i, tp := range e {
		res += tp.ToTPTPString()
		if i < len(e)-1 {
			res += " & "
		}
	}
	return res + ""
}

func (ie Inequalities) ToString() string {
	res := ""
	for i, tp := range ie {
		res += tp.ToString()
		if i < len(ie) {
			res += ", "
		}
	}
	return res
}

func (e Equalities) copy() Equalities {
	res := []eqStruct.TermPair{}
	for _, tp := range e {
		res = append(res, tp.Copy())
	}
	return res
}

/* Apply a substitution on an equality */
func (e Equalities) applySubstitution(old_symbol AST.Meta, new_symbol AST.Term) Equalities {
	res := e.copy()
	for i, tp := range res {
		res[i] = eqStruct.MakeTermPair(
			Core.ApplySubstitutionOnTerm(old_symbol, new_symbol, tp.GetT1()),
			Core.ApplySubstitutionOnTerm(old_symbol, new_symbol, tp.GetT2()),
		)
	}
	return res
}

func (equs Equalities) getMetas() Lib.Set[AST.Meta] {
	metas := Lib.EmptySet[AST.Meta]()

	for _, equ := range equs {
		metas = metas.Union(equ.GetMetas())
	}

	return metas
}

func (equs Equalities) removeHalf() Equalities {
	return equs[int(math.Ceil(float64(len(equs))/2)):]
}

/* Retrieve equalities from a datastructure */
func retrieveEqualities(dt Unif.DataStructure) Equalities {
	debug(
		Lib.MkLazy(func() string { return fmt.Sprintf("Retrieve equalities") }),
	)
	res := Equalities{}
	meta_eq_ty := AST.MkTyMeta("META_TY_EQ", -99)
	MetaEQ1 := AST.MakerMeta("METAEQ1", -90, meta_eq_ty)
	MetaEQ2 := AST.MakerMeta("METAEQ2", -90, meta_eq_ty)

	eq_pred := AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.NewList[AST.Term]())

	eq_pred = AST.MakePred(
		AST.Id_eq,
		Lib.MkListV[AST.Ty](meta_eq_ty),
		Lib.MkListV[AST.Term](MetaEQ1, MetaEQ2),
	)

	debug(
		Lib.MkLazy(func() string { return fmt.Sprintf("Unify to find suitable candidates") }),
	)
	_, eq_list := dt.Unify(eq_pred)

	debug(
		Lib.MkLazy(func() string { return fmt.Sprintf("Candidates list:") }),
	)

	for _, ms := range eq_list {
		debug(
			Lib.MkLazy(func() string { return fmt.Sprintf("%v",ms.ToString()) }),
		)
	}
	
	for _, ms := range eq_list {
		debug(
			Lib.MkLazy(func() string {
				return fmt.Sprintf(
					"Reorder substitution: %v", ms.ToString())
			}),
		)
		ms_ordered := orderSubstForRetrieve(ms.MatchingSubstitutions().GetSubst(), MetaEQ1, MetaEQ2)
		debug(
			Lib.MkLazy(func() string {
				return fmt.Sprintf(
					"Substitution found for equalities: %v", ms_ordered.ToString())
			}),
		)

		eq1_term, ok_t1 := ms_ordered.Get(MetaEQ1)
		if ok_t1 == -1 {
			Glob.PrintError("RE", "Meta_eq_1 not found in map")
		}
		eq2_term, ok_t2 := ms_ordered.Get(MetaEQ2)
		if ok_t2 == -1 {
			Glob.PrintError("RE", "Meta_eq_2 not found in map")
		}
		res = append(res, eqStruct.MakeTermPair(eq1_term, eq2_term))
	}

	debug(
		Lib.MkLazy(func() string { return fmt.Sprintf("Final set of equalities: %v", res.ToString()) }),
	)

	return res
}

/* Retrieve inequalities from a datastructure */
func retrieveInequalities(dt Unif.DataStructure) Inequalities {
	debug(
		Lib.MkLazy(func() string { return fmt.Sprintf("Retrieve inequalities") }),
	)
	res := Inequalities{}
	meta_neq_ty := AST.MkTyMeta("META_TY_NEQ", -99)
	MetaNEQ1 := AST.MakerMeta("META_NEQ_1", -90, meta_neq_ty)
	MetaNEQ2 := AST.MakerMeta("META_NEQ_2", -90, meta_neq_ty)

	neq_pred := AST.MakerPred(AST.Id_eq, Lib.NewList[AST.Ty](), Lib.NewList[AST.Term]())
	neq_pred = AST.MakePred(
		AST.Id_eq,
		Lib.MkListV(meta_neq_ty),
		Lib.MkListV[AST.Term](MetaNEQ1, MetaNEQ2),
	)


	debug(
		Lib.MkLazy(func() string { return fmt.Sprintf("Unify to find suitable candidates") }),
	)

	_, neq_list := dt.Unify(neq_pred)

	debug(
		Lib.MkLazy(func() string { return fmt.Sprintf("Candidates list:") }),
	)

	for _, ms := range neq_list {
		debug(
			Lib.MkLazy(func() string { return fmt.Sprintf("%v",ms.ToString()) }),
		)
	}

	for _, ms := range neq_list {
				debug(
			Lib.MkLazy(func() string {
				return fmt.Sprintf(
					"Reorder substitution: %v", ms.ToString())
			}),
		)

		ms_ordered := orderSubstForRetrieve(
			ms.MatchingSubstitutions().GetSubst(),
			MetaNEQ1,
			MetaNEQ2,
		)

		debug(
			Lib.MkLazy(func() string {
				return fmt.Sprintf(
					"Substitution found for inequalities: %v", ms_ordered.ToString())
			}),
		)
		neq1_term, ok_t1 := ms_ordered.Get(MetaNEQ1)
		if ok_t1 == -1 {
			Glob.PrintError("RI", "Meta_eq_1 not found in map")
		}
		neq2_term, ok_t2 := ms_ordered.Get(MetaNEQ2)
		if ok_t2 == -1 {
			Glob.PrintError("RI", "Meta_eq_2 not found in map")
		}
		res = append(res, eqStruct.MakeTermPair(neq1_term, neq2_term))
	}


	debug(
		Lib.MkLazy(func() string { return fmt.Sprintf("Final set of inequalities: %v", res.ToString()) }),
	)

	return res
}

/* Reoder substitution in case of metavariable equalities. (X, META_1) => (META_1, X). Need to find association. */
func orderSubstForRetrieve(s Unif.Substitutions, M1, M2 AST.Meta) Unif.Substitutions {
	new_subst := Unif.MakeEmptySubstitution()
	for _, subst := range s {
		k, v := subst.Get()
		if !k.Equals(M1) && !k.Equals(M2) {
			if !v.IsMeta() {
				Glob.PrintError("OSFR", "Meta EQ/NEQ not found")
			} else {
				new_subst.Set(v.ToMeta(), k)
			}
		} else {
			new_subst.Set(k, v)
		}
	}
	Unif.EliminateMeta(&new_subst)
	Unif.Eliminate(&new_subst)
	return new_subst
}

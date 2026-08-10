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
* This file contains functions and types which describe the term's data structure
**/

package AST

import (
	"github.com/GoelandProver/Goeland/Glob"
	"github.com/GoelandProver/Goeland/Lib"
)

/* Term */
type Term interface {
	Lib.Comparable
	Lib.Stringable
	Lib.Copyable[Term]
	GetIndex() int
	GetName() string
	IsMeta() bool
	IsFun() bool
	ToMeta() Meta
	GetMetas() Lib.Set[Meta]
	// GetMetasOriginal reports the metavariables of the term as it was worded
	// before any substitution, so a metavariable that was replaced counts and
	// the term that replaced it does not. Skolemisation needs those: a symbol
	// built after a metavariable was instantiated must still list it among its
	// arguments, since it was free in the branch when the symbol was created.
	// It agrees with DeepOrigin: GetMetasOriginal(t) = DeepOrigin(t).GetMetas().
	GetMetasOriginal() Lib.Set[Meta]
	GetMetaList() Lib.List[Meta] // Metas appearing in the term ORDERED
	GetSubTerms() Lib.Set[Term]
	GetSymbols() Lib.Set[Id]
	ReplaceSubTermBy(original_term, new_term Term) Term
	SubstTy(old TyGenVar, new Ty) Term
	Less(any) bool
}

/*** Makers ***/
func MakeId(i int, s string) Id {
	return Id{i, s}
}

func MakeQuotedId(i int, s string) Id {
	return Id{i, "" + s + "'"}
}

func MakeVar(i int, s string) Var {
	return Var{i, s}
}

func MakeMeta(index, occurence int, s string, f int, ty Ty) Meta {
	return Meta{index, occurence, s, f, ty, nil}
}

func MakeFun(p Id, ty_args Lib.List[Ty], args Lib.List[Term], metas Lib.Set[Meta]) Fun {
	return Fun{p, ty_args, args, Lib.MkCache(metas, Fun.forceGetMetas), nil}
}

/*** Functions **/

func TermEquals(x, y Term) bool {
	return x.Equals(y)
}

func GetSymbol(tm Term) Lib.Option[Id] {
	switch t := tm.(type) {
	case Var, Meta:
		return Lib.MkNone[Id]()
	case Fun:
		return Lib.MkSome(t.GetID())
	case Id:
		return Lib.MkSome(tm)
	}

	debug(Lib.MkLazy(func() string {
		return tm.ToString()
	}))

	Glob.Anomaly(
		"term",
		"Found a term that was neither a bound variable nor a free variable nor a function",
	)
	return Lib.MkNone[Id]()
}

/*** Origin of a substituted term ***/

// Origin returns the term [t] replaced when a substitution was applied to it,
// or [t] itself when it replaced nothing.
//
// The proof search instantiates its formulas as it goes, so by the time a proof
// is reconstructed a formula may be worded with the substituted terms while the
// branch it belongs to was built with the original ones. Only the proof output
// needs the original wording; everywhere else a term is read as what it is now.
func Origin(t Term) Term {
	switch typed := t.(type) {
	case Fun:
		if typed.origin != nil {
			return Origin(typed.origin)
		}
	case Meta:
		if typed.origin != nil {
			return Origin(typed.origin)
		}
	}
	return t
}

// WithOrigin records that [t] replaced [original]. Substitutions compose, so an
// origin that already has one keeps pointing at the earliest wording.
func WithOrigin(t Term, original Term) Term {
	if original == nil || t.Equals(original) {
		return t
	}
	switch typed := t.(type) {
	case Fun:
		typed.origin = original
		return typed
	case Meta:
		typed.origin = original
		return typed
	}
	return t
}

// DeepOrigin rewrites [t] the way it was worded before any substitution was
// applied to it, recursively: a term that replaced nothing but whose arguments
// did still has to be rebuilt, otherwise the same skolem symbol ends up written
// with two different argument lists.
func DeepOrigin(t Term) Term {
	t = Origin(t)
	if fun, ok := t.(Fun); ok {
		return MakerFun(
			fun.GetID(),
			fun.GetTyArgs(),
			Lib.ListMap(fun.GetArgs(), DeepOrigin),
		)
	}
	return t
}


// GetMetasOriginalForm is GetMetasOriginal for a formula: the metavariables it
// had before any substitution was applied to it.
func GetMetasOriginalForm(f Form) Lib.Set[Meta] {
	if f == nil {
		return Lib.EmptySet[Meta]()
	}
	return DeepOriginForm(f).GetMetas()
}

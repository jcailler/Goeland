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
* This file provides a TableauxRocq output for Goeland's proofs.
**/

package tableauxrocq

import (
	"strings"

	"github.com/GoelandProver/Goeland/global"
	"github.com/GoelandProver/Goeland/search"
	. "github.com/GoelandProver/Goeland/types/basic-types"
	basictypes "github.com/GoelandProver/Goeland/types/basic-types"
	proof "github.com/GoelandProver/Goeland/visualization_proof"
)

var contextEnabled bool = false

var TableauxRocqOutputProofStruct = &search.OutputProofStruct{ProofOutput: MakeTableauxRocqOutput, Name: "TableauxRocq", Extension: ".v"}

type Rule int

// Rules
const (
	AX Rule = iota
	W
	NOT
	IMP
	AND
	OR
	EQU
	EX
	ALL
	NNOT
	NIMP
	NAND
	NOR
	NEQU
	NEX
	NALL
	R
	REWRITE
)

// ----------------------------------------------------------------------------
// Plugin initialisation and main function to call.

// Section: init
// Functions: MakeTableauxRocqOutput
// Main functions of the TableauxRocq module.
// TODO:
//	* Write the context for TFF problems

func MakeTableauxRocqOutput(prf []proof.ProofStruct, meta *basictypes.MetaList) string {
	if len(prf) == 0 {
		global.PrintError("TableauxRocq", "Nothing to output")
		return ""
	}

	// Transform tableaux's proof in GS3 proof
	return MakeTableauxRocqProof(prf, meta)
}

var MakeTableauxRocqProof = func(proof []proof.ProofStruct, meta *basictypes.MetaList) string {
	contextString := makeContextIfNeeded()
	proofString := makeTableauxRocqProofFromTableaux(proof)
	return contextString + "\n" + proofString
}

// Replace defined symbols by TableauxRocq's defined symbols.
func mapDefault(str string) string {
	return strings.ReplaceAll(strings.ReplaceAll(str, "$i", "goeland_U"), "$o", "Prop")
}

func termToTableauxRocq(t Term) string {
	switch t.(type) {
	case basictypes.Var:
		return "Term.Var \"" + t.GetName() + "\""
	case basictypes.Meta:
		return "Term.Free \"" + t.GetName() + "\""
	case basictypes.Fun:
		return "Term.const \"" + t.GetName() + "\""
	default:
		global.PrintError("TableauxRocq", "termToTableauRocq error TERM")
		return "TableauxRocqError"
	}
}

func termListToTableauxRocq(tl *TermList) string {
	str := "["
	for _, element := range tl.Slice() {
		str += termToTableauxRocq(element) + ", "
	}

	if tl.Len() > 0 {
		return str[:len(str)-2] + "]"
	} else {
		return "[]"
	}
}

func formToTableauxRocq(f Form) string {
	switch nf := f.(type) {
	case Pred:
		return "Form.Pred \"" + nf.GetID().GetName() + "\" (" + termListToTableauxRocq(nf.GetArgs()) + ")"
	case Top:
		return "Form.Top"
	case Bot:
		return "Form.Bot"
	case Not:
		return "Form.Neg (" + formToTableauxRocq(nf.GetForm()) + ")"
	case And:
		forms_aux := ""
		for _, element := range nf.GetChildFormulas().Slice() {
			forms_aux += "(" + formToTableauxRocq(element) + ") "
		}
		return "Form.And " + forms_aux[:len(forms_aux)-1]
	case Or:
		forms_aux := ""
		for _, element := range nf.GetChildFormulas().Slice() {
			forms_aux += "(" + formToTableauxRocq(element) + ") "
		}
		return "Form.Or " + forms_aux[:len(forms_aux)-1]
	case Imp:
		forms_aux := ""
		for _, element := range nf.GetChildFormulas().Slice() {
			forms_aux += "(" + formToTableauxRocq(element) + ") "
		}
		return "Form.Imp " + forms_aux[:len(forms_aux)-1]
	case Equ:
		forms_aux := ""
		for _, element := range nf.GetChildFormulas().Slice() {
			forms_aux += "(" + formToTableauxRocq(element) + ") "
		}
		return "Form.Equ " + forms_aux[:len(forms_aux)-1]
	case Ex:
		if len(nf.GetVarList()) != 1 {
			global.PrintError("TableauxRocq", "formToTableauxRocq error EXISTS")
			return "TableauxRocqError"
		}
		return "Form.Exists " + "\"" + nf.GetVarList()[0].GetName() + "\" " + "(" + formToTableauxRocq(nf.GetForm()) + ")"
	case All:
		if len(nf.GetVarList()) != 1 {
			global.PrintError("TableauxRocq", "formToTableauxRocq error ALL")
			return "TableauxRocqError"
		}
		return "Form.All " + "\"" + nf.GetVarList()[0].GetName() + "\" " + "(" + formToTableauxRocq(nf.GetForm()) + ")"
	default:
		global.PrintError("TableauxRocq", "formToTableauxRocq error DEFAULT")
		return "TableauxRocqError"
	}
}

func formListToTableauxRocq(fl *FormList) string {

	str := ""
	for _, element := range fl.Slice() {
		str += formToTableauxRocq(element) + ", "
	}

	if fl.Len() > 0 {
		return str[:len(str)-2]
	} else {
		return "[]"
	}
}

func proofStructRuleToTableauxRocqRules(rule string) Rule {
	mapping := map[string]Rule{
		"ALPHA_NOT_NOT":    NNOT,
		"ALPHA_NOT_OR":     NOR,
		"ALPHA_NOT_IMPLY":  NIMP,
		"ALPHA_AND":        AND,
		"BETA_NOT_AND":     NAND,
		"BETA_NOT_EQUIV":   NEQU,
		"BETA_OR":          OR,
		"BETA_IMPLY":       IMP,
		"BETA_EQUIV":       EQU,
		"GAMMA_NOT_EXISTS": NEX,
		"GAMMA_FORALL":     ALL,
		"DELTA_NOT_FORALL": NALL,
		"DELTA_EXISTS":     EX,
		"CLOSURE":          AX,
		"WEAKEN":           W,
		"Reintroduction":   R,
		"Rewrite":          REWRITE,
	}
	return mapping[rule]
}

func TableauxRocqRulesToString(rule Rule) string {
	mapping := map[Rule]string{
		NNOT:    "FOLTreeBuilder.neg_neg",
		NOR:     "FOLTreeBuilder.neg_or",
		NIMP:    "FOLTreeBuilder.neg_imp",
		AND:     "FOLTreeBuilder.and",
		NAND:    "FOLTreeBuilder.neg_and",
		NEQU:    "FOLTreeBuilder.neg_equ",
		OR:      "FOLTreeBuilder.or",
		IMP:     "FOLTreeBuilder.imp",
		EQU:     "FOLTreeBuilder.equ",
		NEX:     "FOLTreeBuilder.neg_ex",
		ALL:     "FOLTreeBuilder.all",
		NALL:    "FOLTreeBuilder.neg_all",
		EX:      "FOLTreeBuilder.ex",
		AX:      "FOLTreeBuilder.contra",
		W:       "FOLTreeBuilder.Error — Weakening",
		R:       "FOLTreeBuilder.Error — Reintroduction",
		REWRITE: "FOLTreeBuilder.Error – Rewrite",
	}
	return mapping[rule]
}

// Context flag utility function
func GetContextEnabled() bool {
	return contextEnabled
}

// Context flag utility function
func SetContextEnabled(ce bool) {
	contextEnabled = true
}

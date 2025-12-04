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
* This file provides TableauxRocq's output
**/

package tableauxrocq

import (
	"fmt"
	"strings"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Glob"
	"github.com/GoelandProver/Goeland/Lib"
	"github.com/GoelandProver/Goeland/Search"
	"github.com/GoelandProver/Goeland/Unif"
)

var TROutputProofStruct = &Search.OutputProofStruct{ProofOutput: MakeTableauxRocqOutput, Name: "TR", Extension: ".v"}

// ----------------------------------------------------------------------------
// Plugin initialisation and main function to call.

func MakeTableauxRocqOutput(prf Search.TableauxProof, meta Lib.List[AST.Meta], sub Unif.Substitutions) string {
	if len(prf) == 0 {
		Glob.PrintError("Rocq", "Nothing to output")
		return ""
	}

	// Setup TableauxRocq printer
	connectives := TableauxRocqPrinterConnectives()
	printer := AST.Printer{PrinterAction: TableauxRocqPrinterAction(), PrinterConnective: &connectives}
	AST.SetPrinter(printer)

	// Transform tableaux's proof in GS3 proof
	return MakeTableauxRocqProof(prf, meta, sub)
}


func TableauxRocqPrinterConnectives() AST.PrinterConnective {
	return AST.MkPrinterConnective(
		"TableauxRocqPrinterConnective",
		map[AST.Connective]string{
			AST.ConnAll: "forall",
			AST.ConnEx:  "exists",
			AST.ConnAnd: " /\\ ",
			AST.ConnOr:  " \\/ ",
			AST.ConnImp: "->",
			AST.ConnEqu: "<->",
			AST.ConnTop: "True",
			AST.ConnBot: "False",

			AST.ConnPi:  "forall",
			AST.ConnMap: "->",

			AST.SepVarsForm:   ", ",
			AST.SepTyArgs:     ", ",
			AST.SepArgsTyArgs: ", ",
			AST.SepTyVars:     " ",
			AST.SepVarTy:      "",

			AST.SurQuantStart: "",
			AST.SurQuantEnd:   "",
		},
	)
}

func TableauxRocqPrinterAction() AST.PrinterAction {
	connectives := TableauxRocqPrinterConnectives()

	sanitize_type := func(ty_str string) string {
		replace := map[string]string{
			"$i":     "goeland_U",
			"$o":     "Prop",
			"$tType": "Type",
			// FIXME: define a replacement for every defined stuff
		}
		for k, v := range replace {
			ty_str = strings.ReplaceAll(ty_str, k, v)
		}
		return ty_str
	}
	tr_action := AST.MkPrinterAction(
		AST.PrinterIdentity,
		func(i AST.Id) string { return i.GetName() },
		AST.PrinterIdentity2[int],
		func(metaName string, index int) string { return fmt.Sprintf("%s_%d", metaName, index) },
		sanitize_type,
		func(typed_var Lib.Pair[string, AST.Ty]) string {
			return fmt.Sprintf("(%s : %s)", typed_var.Fst, sanitize_type(typed_var.Snd.ToString()))
		},
		connectives.DefaultOnFunctionalArgs,
	)
	tr_action = tr_action.Compose(AST.SanitizerAction(connectives, []string{"@"}))
	return tr_action.Compose(AST.RemoveSuperfluousParenthesesAction(connectives))
}



var MakeTableauxRocqProof = func(prf Search.TableauxProof, meta Lib.List[AST.Meta], sub Unif.Substitutions) string {
	res := ""
	res += makeContext()

	axioms, conjecture := processMainFormula(prf.AppliedOn())

	res += makeAxioms(axioms)
	axioms.Append(AST.MakerNot(conjecture))

	res += makeContextConjectureBegin()
	res += makeConjecture(conjecture)
	res += makeContextConjectureEnd()

	res += makeContextSubstBegin()
	res += makeGlobalSubst(sub)
	res += makeContextSubstEnd()

	res += makeContextProofBegin(axioms)
	if axioms.Len() > 1 {
		res += makeProof(prf.Children().At(0), sub, axioms)
	} else {
		res += makeProof(prf, sub, axioms)
	}
	res += makeContextProofEnd()

	res += "\n\n"
	return res
}


/************ Term to TR ************/

func TermToTR(t AST.Term) string {
	switch tt := t.(type) {
		case AST.Meta:
			return  fmt.Sprintf("(EVar \"%v\")", tt.ToString())
		case AST.Var:
			return  fmt.Sprintf("(EVar \"%v\")", tt.ToString())
		case AST.Fun: 
			return fmt.Sprintf("(EFun \"%v\" [%v])", tt.GetName(), TermListToTR(tt.GetArgs()))
		default:
			Glob.PrintError("TableauxRocq", "Error in TermToTR")
			return ""
	}
}

func TermListToTR(tl Lib.List[AST.Term]) string {
	var res strings.Builder
	for i, t := range tl.GetSlice() {
		res.WriteString(TermToTR(t))
		if (i < tl.Len()-1) {
			res.WriteString(" ; ")
		}
	}
	return res.String()
}


/************ Formula to TR ************/

func FormToTR(f AST.Form) string {
	switch ft := f.(type) {
		case AST.Pred:
			return fmt.Sprintf("EPred \"%v\" [%v]", ft.GetID().ToString(), TermListToTR(ft.GetArgs()))
		case AST.Not:
			return fmt.Sprintf("ENeg (%v)", FormToTR(ft.GetChildFormulas().At(0)))
		case AST.And:
			return fmt.Sprintf("EAnd (%v) (%v)", FormToTR(ft.GetChildFormulas().At(0)), FormToTR(ft.GetChildFormulas().At(1)))
		case AST.Or:
			return fmt.Sprintf("EOr (%v) (%v)", FormToTR(ft.GetChildFormulas().At(0)), FormToTR(ft.GetChildFormulas().At(1)))
		case AST.Imp:
			return fmt.Sprintf("EImp (%v) (%v)", FormToTR(ft.GetF1()), FormToTR(ft.GetF2()))
		case AST.Equ:
			return fmt.Sprintf("EEqu (%v) (%v)", FormToTR(ft.GetF1()), FormToTR(ft.GetF2()))
		case AST.Ex: // extend E x, y, z -> ex x, ex y, ex z
				res:= ""
				for _, v := range ft.GetVarList().GetSlice() {
					res += fmt.Sprintf("EEx \"%v\" (", v.ToBoundVar().ToString() )
				}
				res += fmt.Sprintf("%v", FormToTR(ft.GetChildFormulas().At(0))) 
				return res + strings.Repeat(")", ft.GetVarList().Len())
		case AST.All: //extend
				res:= ""
				for _, v := range ft.GetVarList().GetSlice() {
					res += res + fmt.Sprintf("EAll \"%v\" (", v.ToBoundVar().ToString())
				}
			res += fmt.Sprintf("%v", FormToTR(ft.GetChildFormulas().At(0))) 
				return res + strings.Repeat(")", ft.GetVarList().Len())
	}
	Glob.Anomaly("FormToTR", "Formula type unknown")
	return ""
}

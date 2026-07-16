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
* This file provides poulet's context for a proof.
**/

package poulet

import (
	"fmt"

	"github.com/GoelandProver/Goeland/Glob"
	"github.com/GoelandProver/Goeland/Lib"
	"github.com/GoelandProver/Goeland/AST"
)

func makeContextAxiomBegin(i int) string {
	return fmt.Sprintf("fof(a%v, axiom, ", i)
}

func makeContextAxiomEnd() string {
	return ").\n"
}

func makeContextConjectureBegin() string {
	return "fof(c, conjecture, "
}

func makeContextConjectureEnd() string {
	return ").\n\n"
}

func makeContextProofBegin(axioms Lib.List[AST.Form]) string {
	resultingString := "Theorem hasTableau_T_Proof :\n"
	skolemization := "OuterSkolemization"
	if (Glob.IsInnerSko()) {
		skolemization = "InnerSkolemization"
	}

	axioms_string := ""
	for i := 0; i<axioms.Len()-1; i++ {
		axioms_string += fmt.Sprintf(" [[ Axiom%v ]] ; ", i)
	}

	resultingString += fmt.Sprintf("	hasTableau %v [ %v Neg (translate_EForm T) ] subst.\n", skolemization, axioms_string)
	resultingString += "Proof.\n"
	return resultingString
}

func makeContextProofEnd() string {
	return "tableaux T_Proof.\nQed."
}

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
* This file provides TableauxRocq's context for a proof.
**/

package tableauxrocq

var contextEnabled bool = false

func makeContext() string {
	if !GetContextEnabled() {
		return ""
	}
	resultingString := "From Tableaux Require Import FOL.Everything.\n"
	resultingString += "From Stdlib Require Import Strings.String.\n"
	resultingString += "Open Scope string_scope.\n"
	resultingString += "Import FOL.\n\n"
	return resultingString
}

func makeContextTableauBegin() string {
	return "Definition T :=\n"
}

func makeContextTableauEnd() string {
	return ").\n\n"
}

func makeContextSubstBegin() string {
	return "#[program] Definition σ : Substitution.t :=\n"
}

func makeContextSubstEnd() string {
	return "Next Obligation. fol_decide. Defined.\n\n"
}

func makeContextLemmaBegin() string {
	resultingString := "Lemma T_is_fol_tableau :\n"
	resultingString += "	is_fol_tableau T σ.\n"
	resultingString += "Proof.\n"
	return resultingString
}

func makeContextLemmaEnd() string {
	return "Qed."
}

// Context flag utility function
func GetContextEnabled() bool {
	return contextEnabled
}

// Context flag utility function
func SetContextEnabled(ce bool) {
	contextEnabled = true
}

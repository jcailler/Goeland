package cc

import (
	"fmt"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Mods/equality/eqStruct"
	"github.com/GoelandProver/Goeland/Unif"
)

// CongruenceClosure with union-find
type CongruenceClosure struct {
	parent map[int]AST.Term
	rank   map[int]int
	sig    map[string]AST.Term
}

func NewCC() *CongruenceClosure {
	return &CongruenceClosure{
		parent: make(map[int]AST.Term),
		rank:   make(map[int]int),
		sig:    make(map[string]AST.Term),
	}
}

// Find canonical representative
func (cc *CongruenceClosure) find(t AST.Term) AST.Term {
	id := t.GetIndex()
	p, ok := cc.parent[id]
	if !ok {
		cc.parent[id] = t
		cc.rank[id] = 0
		return t
	}
	if !p.Equals(t) {
		cc.parent[id] = cc.find(p)
	}
	return cc.parent[id]
}

// Union terms; handle meta-variable substitutions
func (cc *CongruenceClosure) union(a, b AST.Term) bool {
	ra := cc.find(a)
	rb := cc.find(b)
	if ra.Equals(rb) {
		return true
	}

	if ra.IsMeta() {
		return cc.assignMeta(ra.ToMeta(), rb)
	}
	if rb.IsMeta() {
		return cc.assignMeta(rb.ToMeta(), ra)
	}

	fs, okS := ra.(AST.Fun)
	ft, okT := rb.(AST.Fun)
	if okS && okT && fs.GetID().Equals(ft.GetID()) && fs.GetArgs().Len() == ft.GetArgs().Len() {
		for i := 0; i < fs.GetArgs().Len(); i++ {
			if !cc.union(fs.GetArgs().At(i), ft.GetArgs().At(i)) {
				return false
			}
		}
		cc.mergeUnion(ra, rb)
		return true
	}

	// Distinct constants/functions cannot unify
	return false
}

func (cc *CongruenceClosure) mergeUnion(a, b AST.Term) {
	ra := cc.find(a)
	rb := cc.find(b)
	if ra.Equals(rb) {
		return
	}

	rankA := cc.rank[ra.GetIndex()]
	rankB := cc.rank[rb.GetIndex()]

	if rankA < rankB {
		cc.parent[ra.GetIndex()] = rb
	} else if rankA > rankB {
		cc.parent[rb.GetIndex()] = ra
	} else {
		cc.parent[rb.GetIndex()] = ra
		cc.rank[ra.GetIndex()]++
	}
}

// Assign metavariable
func (cc *CongruenceClosure) assignMeta(m AST.Meta, t AST.Term) bool {
	if !Unif.OccurCheckValid(m, t) {
		return false
	}
	cc.parent[m.GetIndex()] = t
	return true
}

// Register a term and its subterms
func (cc *CongruenceClosure) addTerm(t AST.Term) {
	cc.find(t)
	if f, ok := t.(AST.Fun); ok {
		for _, arg := range f.GetArgs().GetSlice() {
			cc.addTerm(arg)
		}
		cc.sig[cc.keyFor(f)] = f
	}
}

// Generate a key for congruence
func (cc *CongruenceClosure) keyFor(t AST.Term) string {
	switch ft := t.(type) {
	case AST.Fun:
		key := ft.GetP().GetName() + "("
		for i, arg := range ft.GetArgs().GetSlice() {
			key += fmt.Sprintf("%d", cc.find(arg).GetIndex())
			if i < ft.GetArgs().Len()-1 {
				key += ","
			}
		}
		return key + ")"
	default:
		return t.ToString()
	}
}

// Extract metavariable substitutions from eqStruct.TermPairs
func deriveMetaSubst(cc *CongruenceClosure, eqs []eqStruct.TermPair) Unif.Substitutions {
	subst := Unif.MakeEmptySubstitution()

	for _, eq := range eqs {
		a := cc.find(eq.GetT1())
		b := cc.find(eq.GetT2())

		if a.IsMeta() && !b.IsMeta() {
			subst.Set(a.ToMeta(), b)
		} else if b.IsMeta() && !a.IsMeta() {
			subst.Set(b.ToMeta(), a)
		} else if a.IsMeta() && b.IsMeta() {
			subst.Set(a.ToMeta(), b)
		}
	}
	return subst
}

// Debug dump
func (cc *CongruenceClosure) Dump() {
	fmt.Println("=== Congruence Closure ===")
	for t, p := range cc.parent {
		fmt.Printf("%s -> %s\n", t, p.ToString())
	}
}

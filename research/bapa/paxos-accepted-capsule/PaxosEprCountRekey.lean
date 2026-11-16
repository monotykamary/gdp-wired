import CountMachine

/-! Count-preserving pair-index representation, independent of the physical-map
re-keying. The bound and body keep their exact meaning under simultaneous pair
parameter substitution. No finite bound or free count-map assumption is added. -/
namespace Bapa.PaxosEprCountRekey
open Kern

-- The old pair parameters are interpreted as projections of one tuple index.
def decode (d : CDecl) : List (Nat × E) :=
  [(d.j, .proj 0 (.var d.j)), (d.lo, .proj 1 (.var d.j))]

def unary (d : CDecl) : CDecl :=
  {d with
    lo := d.j
    base := 0
    below := substE (decode d) d.below
    body := substE (decode d) d.body}

def pairCount (d : CDecl) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (a b : Nat) : Nat :=
  sumBelow (fun k => evalE (upd (upd (upd ρ d.j a) d.lo b) d.key k) M d.body)
    (evalE (upd (upd ρ d.j a) d.lo b) M d.below)

private theorem decoded (d : CDecl) (hj : d.j ≠ d.lo)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (a b : Nat) :
    applyS (decode d) (atJ (unary d) ρ (cpair a b)) M = upd (upd ρ d.j a) d.lo b := by
  funext i
  by_cases hi : i = d.j
  · subst i
    simp [applyS, decode, assoc, lookup, atJ, unary, upd, evalE, pickP, hj, Ne.symm hj]
  · by_cases hlo : i = d.lo
    · subst i
      simp [applyS, decode, assoc, lookup, atJ, unary, upd, evalE, pickP, hj, Ne.symm hj]
    · simp [applyS, decode, assoc, lookup, atJ, unary, upd, evalE, pickP, hi, Ne.symm hi, hlo, Ne.symm hlo]

private theorem decoded_key (d : CDecl) (hj : d.j ≠ d.lo)
    (hkj : d.key ≠ d.j) (hkl : d.key ≠ d.lo)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (a b k : Nat) :
    applyS (decode d) (upd (atJ (unary d) ρ (cpair a b)) d.key k) M =
      upd (upd (upd ρ d.j a) d.lo b) d.key k := by
  funext i
  by_cases hi : i = d.j
  · subst i
    simp [applyS, decode, assoc, lookup, atJ, unary, upd, evalE, pickP, hj, Ne.symm hj, hkj, Ne.symm hkj]
  · by_cases hlo : i = d.lo
    · subst i
      simp [applyS, decode, assoc, lookup, atJ, unary, upd, evalE, pickP, hj, Ne.symm hj, hkj, Ne.symm hkj, hkl, Ne.symm hkl]
    · simp [applyS, decode, assoc, lookup, atJ, unary, upd, evalE, pickP, hi, Ne.symm hi, hlo, Ne.symm hlo]

/-- All pair coordinates and all original count bounds; no restriction to 64. -/
theorem tuple_count (d : CDecl) (hj : d.j ≠ d.lo)
    (hkj : d.key ≠ d.j) (hkl : d.key ≠ d.lo)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (a b : Nat) :
    cntOf (unary d) ρ M (cpair a b) = pairCount d ρ M a b := by
  have hb : evalE (atJ (unary d) ρ (cpair a b)) M (substE (decode d) d.below) =
      evalE (upd (upd ρ d.j a) d.lo b) M d.below := by
    rw [subst_evalE, decoded d hj]
  have he : ∀ k, evalE (upd (atJ (unary d) ρ (cpair a b)) d.key k) M (substE (decode d) d.body) =
      evalE (upd (upd (upd ρ d.j a) d.lo b) d.key k) M d.body := by
    intro k
    rw [subst_evalE, decoded_key d hj hkj hkl]
  change sumBelow (fun k => evalE (upd (atJ (unary d) ρ (cpair a b)) d.key k) M (substE (decode d) d.body))
    (evalE (atJ (unary d) ρ (cpair a b)) M (substE (decode d) d.below)) = _
  simp only [he, hb, pairCount]

/-- Compatibility with the old index where that radix index was injective. -/
theorem retained_count (d : CDecl) (hd : d.base = 64)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (a b : Nat) (hb : b < 64) :
    cntOf d ρ M (64*a+b) = pairCount d ρ M a b := by
  have hdiv : (64*a+b) / d.base = a := by rw [hd]; omega
  have hmod : (64*a+b) % d.base = b := by rw [hd]; omega
  simp only [cntOf, atJ, hdiv, hmod, pairCount]

#print axioms tuple_count
#print axioms retained_count
end Bapa.PaxosEprCountRekey

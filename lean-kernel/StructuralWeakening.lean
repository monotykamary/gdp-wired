import SourceInclusion
import CertificateBoundErasure

/-! Finite syntax certificates, not a decision procedure for semantic implication.
The generator proposes constructor trees; Lean checks every atom by definitional
identity. Neither arithmetic validity nor arbitrary propositional validity is
inferred. Quantifier keys are checked separately by SourceLawImplication. -/
namespace Bapa.StructuralWeakening
open Kern

inductive Subsumes : C → C → Prop where
  | refl (p : C) : Subsumes p p
  | top (p : C) : Subsumes p trueC
  | bot (p : C) : Subsumes (.lt (.const 0) (.const 0)) p
  | neg {p q} : Subsumes q p → Subsumes (.not p) (.not q)
  | orLeft {p q r} : Subsumes p q → Subsumes p (.or q r)
  | orRight {p q r} : Subsumes p r → Subsumes p (.or q r)
  | orElim {p q r} : Subsumes p r → Subsumes q r → Subsumes (.or p q) r
  | andLeft {p q r} : Subsumes p r → Subsumes (.and p q) r
  | andRight {p q r} : Subsumes q r → Subsumes (.and p q) r
  | andIntro {p q r} : Subsumes p q → Subsumes p r → Subsumes p (.and q r)

theorem sound {p q : C} (h : Subsumes p q) (ρ M) :
    evalC ρ M p = true → evalC ρ M q = true := by
  induction h with
  | refl => exact id
  | top => intro _; rfl
  | bot => intro h; simp [evalC, evalE] at h
  | @neg p q _ ih =>
      intro hn
      change (!evalC ρ M q) = true
      cases hq : evalC ρ M q with
      | false => rfl
      | true =>
          have hp := ih hq
          change (!evalC ρ M p) = true at hn
          rw [hp] at hn
          cases hn
  | orLeft _ ih => intro h; simp only [evalC, Bool.or_eq_true]; exact Or.inl (ih h)
  | orRight _ ih => intro h; simp only [evalC, Bool.or_eq_true]; exact Or.inr (ih h)
  | orElim _ _ ih₁ ih₂ =>
      intro h
      simp only [evalC, Bool.or_eq_true] at h
      exact h.elim ih₁ ih₂
  | andLeft _ ih =>
      intro h
      simp only [evalC, Bool.and_eq_true] at h
      exact ih h.1
  | andRight _ ih =>
      intro h
      simp only [evalC, Bool.and_eq_true] at h
      exact ih h.2
  | andIntro _ _ ih₁ ih₂ =>
      intro h
      simp only [evalC, Bool.and_eq_true]
      exact ⟨ih₁ h, ih₂ h⟩

theorem law {strong weak : SEntry}
    (hk : strong.law.key = weak.law.key) (hks : strong.keys2 = weak.keys2)
    (h : Subsumes strong.law.holds weak.law.holds) : SourceLawImplication strong weak :=
  sourceLawImplication_of_pointwise strong weak hk hks (sound h)

/-- Extend the supplied candidate transform to cut-carrying entries. The cut
lists are retained verbatim, never silently dropped. The complete F checker
must accept them against the transformed goals before soundness is available. -/
def countedEntryF (bound : Nat) (e : CEntryF) : CEntryF :=
  { e with
    e := CertificateBoundErasure.entry bound e.e
    start := CertificateBoundErasure.countedCertificate bound e.start
    step := CertificateBoundErasure.countedCertificate bound e.step }

#print axioms sound
#print axioms law
end Bapa.StructuralWeakening

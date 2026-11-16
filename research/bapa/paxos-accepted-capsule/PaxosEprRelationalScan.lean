import PaxosEprScanSimulation
namespace Bapa.PaxosEprScanSimulation
open Bapa.FiniteSimulation

/-- Relational encoding deliberately forgets input/flag/count scratch cells.
A single canonical full-state encoding would incorrectly fix those cells. -/
theorem complete_counted_scan_rel {Store : Type} (size : Nat)
    (target : Kern.SMachine) (ds : List Kern.CDecl)
    (s : Store) (q : Nat → Bool) (r mr v : Nat)
    (commit : Store → Nat → Nat → Store)
    (R : Phase Store → KState → Prop)
    (start : ∀ x, R (idle s) x → ∃ y,
      CSteps target ds x y ∧ R (scanning s q r mr v 0) y)
    (next : ∀ i x, i+1 < size → R (scanning s q r mr v i) x → ∃ y,
      CSteps target ds x y ∧ R (scanning s q r mr v (i+1)) y)
    (finish : ∀ i x, i+1 = size → R (scanning s q r mr v i) x → ∃ y,
      CSteps target ds x y ∧ R (idle (commit s r v)) y)
    (hsize : 0 < size) {x} (hx : R (idle s) x) :
    ∃ y, CSteps target ds x y ∧ R (idle (commit s r v)) y := by
  have rest : ∀ remaining i x, i+remaining+1 = size →
      R (scanning s q r mr v i) x → ∃ y,
      CSteps target ds x y ∧ R (idle (commit s r v)) y := by
    intro remaining
    induction remaining with
    | zero =>
      intro i x heq hx
      exact finish i x (by omega) hx
    | succ remaining ih =>
      intro i x heq hx
      obtain ⟨y,hy,hRy⟩ := next i x (by omega) hx
      obtain ⟨z,hz,hRz⟩ := ih (i+1) y (by omega) hRy
      exact ⟨z,hy.trans hz,hRz⟩
  obtain ⟨y,hy,hRy⟩ := start x hx
  obtain ⟨z,hz,hRz⟩ := rest (size-1) 0 y (by omega) hRy
  exact ⟨z,hy.trans hz,hRz⟩

#print axioms complete_counted_scan_rel
end Bapa.PaxosEprScanSimulation

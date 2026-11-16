import FiniteSimulation

/-! A finite scan scheduling lemma. `row` and `commit` are semantic operations
which a client must connect to its actual machine; this module alone is NOT an
instantiation for the emitted Paxos source or producer. -/
namespace Bapa.PaxosEprScanSimulation
open Bapa.FiniteSimulation

structure Phase (Store : Type) where
  store : Store
  busy : Bool
  cnt : Nat
  pr : Nat
  pmaxr : Nat
  pv : Nat
  qs : Nat → Bool

def idle {Store : Type} (s : Store) : Phase Store :=
  ⟨s,false,0,0,0,0,fun _ => false⟩

def scanning {Store : Type} (s : Store) (q : Nat → Bool) (r mr v i : Nat) : Phase Store :=
  ⟨s,true,i,r,mr,v,q⟩

inductive ScanStep {Store : Type} (size : Nat)
    (row : Store → Nat → Nat → Nat → Prop)
    (commit : Store → Nat → Nat → Store) : Phase Store → Phase Store → Prop where
  | propose (s q r mr v) : ScanStep size row commit (idle s) (scanning s q r mr v 0)
  | check (s q r mr v i) : i+1 < size → (q i = true → row s i r mr) →
      ScanStep size row commit (scanning s q r mr v i) (scanning s q r mr v (i+1))
  | finish (s q r mr v i) : i+1 = size → (q i = true → row s i r mr) →
      ScanStep size row commit (scanning s q r mr v i) (idle (commit s r v))
  | reject (s q r mr v i) : i < size → q i = true → ¬ row s i r mr →
      ScanStep size row commit (scanning s q r mr v i) (idle s)

/-- Universal row admission gives a finite sequence of all scan checks. Every
interior node preserves the old store; only the last node performs commit. -/
theorem complete_scan {Store : Type} (size : Nat)
    (row : Store → Nat → Nat → Nat → Prop) (commit : Store → Nat → Nat → Store)
    (s : Store) (q : Nat → Bool) (r mr v : Nat)
    (hsize : 0 < size) (allRows : ∀ i, i < size → q i = true → row s i r mr) :
    Steps (ScanStep size row commit) (idle s) (idle (commit s r v)) := by
  have rest : ∀ remaining i, i + remaining + 1 = size →
      Steps (ScanStep size row commit) (scanning s q r mr v i) (idle (commit s r v)) := by
    intro remaining
    induction remaining with
    | zero =>
      intro i heq
      exact .next (.refl _) (.finish s q r mr v i (by omega) (allRows i (by omega)))
    | succ remaining ih =>
      intro i heq
      have first : Steps (ScanStep size row commit) (scanning s q r mr v i)
          (scanning s q r mr v (i+1)) :=
        .next (.refl _) (.check s q r mr v i (by omega) (allRows i (by omega)))
      exact first.trans (ih (i+1) (by omega))
  exact (Steps.next (Steps.refl _) (ScanStep.propose s q r mr v)).trans
    (rest (size-1) 0 (by omega))

/-- A client maps every abstract scan edge to one or more real counted steps.
This lifts the finite scheduling proof without assuming the real target is
already reachable at the final phase boundary. -/
theorem Steps.map {α β : Type} {R : α → α → Prop} {T : β → β → Prop}
    (encode : α → β) (edge : ∀ x y, R x y → Steps T (encode x) (encode y))
    {x y} (h : Steps R x y) : Steps T (encode x) (encode y) := by
  induction h with
  | refl => exact .refl _
  | next _ hstep ih => exact ih.trans (edge _ _ hstep)

theorem complete_counted_scan {Store : Type} (size : Nat)
    (row : Store → Nat → Nat → Nat → Prop) (commit : Store → Nat → Nat → Store)
    (target : Kern.SMachine) (ds : List Kern.CDecl) (encode : Phase Store → KState)
    (edges : ∀ x y, ScanStep size row commit x y →
      CSteps target ds (encode x) (encode y))
    (s : Store) (q : Nat → Bool) (r mr v : Nat)
    (hsize : 0 < size) (allRows : ∀ i, i < size → q i = true → row s i r mr) :
    CSteps target ds (encode (idle s)) (encode (idle (commit s r v))) :=
  Steps.map encode edges (complete_scan size row commit s q r mr v hsize allRows)

#print axioms complete_scan
#print axioms complete_counted_scan
end Bapa.PaxosEprScanSimulation

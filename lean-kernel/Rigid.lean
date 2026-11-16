import Sets

/-!
Fixed interpretations already exist in SMachine: a map absent from maps0 is
arbitrary initially, and factsOk forbids a fact from reading a map that a step
writes or a request carries. No new certificate constructor is introduced here.
The new bridge removes the auxiliary Skolem function from a bounded source axiom.
-/
namespace Kern.Rigid

/-- Generic two-universal, one-existential finite axiom lowering. The result is
bounded only when both arguments are in their declared sorts. -/
theorem choice2_iff (sizeA sizeB sizeW : Nat) (P : Nat → Nat → Nat → Prop) :
    (∀ a b, a < sizeA → b < sizeB → ∃ w, w < sizeW ∧ P a b w) ↔
    ∃ choose : Nat → Nat → Nat, ∀ a b, a < sizeA → b < sizeB →
      choose a b < sizeW ∧ P a b (choose a b) := by
  classical
  constructor
  · intro h
    let choose := fun a b =>
      if hab : a < sizeA ∧ b < sizeB then Classical.choose (h a b hab.1 hab.2) else 0
    refine ⟨choose, ?_⟩
    intro a b ha hb
    simpa [choose, ha, hb] using Classical.choose_spec (h a b ha hb)
  · rintro ⟨choose, h⟩ a b ha hb
    exact ⟨choose a b, h a b ha hb⟩

theorem discharge_choice2 (sizeA sizeB sizeW : Nat) (P : Nat → Nat → Nat → Prop)
    (claim : Prop)
    (checked : ∀ choose : Nat → Nat → Nat,
      (∀ a b, a < sizeA → b < sizeB → choose a b < sizeW ∧ P a b (choose a b)) → claim)
    (source : ∀ a b, a < sizeA → b < sizeB → ∃ w, w < sizeW ∧ P a b w) : claim := by
  obtain ⟨choose, hc⟩ := (choice2_iff sizeA sizeB sizeW P).mp source
  exact checked choose hc

#print axioms choice2_iff
#print axioms discharge_choice2

/-- The original quorum axiom, over finite sorts with no positivity premise. -/
def Intersects {nodes quorums : Nat} (member : Fin nodes → Fin quorums → Prop) : Prop :=
  ∀ q₁ q₂, ∃ n, member n q₁ ∧ member n q₂

/-- A supplied auxiliary function witnesses exactly the original axiom. -/
def Witnesses {nodes quorums : Nat} (member : Fin nodes → Fin quorums → Prop)
    (meet : Fin quorums → Fin quorums → Fin nodes) : Prop :=
  ∀ q₁ q₂, member (meet q₁ q₂) q₁ ∧ member (meet q₁ q₂) q₂

/-- No inhabitance assumption is added: empty argument sorts remain empty. -/
theorem finite_choice_iff {nodes quorums : Nat} (member : Fin nodes → Fin quorums → Prop) :
    Intersects member ↔ ∃ meet, Witnesses member meet := by
  classical
  constructor
  · intro h
    exact ⟨fun q₁ q₂ => Classical.choose (h q₁ q₂), fun q₁ q₂ => Classical.choose_spec (h q₁ q₂)⟩
  · rintro ⟨meet, h⟩ q₁ q₂
    exact ⟨meet q₁ q₂, h q₁ q₂⟩

/-- The exact bounded-Nat source formula; outside-domain data is irrelevant. -/
def BoundedIntersects (nodes quorums : Nat) (member : Nat → Nat → Prop) : Prop :=
  ∀ q₁ q₂, q₁ < quorums → q₂ < quorums → ∃ n, n < nodes ∧ member n q₁ ∧ member n q₂

/-- The lowered facts, including the result bound, at every valid argument pair. -/
def BoundedWitnesses (nodes quorums : Nat) (member : Nat → Nat → Prop)
    (meet : Nat → Nat → Nat) : Prop :=
  ∀ q₁ q₂, q₁ < quorums → q₂ < quorums →
    meet q₁ q₂ < nodes ∧ member (meet q₁ q₂) q₁ ∧ member (meet q₁ q₂) q₂

/-- A total natural-valued auxiliary suffices, even if a declared sort is empty. -/
theorem bounded_choice_iff (nodes quorums : Nat) (member : Nat → Nat → Prop) :
    BoundedIntersects nodes quorums member ↔ ∃ meet, BoundedWitnesses nodes quorums member meet := by
  classical
  constructor
  · intro h
    let meet := fun q₁ q₂ =>
      if hq : q₁ < quorums ∧ q₂ < quorums then Classical.choose (h q₁ q₂ hq.1 hq.2) else 0
    refine ⟨meet, ?_⟩
    intro q₁ q₂ h₁ h₂
    simpa [meet, h₁, h₂] using Classical.choose_spec (h q₁ q₂ h₁ h₂)
  · rintro ⟨meet, h⟩ q₁ q₂ h₁ h₂
    exact ⟨meet q₁ q₂, h q₁ q₂ h₁ h₂⟩

/-- A theorem not mentioning the fresh auxiliary can be transported back to the
original source premise. This is the interface consumed by the exporter. -/
theorem discharge_skolem (nodes quorums : Nat) (member : Nat → Nat → Prop) (claim : Prop)
    (prove : ∀ meet, BoundedWitnesses nodes quorums member meet → claim)
    (source : BoundedIntersects nodes quorums member) : claim := by
  obtain ⟨meet, hm⟩ := (bounded_choice_iff nodes quorums member).mp source
  exact prove meet hm

/-- Minimal no-helper, no-existential claim for the first end-to-end example. -/
theorem quorum_nonempty_implies_node_nonempty (nodes quorums : Nat) (member : Nat → Nat → Prop)
    (source : BoundedIntersects nodes quorums member) : quorums > 0 → nodes > 0 := by
  intro hq
  obtain ⟨n, hn, _⟩ := source 0 0 hq hq
  omega

/-- A rigid map absent from every write really is preserved by the existing
point-update semantics; this is not a new state transition rule. -/
theorem writeMaps_fixed (writes : List (Nat × E × E)) (W : Nat → Nat)
    (M : Nat → Nat → Nat) (symbol : Nat)
    (absent : lookup (fun w => w.1 == symbol) writes = none) :
    writeMaps writes W M symbol = M symbol := by
  funext key
  simp [writeMaps, absent]

/-- Existing start semantics does not force an undeclared rigid map to zero. -/
theorem startMaps_unconstrained (m : MMachine) (M R : Nat → Nat → Nat) (symbol : Nat)
    (absent : ∀ p ∈ m.maps0, p.1 ≠ symbol) (h : StartMaps m M) :
    StartMaps m (fun mp => if mp = symbol then R mp else M mp) := by
  intro p hp key
  simpa [absent p hp] using h p hp key

#print axioms finite_choice_iff
#print axioms bounded_choice_iff
#print axioms discharge_skolem
#print axioms quorum_nonempty_implies_node_nonempty
#print axioms writeMaps_fixed
#print axioms startMaps_unconstrained
end Kern.Rigid

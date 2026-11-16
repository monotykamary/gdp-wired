import Rigid

/-!
Source semantics for ivybench ex/ivy/naive_consensus.ivy, blob
798410c0fd8147cdb80286e2cf36ca316c955c66. These are the three source
relations and actions, not the majority/counting suite port. The three
inductive helpers are GIVEN (the source lists them as commented invariants).
-/
namespace Kern.Rigid.Naive

structure State (nodes quorums values : Nat) where
  vote : Fin nodes → Fin values → Prop
  decide : Fin quorums → Fin values → Prop
  decision : Fin values → Prop

def initial (nodes quorums values : Nat) : State nodes quorums values :=
  ⟨fun _ _ => False, fun _ _ => False, fun _ => False⟩

def castVote (s : State nodes quorums values) (n : Fin nodes) (v : Fin values) : State nodes quorums values :=
  {s with vote := fun n' v' => s.vote n' v' ∨ (n' = n ∧ v' = v)}

def collectVotes (s : State nodes quorums values) (q : Fin quorums) (v : Fin values) : State nodes quorums values :=
  {s with decide := fun q' v' => s.decide q' v' ∨ (q' = q ∧ v' = v)}

def learnValue (s : State nodes quorums values) (v : Fin values) : State nodes quorums values :=
  {s with decision := fun v' => s.decision v' ∨ v' = v}

inductive Step (member : Fin nodes → Fin quorums → Prop) :
    State nodes quorums values → State nodes quorums values → Prop
  | cast (s) (n : Fin nodes) (v : Fin values) (guard : ∀ w, ¬s.vote n w) :
      Step member s (castVote s n v)
  | collect (s) (q : Fin quorums) (v : Fin values) (guard : ∀ n, member n q → s.vote n v) :
      Step member s (collectVotes s q v)
  | learn (s) (q : Fin quorums) (v : Fin values) (guard : s.decide q v) :
      Step member s (learnValue s v)

inductive Reach (member : Fin nodes → Fin quorums → Prop) : State nodes quorums values → Prop
  | init : Reach member (initial nodes quorums values)
  | step {s t} : Reach member s → Step member s t → Reach member t

structure Invariants (member : Fin nodes → Fin quorums → Prop) (s : State nodes quorums values) : Prop where
  uniqueVote : ∀ n v₁ v₂, s.vote n v₁ → s.vote n v₂ → v₁ = v₂
  certified : ∀ q v, s.decide q v → ∀ n, member n q → s.vote n v
  learned : ∀ v, s.decision v → ∃ q, s.decide q v

theorem initial_invariants (member : Fin nodes → Fin quorums → Prop) :
    Invariants member (initial nodes quorums values) := by
  constructor
  · intro _ _ _ h; exact False.elim h
  · intro _ _ h; exact False.elim h
  · intro _ h; exact False.elim h

theorem step_invariants (member : Fin nodes → Fin quorums → Prop)
    {s t : State nodes quorums values} (hs : Invariants member s) (step : Step member s t) : Invariants member t := by
  cases step with
  | cast n v guard =>
    constructor
    · intro n' v₁ v₂ h₁ h₂
      change (s.vote n' v₁ ∨ (n' = n ∧ v₁ = v)) at h₁
      change (s.vote n' v₂ ∨ (n' = n ∧ v₂ = v)) at h₂
      rcases h₁ with h₁ | ⟨rfl, rfl⟩
      · rcases h₂ with h₂ | ⟨rfl, rfl⟩
        · exact hs.uniqueVote _ _ _ h₁ h₂
        · exact False.elim (guard _ h₁)
      · rcases h₂ with h₂ | ⟨_, rfl⟩
        · exact False.elim (guard _ h₂)
        · rfl
    · intro q w hq n' hn
      exact Or.inl (hs.certified q w hq n' hn)
    · intro w hw
      exact hs.learned w hw
  | collect q v guard =>
    constructor
    · exact hs.uniqueVote
    · intro q' w hq n hn
      change (s.decide q' w ∨ (q' = q ∧ w = v)) at hq
      rcases hq with hq | ⟨rfl, rfl⟩
      · exact hs.certified q' w hq n hn
      · exact guard n hn
    · intro w hw
      obtain ⟨q', hq⟩ := hs.learned w hw
      exact ⟨q', Or.inl hq⟩
  | learn q v guard =>
    constructor
    · exact hs.uniqueVote
    · exact hs.certified
    · intro w hw
      change (s.decision w ∨ w = v) at hw
      rcases hw with hw | rfl
      · exact hs.learned w hw
      · exact ⟨q, guard⟩

theorem reach_invariants (member : Fin nodes → Fin quorums → Prop)
    {s : State nodes quorums values} (h : Reach member s) : Invariants member s := by
  induction h with
  | init => exact initial_invariants member
  | step _ step ih => exact step_invariants member ih step

/-- Original safety, at all symbolic finite sizes and under the original axiom.
The rigid interpretation is fixed for the entire Reach derivation. -/
theorem original_safety (member : Fin nodes → Fin quorums → Prop)
    {s : State nodes quorums values} (intersection : Kern.Rigid.Intersects member) (h : Reach member s)
    (v₁ v₂ : Fin values) (h₁ : s.decision v₁) (h₂ : s.decision v₂) : v₁ = v₂ := by
  have inv := reach_invariants member h
  obtain ⟨q₁, hq₁⟩ := inv.learned v₁ h₁
  obtain ⟨q₂, hq₂⟩ := inv.learned v₂ h₂
  obtain ⟨n, hn₁, hn₂⟩ := intersection q₁ q₂
  exact inv.uniqueVote n v₁ v₂ (inv.certified q₁ v₁ hq₁ n hn₁) (inv.certified q₂ v₂ hq₂ n hn₂)

#print axioms initial_invariants
#print axioms step_invariants
#print axioms reach_invariants
#print axioms original_safety
end Kern.Rigid.Naive

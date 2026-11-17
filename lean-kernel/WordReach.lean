import Sets
import WordDivision

/-! Runs with concrete immutable reserved word maps. These runs do not broaden
`Kern.SReach`: a start uses a concrete overlay, and every transition is exactly
the source machine's transition, including arbitrary carried maps. -/
namespace Kern.WordReach

/-- Pointwise, at every key of every reserved map, not just at a proof's reads. -/
def WordInterpret (reserved : List Nat) (value M : Nat → Nat → Nat) : Prop :=
  ∀ mp ∈ reserved, ∀ key, M mp key = value mp key

/-- Right-biased concrete interpretation; all ordinary map IDs retain `base`. -/
def overlay (reserved : List Nat) (value base : Nat → Nat → Nat) : Nat → Nat → Nat :=
  fun mp key => if reserved.contains mp then value mp key else base mp key

theorem overlay_interpret (reserved : List Nat) (value base : Nat → Nat → Nat) :
    WordInterpret reserved value (overlay reserved value base) := by
  intro mp hm key
  simp [overlay, hm]

theorem overlay_other (reserved : List Nat) (value base : Nat → Nat → Nat)
    (mp : Nat) (hm : mp ∉ reserved) (key : Nat) :
    overlay reserved value base mp key = base mp key := by
  simp [overlay, hm]

/-- The reserved namespace is untouched by initialization and by all three
kinds of map transition: request-carried, point writes, and every-key writes. -/
structure WordSMachine where
  s : SMachine
  reserved : List Nat
  value : Nat → Nat → Nat
  startDisjoint : ∀ p ∈ s.f.m.maps0, p.1 ∉ reserved
  carriedDisjoint : ∀ mp ∈ s.carried, mp ∉ reserved
  everyDisjoint : ∀ w ∈ s.every, w.1 ∉ reserved
  writesDisjoint : ∀ w ∈ s.f.m.writes, w.1 ∉ reserved

theorem overlay_start (w : WordSMachine) (base : Nat → Nat → Nat)
    (h : StartMaps w.s.f.m base) : StartMaps w.s.f.m (overlay w.reserved w.value base) := by
  intro p hp key
  rw [overlay_other _ _ _ _ (w.startDisjoint p hp)]
  exact h p hp key

/-- Exact decoding for a reserved getter at an arbitrary expression key. -/
theorem read_interpret {reserved : List Nat} {value M : Nat → Nat → Nat}
    (h : WordInterpret reserved value M) (X : Nat → Nat) (mp : Nat)
    (hm : mp ∈ reserved) (key : E) :
    evalE X M (.get mp key) = value mp (evalE X M key) := by
  exact h mp hm (evalE X M key)

theorem carried_interpret (w : WordSMachine) {M κ : Nat → Nat → Nat}
    (h : WordInterpret w.reserved w.value M) :
    WordInterpret w.reserved w.value (withCarried w.s M κ) := by
  intro mp hm key
  have hc : mp ∉ w.s.carried := by
    intro hmp
    exact w.carriedDisjoint mp hmp hm
  simp [withCarried, hc, h mp hm key]

theorem every_interpret (w : WordSMachine) {D : Nat → Nat}
    {N : Nat → Nat → Nat} (h : WordInterpret w.reserved w.value N) :
    WordInterpret w.reserved w.value (everyMaps w.s D N) := by
  intro mp hm key
  have he : lookup (fun entry => entry.1 == mp) w.s.every = none := by
    apply lookup_none
    intro entry he
    simp only [beq_eq_false_iff_ne]
    intro eq
    exact w.everyDisjoint entry he (eq ▸ hm)
  have hw : lookup (fun entry => entry.1 == mp) w.s.f.m.writes = none := by
    apply lookup_none
    intro entry he
    simp only [beq_eq_false_iff_ne]
    intro eq
    exact w.writesDisjoint entry he (eq ▸ hm)
  simpa [everyMaps, writeMaps, he, hw] using h mp hm key

/-- A reserved map cannot be silently substituted by a carried frame name. -/
theorem frameRd_reserved (w : WordSMachine) (mr : List (Nat × Nat))
    (hframe : ∀ p ∈ mr, p.1 ∈ w.s.carried)
    (rd : Nat → E → E) (mp : Nat) (hm : mp ∈ w.reserved) (key : E) :
    frameRd mr rd mp key = rd mp key := by
  have hn : lookup (fun p => p.1 == mp) mr = none := by
    apply lookup_none
    intro p hp
    simp only [beq_eq_false_iff_ne]
    intro he
    exact w.carriedDisjoint p.1 (hframe p hp) (he ▸ hm)
  simp [frameRd, hn]

/-- A reserved map is unaffected by either form of source-step map rewrite. -/
theorem stepRdS_reserved (w : WordSMachine) (τ : List (Nat × E))
    (rd : Nat → E → E) (mp : Nat) (hm : mp ∈ w.reserved) (key : E) :
    stepRdS w.s τ rd mp key = rd mp key := by
  have he : lookup (fun entry => entry.1 == mp) w.s.every = none := by
    apply lookup_none
    intro entry hp
    simp only [beq_eq_false_iff_ne]
    intro eq
    exact w.everyDisjoint entry hp (eq ▸ hm)
  have hw : lookup (fun entry => entry.1 == mp) w.s.f.m.writes = none := by
    apply lookup_none
    intro entry hp
    simp only [beq_eq_false_iff_ne]
    intro eq
    exact w.writesDisjoint entry hp (eq ▸ hm)
  simp [stepRdS, stepRd, he, hw]

theorem view_interpret (w : WordSMachine) {ρ ι : Nat → Nat}
    {M κ : Nat → Nat → Nat} (h : WordInterpret w.reserved w.value M) :
    WordInterpret w.reserved w.value (sView w.s ρ M ι κ).2 := by
  exact carried_interpret w h

theorem next_interpret (w : WordSMachine) {ρ ι : Nat → Nat}
    {M κ : Nat → Nat → Nat} (h : WordInterpret w.reserved w.value M) :
    WordInterpret w.reserved w.value (sNext w.s ρ M ι κ).2 := by
  exact every_interpret w (view_interpret w h)

/-- Starts from the actual concrete overlay and follows *precisely* `SReach`.
No arbitrary initial word maps, no stipulated helper law, no altered admission. -/
inductive WordSReach (w : WordSMachine) : (Nat → Nat) → (Nat → Nat → Nat) → Prop
  | start (ρ : Nat → Nat) (base : Nat → Nat → Nat) :
      StartMaps w.s.f.m base →
      evalC ρ (overlay w.reserved w.value base) w.s.f.m.pre = true →
      (∀ l ∈ w.s.facts, l.Holds ρ (overlay w.reserved w.value base)) →
      w.s.PFacts ρ (overlay w.reserved w.value base) →
      WordSReach w (applyS w.s.f.m.init ρ (overlay w.reserved w.value base))
        (overlay w.reserved w.value base)
  | step (ρ : Nat → Nat) (M : Nat → Nat → Nat)
      (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
      WordSReach w ρ M →
      evalC (sView w.s ρ M ι κ).1 (sView w.s ρ M ι κ).2 w.s.f.m.assume = true →
      WordSReach w (sNext w.s ρ M ι κ).1 (sNext w.s ρ M ι κ).2

/-- Forget concrete-word provenance, preserving the unmodified source reach. -/
theorem word_sreach_sreach (w : WordSMachine) :
    ∀ {ρ M}, WordSReach w ρ M → SReach w.s ρ M := by
  intro ρ M hr
  induction hr with
  | start ρ base hm hp hf hpf =>
      exact SReach.start ρ (overlay w.reserved w.value base)
        (overlay_start w base hm) hp hf hpf
  | step ρ M ι κ _ ha ih => exact SReach.step ρ M ι κ ih ha

/-- Every reachable state retains the concrete right-key interpretation at
*every* reserved map and key, including across arbitrary request maps. -/
theorem word_sreach_interpret (w : WordSMachine) :
    ∀ {ρ M}, WordSReach w ρ M → WordInterpret w.reserved w.value M := by
  intro ρ M hr
  induction hr with
  | start ρ base _ _ _ _ => exact overlay_interpret _ _ _
  | step ρ M ι κ _ _ ih => exact next_interpret w ih

/-- Map semantics at an admitted frame, before the step reads its terms. -/
theorem word_sreach_view_interpret (w : WordSMachine) {ρ M ι κ}
    (hr : WordSReach w ρ M) :
    WordInterpret w.reserved w.value (sView w.s ρ M ι κ).2 :=
  view_interpret w (word_sreach_interpret w hr)

end Kern.WordReach

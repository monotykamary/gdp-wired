import Ghost

/-!
What a refinement means, proven: compose.ts's `refinement(impl, spec, {relation, witness, stutter})` builds one machine,
the implementation beside the spec, the spec sent at each of the implementation's requests the request the witness
names, and left as it was where `stutter` holds. Lean builds that machine from the two (`Refined.full`), the spec given
in the composite's names, and checks that neither reads the other's parts (`refinedOk`). With the relation proven of the
composite (fmmachine_sound) and its step law that the spec allows every request it is sent (steplaw_sound):
- `refine_lift`: every reachable state of the implementation is, outside the spec's part, a reachable state of the
  composite;
- `refine_project`: the spec's part of every reachable state of the composite is a reachable state of the spec;
- `refines`: so every reachable state of the implementation is related, by the relation, to a reachable state of the
  spec.
-/

namespace Kern

structure Refined where
  impl : FMMachine            -- the implementation, in the composite's names
  spec : FMMachine            -- the spec, in the composite's names (its inputs fresh)
  wit : List (Nat × E)        -- each spec input and its term over the implementation's request and both states
  stutter : C                 -- where the implementation's step is one the spec doesn't see

-- The composite: the implementation, then the spec, its inputs read as the witness, each part kept where it stutters.
def Refined.full (r : Refined) : FMMachine :=
  ⟨{ inputs := r.impl.m.inputs
     init := r.impl.m.init ++ r.spec.m.init
     maps0 := r.impl.m.maps0 ++ r.spec.m.maps0
     step := r.impl.m.step ++ r.spec.m.step.map (fun p => (p.1, .ite r.stutter (.var p.1) (substE r.wit p.2)))
     writes := r.impl.m.writes ++ r.spec.m.writes.map (fun w =>
       (w.1, substE r.wit w.2.1, .ite r.stutter (.get w.1 (substE r.wit w.2.1)) (substE r.wit w.2.2)))
     pre := r.impl.m.pre
     assume := r.impl.m.assume },
   r.impl.flags ++ r.spec.flags.map (fun p => (p.1, substC r.wit p.2))⟩

-- What the composite's step law states: the spec doesn't step, or it allows the request it is sent.
def Refined.allowed (r : Refined) : C := inlineC r.full.flags (.or r.stutter (substC r.wit r.spec.m.assume))

-- The implementation's names (inputs, state, flags) and maps; the spec's (state and flags) and maps.
def Refined.IV (r : Refined) : List Nat := r.impl.m.inputs ++ r.impl.m.init.map (·.1) ++ r.impl.m.step.map (·.1) ++ flagVars r.impl.flags
def Refined.IM (r : Refined) : List Nat := r.impl.m.maps0.map (·.1) ++ r.impl.m.writes.map (·.1)
def Refined.SV (r : Refined) : List Nat := r.spec.m.init.map (·.1) ++ r.spec.m.step.map (·.1) ++ flagVars r.spec.flags
def Refined.SM (r : Refined) : List Nat := r.spec.m.maps0.map (·.1) ++ r.spec.m.writes.map (·.1)
-- Where a reachable state of the spec and the composite's agree: everywhere but the implementation's names and the
-- spec's flags and inputs (which a step sets before reading).
def Refined.X (r : Refined) : List Nat := r.IV ++ flagVars r.spec.flags ++ r.spec.m.inputs

def readsNone (V MS : List Nat) (c : C) : Bool := avoids V c && avoidsMaps MS c
def readsNoneE (V MS : List Nat) (e : E) : Bool := avoidsE V e && avoidsMapsE MS e

def refinedOk (r : Refined) : Bool :=
  -- The implementation reads no part of the spec.
  readsNone r.SV r.SM r.impl.m.pre && readsNone r.SV r.SM r.impl.m.assume
    && r.impl.flags.all (fun p => readsNone r.SV r.SM p.2) && r.impl.m.step.all (fun p => readsNoneE r.SV r.SM p.2)
    && r.impl.m.init.all (fun p => readsNoneE r.SV r.SM p.2) && r.impl.m.writes.all (fun w => readsNoneE r.SV r.SM w.2.1 && readsNoneE r.SV r.SM w.2.2)
  -- The spec reads no part of the implementation, and its flags read no flag.
    && readsNone r.IV r.IM r.spec.m.assume && r.spec.flags.all (fun p => readsNone (r.IV ++ flagVars r.spec.flags) r.IM p.2)
    && r.spec.m.step.all (fun p => readsNoneE r.IV r.IM p.2) && r.spec.m.init.all (fun p => readsNoneE (r.IV ++ r.spec.m.inputs) r.IM p.2)
    && r.spec.m.writes.all (fun w => readsNoneE r.IV r.IM w.2.1 && readsNoneE r.IV r.IM w.2.2)
  -- The spec's precondition reads the params alone.
    && readsNone (r.X ++ r.SV) r.IM r.spec.m.pre && !readsC r.spec.m.pre
  -- Names apart: the spec's from the implementation's, its inputs from both; maps apart.
    && r.SV.all (fun v => !r.IV.contains v) && r.spec.m.inputs.all (fun v => !(r.IV ++ r.SV).contains v)
    && r.SM.all (fun mp => !r.IM.contains mp)
  -- The witness names the spec's inputs, and it and `stutter` read no flag and no spec input.
    && r.wit.all (fun p => r.spec.m.inputs.contains p.1 && avoidsE (flagVars r.impl.flags ++ flagVars r.spec.flags ++ r.spec.m.inputs) p.2)
    && avoids (flagVars r.impl.flags ++ flagVars r.spec.flags ++ r.spec.m.inputs) r.stutter

-- Each of the spec's maps starts at one constant.
def refinedMapsOk (r : Refined) : Bool := distinct (r.spec.m.maps0.map (·.1))

/-! Lists and flags -/

theorem applyS_append_right {σ τ : List (Nat × E)} {i : Nat} (h : i ∉ σ.map (·.1)) (ρ : Nat → Nat) (M : Nat → Nat → Nat) :
    applyS (σ ++ τ) ρ M i = applyS τ ρ M i := by
  have hσ : lookup (fun p => p.1 == i) σ = none :=
    lookup_none (fun p hp => by simp only [beq_eq_false_iff_ne]; intro he; exact h (by rw [← he]; exact List.mem_map_of_mem hp))
  simp only [applyS, assoc, lookup_append, hσ]

theorem flagOf_append_left {fl fl' : List (Nat × C)} {i : Nat} (h : i ∉ flagVars fl') : flagOf (fl ++ fl') i = flagOf fl i := by
  have h' : lookup (fun p => p.1 == i) fl' = none :=
    lookup_none (fun p hp => by simp only [beq_eq_false_iff_ne]; intro he; exact h (by rw [← he]; exact List.mem_map_of_mem hp))
  simp only [flagOf, lookup_append]
  cases hl : lookup (fun p => p.1 == i) fl <;> simp [h']

theorem flagOf_append_right {fl fl' : List (Nat × C)} {i : Nat} (h : i ∉ flagVars fl) : flagOf (fl ++ fl') i = flagOf fl' i := by
  have h' : lookup (fun p => p.1 == i) fl = none :=
    lookup_none (fun p hp => by simp only [beq_eq_false_iff_ne]; intro he; exact h (by rw [← he]; exact List.mem_map_of_mem hp))
  simp only [flagOf, lookup_append, h']

theorem flagOf_map {fl : List (Nat × C)} {g : C → C} (i : Nat) : flagOf (fl.map (fun p => (p.1, g p.2))) i = (flagOf fl i).map g := by
  simp only [flagOf]
  induction fl with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, lookup]
    split <;> simp_all

theorem decideFlags_of (fl : List (Nat × C)) (X : Nat → Nat) (M : Nat → Nat → Nat) (i : Nat) :
    decideFlags fl X M i = match flagOf fl i with
      | some c => if evalC X M c = true then 1 else 0
      | none => X i := by
  simp only [decideFlags, applyS, assoc_flagSub]
  cases flagOf fl i <;> simp [evalE]

theorem rn_v {V MS : List Nat} {c : C} (h : readsNone V MS c = true) : avoids V c = true := by simp only [readsNone, Bool.and_eq_true] at h; exact h.1
theorem rn_m {V MS : List Nat} {c : C} (h : readsNone V MS c = true) : avoidsMaps MS c = true := by simp only [readsNone, Bool.and_eq_true] at h; exact h.2
theorem rnE_v {V MS : List Nat} {e : E} (h : readsNoneE V MS e = true) : avoidsE V e = true := by simp only [readsNoneE, Bool.and_eq_true] at h; exact h.1
theorem rnE_m {V MS : List Nat} {e : E} (h : readsNoneE V MS e = true) : avoidsMapsE MS e = true := by simp only [readsNoneE, Bool.and_eq_true] at h; exact h.2

theorem assoc_map_fst (l : List (Nat × E)) (g : Nat × E → E) (v : Nat) :
    assoc (l.map (fun q => (q.1, g q))) v = (lookup (fun q => q.1 == v) l).map g := by
  simp only [assoc, lookup_map_pred, Option.map_map]; rfl

theorem lookup_writes_map (l : List (Nat × E × E)) (g : Nat × E × E → E × E) (mp : Nat) :
    lookup (fun w : Nat × E × E => w.1 == mp) (l.map (fun w => (w.1, g w))) = (lookup (fun w : Nat × E × E => w.1 == mp) l).map (fun w => (w.1, g w)) := by
  rw [lookup_map_pred]

/-! The implementation's runs, inside the composite's -/

section lift
variable (r : Refined) (hok : refinedOk r = true) (hmo : refinedMapsOk r = true)
include hok

theorem refined_parts :
    readsNone r.SV r.SM r.impl.m.pre = true ∧ readsNone r.SV r.SM r.impl.m.assume = true
      ∧ (∀ p ∈ r.impl.flags, readsNone r.SV r.SM p.2 = true) ∧ (∀ p ∈ r.impl.m.step, readsNoneE r.SV r.SM p.2 = true)
      ∧ (∀ p ∈ r.impl.m.init, readsNoneE r.SV r.SM p.2 = true)
      ∧ (∀ w ∈ r.impl.m.writes, readsNoneE r.SV r.SM w.2.1 = true ∧ readsNoneE r.SV r.SM w.2.2 = true)
      ∧ readsNone r.IV r.IM r.spec.m.assume = true ∧ (∀ p ∈ r.spec.flags, readsNone (r.IV ++ flagVars r.spec.flags) r.IM p.2 = true)
      ∧ (∀ p ∈ r.spec.m.step, readsNoneE r.IV r.IM p.2 = true) ∧ (∀ p ∈ r.spec.m.init, readsNoneE (r.IV ++ r.spec.m.inputs) r.IM p.2 = true)
      ∧ (∀ w ∈ r.spec.m.writes, readsNoneE r.IV r.IM w.2.1 = true ∧ readsNoneE r.IV r.IM w.2.2 = true)
      ∧ readsNone (r.X ++ r.SV) r.IM r.spec.m.pre = true ∧ readsC r.spec.m.pre = false
      ∧ (∀ v ∈ r.SV, v ∉ r.IV) ∧ (∀ v ∈ r.spec.m.inputs, v ∉ r.IV ++ r.SV) ∧ (∀ mp ∈ r.SM, mp ∉ r.IM)
      ∧ (∀ p ∈ r.wit, p.1 ∈ r.spec.m.inputs ∧ avoidsE (flagVars r.impl.flags ++ flagVars r.spec.flags ++ r.spec.m.inputs) p.2 = true)
      ∧ avoids (flagVars r.impl.flags ++ flagVars r.spec.flags ++ r.spec.m.inputs) r.stutter = true := by
  simp only [refinedOk, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩ := hok
  refine ⟨h1, h2, h3, h4, h5, fun w hw => (h6 w hw), h7, h8, h9, h10, fun w hw => h11 w hw, h12, h13, fun v hv h => ?_, fun v hv h => ?_,
    fun mp hm h => ?_, fun p hp => ⟨List.contains_iff_mem.mp (h17 p hp).1, (h17 p hp).2⟩, h18⟩
  · have := h14 v hv; rw [List.contains_iff_mem.mpr h] at this; cases this
  · have := h15 v hv; rw [List.contains_iff_mem.mpr h] at this; cases this
  · have := h16 mp hm; rw [List.contains_iff_mem.mpr h] at this; cases this

-- One step of the composite from a state that agrees with the implementation's outside the spec's part, with the same
-- request: allowed alike, to states that still agree.
theorem refine_step {ρ ρc : Nat → Nat} {M Mc : Nat → Nat → Nat} (hag : Agree r.SV ρc ρ) (hmag : ∀ mp, mp ∉ r.SM → Mc mp = M mp) (ι : Nat → Nat) :
    (evalC (decideFlags r.full.flags (withInputs r.full.m.inputs ρc ι) Mc) Mc r.full.m.assume
        = evalC (decideFlags r.impl.flags (withInputs r.impl.m.inputs ρ ι) M) M r.impl.m.assume)
      ∧ Agree r.SV (applyS r.full.m.step (decideFlags r.full.flags (withInputs r.full.m.inputs ρc ι) Mc) Mc)
          (applyS r.impl.m.step (decideFlags r.impl.flags (withInputs r.impl.m.inputs ρ ι) M) M)
      ∧ ∀ mp, mp ∉ r.SM → writeMaps r.full.m.writes (decideFlags r.full.flags (withInputs r.full.m.inputs ρc ι) Mc) Mc mp
          = writeMaps r.impl.m.writes (decideFlags r.impl.flags (withInputs r.impl.m.inputs ρ ι) M) M mp := by
  obtain ⟨_, ha, hf, hs, _, hw, _⟩ := refined_parts r hok
  have hin : Agree r.SV (withInputs r.impl.m.inputs ρc ι) (withInputs r.impl.m.inputs ρ ι) := fun i hi => by
    simp only [withInputs]; split
    · rfl
    · exact hag i hi
  -- The composite's flags decide the implementation's alike, outside the spec's flag names.
  have hD : Agree r.SV (decideFlags r.full.flags (withInputs r.full.m.inputs ρc ι) Mc) (decideFlags r.impl.flags (withInputs r.impl.m.inputs ρ ι) M) := by
    intro i hi
    have hif : i ∉ flagVars (r.spec.flags.map (fun p => (p.1, substC r.wit p.2))) := fun h' => hi (by
      simp only [flagVars, List.map_map] at h'; simp only [Refined.SV, List.mem_append]; right
      simpa [flagVars, Function.comp_def] using h')
    show decideFlags (r.impl.flags ++ _) (withInputs r.impl.m.inputs ρc ι) Mc i = _
    rw [decideFlags_of, decideFlags_of, flagOf_append_left hif]
    cases hfo : flagOf r.impl.flags i with
    | none => exact hin i hi
    | some c =>
      obtain ⟨p, hp, rfl⟩ := flagOf_some hfo
      simp only
      rw [congrMC _ Mc M _ (fun mp hmp => hmag mp (avoidsMaps_occ (rn_m (hf p hp)) hmp)),
        congrC _ _ M _ (fun j hj => hin j (avoids_occ (rn_v (hf p hp)) hj))]
  refine ⟨?_, fun i hi => ?_, fun mp hmp => ?_⟩
  · show evalC _ Mc r.impl.m.assume = _
    rw [congrMC _ Mc M _ (fun mp hmp => hmag mp (avoidsMaps_occ (rn_m ha) hmp)), congrC _ _ M _ (fun j hj => hD j (avoids_occ (rn_v ha) hj))]
  · show applyS (r.impl.m.step ++ _) _ Mc i = _
    have hit : i ∉ (r.spec.m.step.map (fun p => (p.1, E.ite r.stutter (.var p.1) (substE r.wit p.2)))).map (·.1) := fun h' => hi (by
      simp only [List.map_map] at h'; simp only [Refined.SV, List.mem_append]; left; right; simpa [Function.comp_def] using h')
    rw [applyS_append_other hit]
    simp only [applyS]
    cases hst : assoc r.impl.m.step i with
    | none => exact hD i hi
    | some e =>
      have hm : (i, e) ∈ r.impl.m.step := by
        simp only [assoc, Option.map_eq_some_iff] at hst
        obtain ⟨q, hq, rfl⟩ := hst
        obtain ⟨hqm, hqv⟩ := lookup_some hq
        simp only [beq_iff_eq] at hqv; rw [← hqv]; exact hqm
      dsimp only
      rw [congrME _ Mc M e (fun mp hmp => hmag mp (avoidsMapsE_occ (rnE_m (hs (i, e) hm)) hmp)),
        congrE _ _ M e (fun j hj => hD j (avoidsE_occ (rnE_v (hs (i, e) hm)) hj))]
  · funext key
    show writeMaps (r.impl.m.writes ++ _) _ Mc mp key = _
    have hwm : lookup (fun w : Nat × E × E => w.1 == mp) (r.spec.m.writes.map (fun w =>
        (w.1, substE r.wit w.2.1, E.ite r.stutter (.get w.1 (substE r.wit w.2.1)) (substE r.wit w.2.2)))) = none :=
      lookup_none (fun w hw' => by
        simp only [beq_eq_false_iff_ne]; intro he
        obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw'
        exact hmp (by simp only [Refined.SM, List.mem_append]; right; rw [← he]; exact List.mem_map.mpr ⟨w0, hw0, rfl⟩))
    simp only [writeMaps, lookup_append]
    cases hl : lookup (fun w => w.1 == mp) r.impl.m.writes with
    | none => simp only [hwm]; exact congrFun (hmag mp hmp) key
    | some w =>
      obtain ⟨h1, h2⟩ := hw w (lookup_some hl).1
      simp only
      rw [congrME _ Mc M w.2.1 (fun mp' h => hmag mp' (avoidsMapsE_occ (rnE_m h1) h)), congrE _ _ M w.2.1 (fun j hj => hD j (avoidsE_occ (rnE_v h1) hj)),
        congrME _ Mc M w.2.2 (fun mp' h => hmag mp' (avoidsMapsE_occ (rnE_m h2) h)), congrE _ _ M w.2.2 (fun j hj => hD j (avoidsE_occ (rnE_v h2) hj)), hmag mp hmp]

include hmo in
/-- Every reachable state of the implementation is, outside the spec's part, a reachable state of the composite. -/
theorem refine_lift : ∀ {ρ M}, FMReach r.impl ρ M → ∃ ρc Mc, FMReach r.full ρc Mc ∧ Agree r.SV ρc ρ ∧ ∀ mp, mp ∉ r.SM → Mc mp = M mp := by
  obtain ⟨hp, _, _, _, hi, _⟩ := refined_parts r hok
  have hsm := (refined_parts r hok).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  intro ρ M hr
  induction hr with
  | start ρ M hM h0 =>
    -- The spec's maps start at their constants; every other map as the implementation's.
    let Mc : Nat → Nat → Nat := fun mp => match lookup (fun p => p.1 == mp) r.spec.m.maps0 with
      | some p => fun _ => p.2
      | none => M mp
    have hMc : ∀ mp, mp ∉ r.SM → Mc mp = M mp := fun mp hmp => by
      simp only [Mc]
      rw [lookup_none (fun p hp' => by
        simp only [beq_eq_false_iff_ne]; intro he
        exact hmp (by simp only [Refined.SM, List.mem_append]; left; rw [← he]; exact List.mem_map_of_mem hp'))]
    have hpre : evalC ρ Mc r.full.m.pre = true := by
      show evalC ρ Mc r.impl.m.pre = true
      rw [congrMC _ Mc M _ (fun mp hmp => hMc mp (avoidsMaps_occ (rn_m hp) hmp))]; exact h0
    have hstart : StartMaps r.full.m Mc := by
      intro p hp' key
      rcases List.mem_append.mp hp' with hp' | hp'
      · -- An implementation's map: none of the spec's, so as the implementation's start has it.
        have hn : p.1 ∉ r.SM := fun h' => hsm p.1 h' (by simp only [Refined.IM, List.mem_append]; left; exact List.mem_map_of_mem hp')
        rw [hMc p.1 hn]; exact hM p hp' key
      · -- A spec's map: its one constant.
        have hl : lookup (fun q => q.1 == p.1) r.spec.m.maps0 = some p := lookup_unique1 (by simpa [refinedMapsOk] using hmo) hp'
        simp only [Mc, hl]
    refine ⟨_, Mc, FMReach.start ρ Mc hstart hpre, fun i hi' => ?_, hMc⟩
    show applyS (r.impl.m.init ++ r.spec.m.init) ρ Mc i = applyS r.impl.m.init ρ M i
    rw [applyS_append_other (by
      intro h'; apply hi'; simp only [Refined.SV, List.mem_append]; left; left; exact h')]
    simp only [applyS]
    cases hst : assoc r.impl.m.init i with
    | none => rfl
    | some e =>
      have hm : (i, e) ∈ r.impl.m.init := by
        simp only [assoc, Option.map_eq_some_iff] at hst
        obtain ⟨q, hq, rfl⟩ := hst
        obtain ⟨hqm, hqv⟩ := lookup_some hq
        simp only [beq_iff_eq] at hqv; rw [← hqv]; exact hqm
      exact congrME _ Mc M e (fun mp hmp => hMc mp (avoidsMapsE_occ (rnE_m (hi (i, e) hm)) hmp))
  | step ρ M ι _ ha ih =>
    obtain ⟨ρc, Mc, hrc, hag, hmag⟩ := ih
    obtain ⟨hA, hS, hW⟩ := refine_step r hok hag hmag ι
    exact ⟨_, _, FMReach.step ρc Mc ι hrc (by rw [hA]; exact ha), hS, hW⟩
end lift

/-! The spec's part of the composite's runs -/

section project
variable (r : Refined) (hok : refinedOk r = true)
include hok

-- The spec's view of a step (its flags decided over its state, its inputs as the witness reads them) agrees with the
-- composite's view with the witness put in, outside the implementation's names.
theorem spec_view {ρ σ : Nat → Nat} {M Ms : Nat → Nat → Nat} (hag : Agree r.X σ ρ) (hmag : ∀ mp, mp ∉ r.IM → Ms mp = M mp) (ι : Nat → Nat) :
    Agree r.IV (decideFlags r.spec.flags (withInputs r.spec.m.inputs σ (applyS r.wit (decideFlags r.full.flags (withInputs r.full.m.inputs ρ ι) M) M)) Ms)
      (applyS r.wit (decideFlags r.full.flags (withInputs r.full.m.inputs ρ ι) M) M) := by
  obtain ⟨_, _, _, _, _, _, _, hsf, _, _, _, _, _, hsv, hsi, _, hwit, _⟩ := refined_parts r hok
  have hwdom : ∀ i, i ∉ r.spec.m.inputs → i ∉ r.wit.map (·.1) := fun i hi h' => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h'; exact hi (hwit p hp).1
  have hflagF : ∀ i, i ∉ flagVars r.impl.flags → i ∉ flagVars r.spec.flags → i ∉ flagVars r.full.flags := fun i h1 h2 h' => by
    simp only [Refined.full, flagVars, List.map_append, List.map_map, List.mem_append] at h'
    rcases h' with h' | h'
    · exact h1 h'
    · exact h2 (by simpa [flagVars, Function.comp_def] using h')
  -- The witness reads alike in the composite's view and before its flags are decided.
  have hXW : ∀ j, j ∉ flagVars r.full.flags → applyS r.wit (decideFlags r.full.flags (withInputs r.full.m.inputs ρ ι) M) M j
      = applyS r.wit (withInputs r.full.m.inputs ρ ι) M j := fun j hj => by
    simp only [applyS]
    cases ha : assoc r.wit j with
    | none => exact decide_other hj _ M
    | some e =>
      have hm : (j, e) ∈ r.wit := by
        simp only [assoc, Option.map_eq_some_iff] at ha
        obtain ⟨q, hq, rfl⟩ := ha
        obtain ⟨hqm, hqv⟩ := lookup_some hq
        simp only [beq_iff_eq] at hqv; rw [← hqv]; exact hqm
      exact congrE _ _ M e (fun k hk => decide_other (fun h' => by
        have := avoidsE_occ (hwit (j, e) hm).2 hk
        simp only [Refined.full, flagVars, List.map_append, List.map_map, List.mem_append] at h'
        rcases h' with h' | h'
        · exact this (List.mem_append_left _ (List.mem_append_left _ h'))
        · exact this (List.mem_append_left _ (List.mem_append_right _ (by simpa [flagVars, Function.comp_def] using h')))) _ M)
  have hIVf : ∀ i, i ∉ r.IV → i ∉ flagVars r.impl.flags := fun i hi h' => hi (List.mem_append_right _ h')
  have hIVi : ∀ i, i ∉ r.IV → i ∉ r.impl.m.inputs := fun i hi h' => hi (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h')))
  intro v hv
  by_cases hvf : v ∈ flagVars r.spec.flags
  · -- A spec flag: decided over the spec's view; in the composite, its condition with the witness put in.
    have hvi : v ∉ r.spec.m.inputs := fun h' => hsi v h' (List.mem_append_right _ (List.mem_append_right _ hvf))
    cases hfo : flagOf r.spec.flags v with
    | none => exact absurd hvf (flagOf_none hfo)
    | some c =>
      obtain ⟨p, hp, rfl⟩ := flagOf_some hfo
      have hfull : flagOf r.full.flags v = some (substC r.wit p.2) := by
        show flagOf (r.impl.flags ++ _) v = _
        rw [flagOf_append_right (hIVf v hv), flagOf_map, hfo]; rfl
      rw [decideFlags_of, hfo]
      simp only [applyS]
      rw [assoc_none_of (hwdom v hvi)]
      simp only
      rw [decideFlags_of, hfull]
      simp only
      rw [subst_evalC, congrMC _ Ms M _ (fun mp hmp => hmag mp (avoidsMaps_occ (rn_m (hsf p hp)) hmp))]
      rw [congrC _ (applyS r.wit (withInputs r.full.m.inputs ρ ι) M) M p.2 (fun j hj => by
        have hj1 : j ∉ r.IV := fun h' => avoids_occ (rn_v (hsf p hp)) hj (List.mem_append_left _ h')
        have hj2 : j ∉ flagVars r.spec.flags := fun h' => avoids_occ (rn_v (hsf p hp)) hj (List.mem_append_right _ h')
        by_cases hji : j ∈ r.spec.m.inputs
        · simp only [withInputs, List.contains_iff_mem.mpr hji, if_true]
          exact hXW j (hflagF j (hIVf j hj1) hj2)
        · rw [withInputs_other hji, hag j (fun h' => by
            simp only [Refined.X, List.mem_append] at h'; rcases h' with (h' | h') | h'
            · exact hj1 h'
            · exact hj2 h'
            · exact hji h')]
          simp only [applyS]; rw [assoc_none_of (hwdom j hji)]
          exact (withInputs_other (hIVi j hj1) ρ ι).symm)]
  · by_cases hvi : v ∈ r.spec.m.inputs
    · rw [decide_other hvf]
      simp only [withInputs, List.contains_iff_mem.mpr hvi, if_true]
    · rw [decide_other hvf, withInputs_other hvi, hag v (fun h' => by
        simp only [Refined.X, List.mem_append] at h'; rcases h' with (h' | h') | h'
        · exact hv h'
        · exact hvf h'
        · exact hvi h')]
      rw [hXW v (hflagF v (hIVf v hv) hvf)]
      simp only [applyS]
      rw [assoc_none_of (hwdom v hvi)]
      exact (withInputs_other (hIVi v hv) ρ ι).symm

-- A term of the spec, read in the spec's view, is the term with the witness put in, read in the composite's view.
theorem spec_term {ρ σ : Nat → Nat} {M Ms : Nat → Nat → Nat} (hag : Agree r.X σ ρ) (hmag : ∀ mp, mp ∉ r.IM → Ms mp = M mp) (ι : Nat → Nat)
    {e : E} (he : readsNoneE r.IV r.IM e = true) :
    evalE (decideFlags r.spec.flags (withInputs r.spec.m.inputs σ (applyS r.wit (decideFlags r.full.flags (withInputs r.full.m.inputs ρ ι) M) M)) Ms) Ms e
      = evalE (decideFlags r.full.flags (withInputs r.full.m.inputs ρ ι) M) M (substE r.wit e) := by
  rw [subst_evalE, congrME _ Ms M e (fun mp hmp => hmag mp (avoidsMapsE_occ (rnE_m he) hmp))]
  exact congrE _ _ M e (fun j hj => spec_view r hok hag hmag ι j (avoidsE_occ (rnE_v he) hj))

theorem spec_cond {ρ σ : Nat → Nat} {M Ms : Nat → Nat → Nat} (hag : Agree r.X σ ρ) (hmag : ∀ mp, mp ∉ r.IM → Ms mp = M mp) (ι : Nat → Nat)
    {c : C} (hc : readsNone r.IV r.IM c = true) :
    evalC (decideFlags r.spec.flags (withInputs r.spec.m.inputs σ (applyS r.wit (decideFlags r.full.flags (withInputs r.full.m.inputs ρ ι) M) M)) Ms) Ms c
      = evalC (decideFlags r.full.flags (withInputs r.full.m.inputs ρ ι) M) M (substC r.wit c) := by
  rw [subst_evalC, congrMC _ Ms M c (fun mp hmp => hmag mp (avoidsMaps_occ (rn_m hc) hmp))]
  exact congrC _ _ M c (fun j hj => spec_view r hok hag hmag ι j (avoids_occ (rn_v hc) hj))

-- A variable none of the composite's or the spec's flags or inputs, and the composite's view reads it as the state does.
theorem view_plain {ρ : Nat → Nat} {M : Nat → Nat → Nat} (ι : Nat → Nat) {v : Nat} (hv : v ∉ r.X) :
    decideFlags r.full.flags (withInputs r.full.m.inputs ρ ι) M v = ρ v := by
  simp only [Refined.X, Refined.IV, List.mem_append, not_or] at hv
  obtain ⟨⟨⟨⟨⟨hi, _⟩, _⟩, hf⟩, hsf⟩, _⟩ := hv
  rw [decide_other (fun h' => by
    simp only [Refined.full, flagVars, List.map_append, List.map_map, List.mem_append] at h'
    rcases h' with h' | h'
    · exact hf h'
    · exact hsf (by simpa [flagVars, Function.comp_def] using h'))]
  exact withInputs_other hi ρ ι

/-- The spec's part of every reachable state of the composite is a reachable state of the spec, given that the spec's
precondition holds at every reachable state of the composite (one of its laws) and that the spec allows every request
the composite sends it (its step law). -/
theorem refine_project (hpre : ∀ ρ M, FMReach r.full ρ M → evalC ρ M r.spec.m.pre = true)
    (hallow : ∀ ρ M, FMReach r.full ρ M → ∀ ι, evalC (decideFlags r.full.flags (withInputs r.full.m.inputs ρ ι) M) M r.full.m.assume = true →
      evalC (withInputs r.full.m.inputs ρ ι) M r.allowed = true) :
    ∀ {ρ M}, FMReach r.full ρ M → ∃ σ Ms, FMReach r.spec σ Ms ∧ Agree r.X σ ρ ∧ ∀ mp, mp ∉ r.IM → Ms mp = M mp := by
  obtain ⟨_, _, _, _, _, _, hsa, _, hss, hsi, hsw, hsp, hrp, hsv, _, hsm, _, hst⟩ := refined_parts r hok
  intro ρ M hr
  induction hr with
  | start ρ M hM h0 =>
    -- The spec starts where the composite's state was before its start values: its precondition reads the params.
    have hp0 : evalC ρ M r.spec.m.pre = true := by
      have h := hpre _ M (FMReach.start ρ M hM h0)
      have hag0 : ∀ i, occC i r.spec.m.pre = true → applyS r.full.m.init ρ M i = ρ i := fun i hi => applyS_other (fun h' => by
        apply avoids_occ (rn_v hsp) hi
        simp only [Refined.full, List.map_append, List.mem_append] at h'
        rcases h' with h' | h' <;> simp [Refined.X, Refined.IV, Refined.SV, h']) ρ M
      rwa [congrC _ ρ M r.spec.m.pre hag0] at h
    have hMs : StartMaps r.spec.m M := fun p hp' key => hM p (List.mem_append_right _ hp') key
    refine ⟨_, M, FMReach.start ρ M hMs hp0, fun i hi => ?_, fun _ _ => rfl⟩
    show applyS r.spec.m.init ρ M i = applyS (r.impl.m.init ++ r.spec.m.init) ρ M i
    rw [applyS_append_right (fun h' => hi (by simp [Refined.X, Refined.IV, h']))]
  | step ρ M ι hr ha ih =>
    obtain ⟨σ, Ms, hrs, hag, hmag⟩ := ih
    have hA := hallow ρ M hr ι ha
    simp only [Refined.allowed] at hA
    rw [inline_evalC] at hA
    simp only [evalC, Bool.or_eq_true] at hA
    -- The composite's step at a variable or map of the spec's part: kept where it stutters, the spec's term otherwise.
    have hstepS : ∀ v, v ∉ r.IV → applyS r.full.m.step (decideFlags r.full.flags (withInputs r.full.m.inputs ρ ι) M) M v
        = applyS (r.spec.m.step.map (fun p => (p.1, E.ite r.stutter (.var p.1) (substE r.wit p.2)))) (decideFlags r.full.flags (withInputs r.full.m.inputs ρ ι) M) M v :=
      fun v hv => applyS_append_right (fun h' => hv (List.mem_append_left _ (List.mem_append_right _ h'))) _ M
    by_cases hstut : evalC (decideFlags r.full.flags (withInputs r.full.m.inputs ρ ι) M) M r.stutter = true
    · -- The spec doesn't step: its state is the same, and so is the composite's spec part.
      refine ⟨σ, Ms, hrs, fun v hv => ?_, fun mp hmp => ?_⟩
      · rw [hstepS v (fun h' => hv (List.mem_append_left _ (List.mem_append_left _ h')))]
        simp only [applyS]
        cases hl : assoc (r.spec.m.step.map (fun p => (p.1, E.ite r.stutter (.var p.1) (substE r.wit p.2)))) v with
        | none => dsimp only; rw [view_plain r hok ι hv]; exact hag v hv
        | some e =>
          obtain ⟨q, hq, hqv, rfl⟩ : ∃ q ∈ r.spec.m.step, q.1 = v ∧ e = E.ite r.stutter (.var q.1) (substE r.wit q.2) := by
            simp only [assoc, Option.map_eq_some_iff] at hl
            obtain ⟨x, hx, rfl⟩ := hl
            obtain ⟨hxm, hxv⟩ := lookup_some hx
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hxm
            simp only [beq_iff_eq] at hxv
            exact ⟨q, hq, hxv, rfl⟩
          dsimp only
          simp only [evalE, hstut, if_true]
          rw [hqv, view_plain r hok ι hv]; exact hag v hv
      · funext key
        show Ms mp key = writeMaps (r.impl.m.writes ++ _) _ M mp key
        rw [hmag mp hmp]
        simp only [writeMaps, lookup_append]
        rw [lookup_none (l := r.impl.m.writes) (fun w hw => by simp only [beq_eq_false_iff_ne]; intro he; exact hmp (by
          simp only [Refined.IM, List.mem_append]; right; rw [← he]; exact List.mem_map_of_mem hw))]
        (try dsimp only); rw [lookup_writes_map]
        cases hw0 : lookup (fun w : Nat × E × E => w.1 == mp) r.spec.m.writes with
        | none => rfl
        | some w0 =>
          have hw0m := (lookup_some hw0).2
          simp only [beq_iff_eq] at hw0m
          simp only [Option.map_some, evalE, hstut, if_true, hw0m]
          by_cases hk : key = evalE (decideFlags r.full.flags (withInputs r.full.m.inputs ρ ι) M) M (substE r.wit w0.2.1)
          · rw [if_pos hk, ← hk]
          · rw [if_neg hk]
    · -- The spec steps, sent the witness's request, which it allows.
      have hX := hA.resolve_left hstut
      rw [← spec_cond r hok hag hmag ι (c := r.spec.m.assume) hsa] at hX
      refine ⟨_, _, FMReach.step σ Ms _ hrs hX, fun v hv => ?_, fun mp hmp => ?_⟩
      · rw [hstepS v (fun h' => hv (List.mem_append_left _ (List.mem_append_left _ h')))]
        simp only [applyS]
        rw [assoc_map_fst]
        cases hl : lookup (fun q => q.1 == v) r.spec.m.step with
        | none =>
          have hn : assoc r.spec.m.step v = none := by simp only [assoc, hl, Option.map_none]
          rw [hn]; dsimp only
          rw [view_plain r hok ι hv]
          have hvf : v ∉ flagVars r.spec.flags := fun h' => hv (List.mem_append_left _ (List.mem_append_right _ h'))
          have hvi : v ∉ r.spec.m.inputs := fun h' => hv (List.mem_append_right _ h')
          rw [decide_other hvf, withInputs_other hvi]; exact hag v hv
        | some q =>
          have hq := lookup_some hl
          simp only [beq_iff_eq] at hq
          have hn : assoc r.spec.m.step v = some q.2 := by simp only [assoc, hl, Option.map_some]
          rw [hn]; dsimp only
          simp only [Option.map_some, evalE, hstut, Bool.false_eq_true, if_false]
          have hm : (v, q.2) ∈ r.spec.m.step := by rw [← hq.2]; exact hq.1
          exact spec_term r hok hag hmag ι (hss (v, q.2) hm)
      · funext key
        show writeMaps r.spec.m.writes _ Ms mp key = writeMaps (r.impl.m.writes ++ _) _ M mp key
        simp only [writeMaps, lookup_append]
        rw [lookup_none (l := r.impl.m.writes) (fun w hw => by simp only [beq_eq_false_iff_ne]; intro he; exact hmp (by
          simp only [Refined.IM, List.mem_append]; right; rw [← he]; exact List.mem_map_of_mem hw))]
        simp only
        rw [lookup_writes_map]
        cases hw0 : lookup (fun w : Nat × E × E => w.1 == mp) r.spec.m.writes with
        | none => simp only [Option.map_none]; exact congrFun (hmag mp hmp) key
        | some w0 =>
          have hw0m := lookup_some hw0
          obtain ⟨h1, h2⟩ := hsw w0 hw0m.1
          simp only [Option.map_some, evalE, hstut, Bool.false_eq_true, if_false]
          rw [spec_term r hok hag hmag ι h1, spec_term r hok hag hmag ι h2, hmag mp hmp]
end project

-- Read where `then` reads, a condition that reads no primed name is the condition before the step.
theorem unprimed_evalC {pr pm : List (Nat × Nat)} {c : C} (hv : avoids (pr.map (·.2)) c = true) (hm : avoidsMaps (pm.map (·.2)) c = true)
    (ρ ρ' : Nat → Nat) (M M' : Nat → Nat → Nat) : evalC (primed pr ρ' ρ) (primedMaps pm M' M) c = evalC ρ M c := by
  rw [congrC _ ρ _ c (fun i hi => by
    simp only [primed]
    rw [lookup_none (fun q hq => by simp only [beq_eq_false_iff_ne]; intro he; exact avoids_occ hv hi (by rw [← he]; exact List.mem_map_of_mem hq))])]
  exact congrMC ρ _ M c (fun mp hmp => by
    funext k; simp only [primedMaps]
    rw [lookup_none (fun q hq => by simp only [beq_eq_false_iff_ne]; intro he; exact avoidsMaps_occ hm hmp (by rw [← he]; exact List.mem_map_of_mem hq))])

/-- What a refinement means: with the relation (and the spec's precondition, the j-th law) proven of the composite, and
its step law that the spec allows every request it is sent, every reachable state of the implementation is, outside
the spec's part, a reachable state of the composite, whose spec part is a reachable state of the spec, the two related
by every law. -/
theorem refines (r : Refined) (hok : refinedOk r = true) (hmo : refinedMapsOk r = true) (ps : List MEntry) (hl : checkFMMachine r.full ps = true)
    (j : Nat) (hj : (ps[j]?).map (·.law.holds) = some r.spec.m.pre ∧ (ps[j]?).map (·.law.key) = some none)
    (prime primeMaps : List (Nat × Nat)) (insts : List (Nat × E)) (proof : List VDef × Tree)
    (hs : checkStepLaw r.full ps ⟨trueC, r.allowed, prime, primeMaps, insts, proof⟩ = true)
    (hfresh : avoids (prime.map (·.2)) r.allowed = true ∧ avoidsMaps (primeMaps.map (·.2)) r.allowed = true) :
    ∀ ρ M, FMReach r.impl ρ M → ∃ ρc Mc σ Ms, FMReach r.full ρc Mc ∧ Agree r.SV ρc ρ ∧ (∀ mp, mp ∉ r.SM → Mc mp = M mp)
      ∧ FMReach r.spec σ Ms ∧ Agree r.X σ ρc ∧ (∀ mp, mp ∉ r.IM → Ms mp = Mc mp) ∧ ∀ e ∈ ps, e.law.Holds ρc Mc := by
  have hlaws := fmmachine_sound r.full ps hl
  have hpre : ∀ ρ M, FMReach r.full ρ M → evalC ρ M r.spec.m.pre = true := by
    intro ρ M hr
    cases he : ps[j]? with
    | none => simp [he] at hj
    | some e =>
      simp only [he, Option.map_some, Option.some.injEq] at hj
      have h := hlaws ρ M hr e (List.mem_of_getElem? he)
      unfold MLaw.Holds at h
      rw [hj.2] at h
      simpa [hj.1] using h
  have hsl := steplaw_sound r.full ps _ hl hs
  have hallow : ∀ ρ M, FMReach r.full ρ M → ∀ ι, evalC (decideFlags r.full.flags (withInputs r.full.m.inputs ρ ι) M) M r.full.m.assume = true →
      evalC (withInputs r.full.m.inputs ρ ι) M r.allowed = true := by
    intro ρ M hr ι ha
    have h := hsl ρ M hr ι ha (by simp [trueC, evalC, evalE])
    rwa [unprimed_evalC hfresh.1 hfresh.2] at h
  intro ρ M hr
  obtain ⟨ρc, Mc, hrc, hag, hmag⟩ := refine_lift r hok hmo hr
  obtain ⟨σ, Ms, hrs, hags, hmags⟩ := refine_project r hok hpre hallow hrc
  exact ⟨ρc, Mc, σ, Ms, hrc, hag, hmag, hrs, hags, hmags, hlaws ρc Mc hrc⟩

end Kern

#print axioms Kern.refine_lift
#print axioms Kern.refine_project
#print axioms Kern.refines

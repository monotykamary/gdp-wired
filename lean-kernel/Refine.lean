import Ghost

/-!
What a refinement means, proven: compose.ts's `refinement(impl, spec, {relation, witness, stutter})` builds one machine,
the implementation beside the spec, the spec sent at each of the implementation's requests the request the witness
names, and left as it was where `stutter` holds. Lean builds that machine from the two (`SRefined.full`), the spec
given in the composite's names, and checks that neither reads the other's parts (`srOk`). The machines have maps,
flags and sets (a machine with maps and flags is one with no sets): requests carry maps, the spec's among the
implementation's, shared by name. With the relation proven of the composite (smachine_sound) and its step law that the
spec stutters or allows every request it is sent (skstep_sound):
- `srefine_lift`: every reachable state of the implementation is, outside the spec's part, a reachable state of the
  composite;
- `srefine_project`: the spec's part of every reachable state of the composite is a reachable state of the spec;
- `srefines`: so every reachable state of the implementation is related, by the relation, to a reachable state of the
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

def readsNone (V MS : List Nat) (c : C) : Bool := avoids V c && avoidsMaps MS c
def readsNoneE (V MS : List Nat) (e : E) : Bool := avoidsE V e && avoidsMapsE MS e

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

-- Read where `then` reads, a condition that reads no primed name is the condition before the step.
theorem unprimed_evalC {pr pm : List (Nat × Nat)} {c : C} (hv : avoids (pr.map (·.2)) c = true) (hm : avoidsMaps (pm.map (·.2)) c = true)
    (ρ ρ' : Nat → Nat) (M M' : Nat → Nat → Nat) : evalC (primed pr ρ' ρ) (primedMaps pm M' M) c = evalC ρ M c := by
  rw [congrC _ ρ _ c (fun i hi => by
    simp only [primed]
    rw [lookup_none (fun q hq => by simp only [beq_eq_false_iff_ne]; intro he; exact avoids_occ hv hi (by rw [← he]; exact List.mem_map_of_mem hq))])]
  exact congrMC ρ _ M c (fun mp hmp => by
    funext k; simp only [primedMaps]
    rw [lookup_none (fun q hq => by simp only [beq_eq_false_iff_ne]; intro he; exact avoidsMaps_occ hm hmp (by rw [← he]; exact List.mem_map_of_mem hq))])


/-! Refinements -/

open Classical

structure SRefined where
  impl : SMachine
  spec : SMachine
  wit : List (Nat × E)
  stutter : C


def SRefined.base (r : SRefined) : Refined := ⟨r.impl.f, r.spec.f, r.wit, r.stutter⟩
def SRefined.full (r : SRefined) : SMachine :=
  ⟨r.base.full, r.impl.carried,
   r.impl.every ++ r.spec.every.map (fun w => (w.1, w.2.1, E.ite r.stutter (.get w.1 (.var w.2.1)) (substE r.wit w.2.2))),
   r.impl.qflags ++ r.spec.qflags.map (fun q => (q.1, q.2.1, substC r.wit q.2.2)),
   r.impl.wits ++ r.spec.wits, []⟩
def SRefined.allowed (r : SRefined) : C := inlineC r.full.f.flags (.or r.stutter (substC r.wit r.spec.f.m.assume))

theorem sfull_inputs (r : SRefined) : r.full.f.m.inputs = r.impl.f.m.inputs := rfl
theorem sfull_carried (r : SRefined) : r.full.carried = r.impl.carried := rfl
theorem sfull_flags (r : SRefined) : r.full.f.flags = r.impl.f.flags ++ r.spec.f.flags.map (fun p => (p.1, substC r.wit p.2)) := rfl
theorem sfull_qflags (r : SRefined) : r.full.qflags = r.impl.qflags ++ r.spec.qflags.map (fun q => (q.1, q.2.1, substC r.wit q.2.2)) := rfl
theorem sfull_every (r : SRefined) : r.full.every = r.impl.every ++ r.spec.every.map (fun w => (w.1, w.2.1, E.ite r.stutter (.get w.1 (.var w.2.1)) (substE r.wit w.2.2))) := rfl
theorem sfull_step (r : SRefined) : r.full.f.m.step = r.impl.f.m.step ++ r.spec.f.m.step.map (fun p => (p.1, .ite r.stutter (.var p.1) (substE r.wit p.2))) := rfl
theorem sfull_writes (r : SRefined) : r.full.f.m.writes = r.impl.f.m.writes ++ r.spec.f.m.writes.map (fun w =>
    (w.1, substE r.wit w.2.1, .ite r.stutter (.get w.1 (substE r.wit w.2.1)) (substE r.wit w.2.2))) := rfl
theorem sfull_init (r : SRefined) : r.full.f.m.init = r.impl.f.m.init ++ r.spec.f.m.init := rfl
theorem sfull_maps0 (r : SRefined) : r.full.f.m.maps0 = r.impl.f.m.maps0 ++ r.spec.f.m.maps0 := rfl
theorem sfull_assume (r : SRefined) : r.full.f.m.assume = r.impl.f.m.assume := rfl
theorem sfull_pre (r : SRefined) : r.full.f.m.pre = r.impl.f.m.pre := rfl

-- The implementation's names and maps (its own, and those only it carries); the spec's; where the spec's state and the
-- composite's may differ; what the witness and `stutter` may not read.
def SRefined.IV (r : SRefined) : List Nat := r.impl.f.m.inputs ++ r.impl.f.m.init.map (·.1) ++ r.impl.f.m.step.map (·.1) ++ flagVars r.impl.f.flags ++ r.impl.qVars ++ bkeys r.impl
def SRefined.IO (r : SRefined) : List Nat := r.impl.f.m.maps0.map (·.1) ++ r.impl.f.m.writes.map (·.1) ++ r.impl.every.map (·.1)
def SRefined.IM (r : SRefined) : List Nat := r.IO ++ r.impl.carried.filter (fun mp => !r.spec.carried.contains mp)
def SRefined.SV (r : SRefined) : List Nat := r.spec.f.m.init.map (·.1) ++ r.spec.f.m.step.map (·.1) ++ flagVars r.spec.f.flags ++ r.spec.qVars ++ bkeys r.spec
def SRefined.SM (r : SRefined) : List Nat := r.spec.f.m.maps0.map (·.1) ++ r.spec.f.m.writes.map (·.1) ++ r.spec.every.map (·.1)
def SRefined.X (r : SRefined) : List Nat := r.IV ++ flagVars r.spec.f.flags ++ r.spec.qVars ++ r.spec.f.m.inputs
def SRefined.W (r : SRefined) : List Nat := flagVars r.impl.f.flags ++ flagVars r.spec.f.flags ++ r.spec.f.m.inputs ++ r.impl.qVars ++ r.spec.qVars ++ bkeys r.spec

def srImplOk (r : SRefined) : Bool :=
  readsNone r.SV r.SM r.impl.f.m.pre && readsNone r.SV r.SM r.impl.f.m.assume
    && r.impl.f.flags.all (fun p => readsNone r.SV r.SM p.2) && r.impl.f.m.step.all (fun p => readsNoneE r.SV r.SM p.2)
    && r.impl.f.m.init.all (fun p => readsNoneE r.SV r.SM p.2)
    && r.impl.f.m.writes.all (fun w => readsNoneE r.SV r.SM w.2.1 && readsNoneE r.SV r.SM w.2.2)
    && r.impl.every.all (fun w => readsNoneE r.SV r.SM w.2.2) && r.impl.qflags.all (fun q => readsNone r.SV r.SM q.2.2)
def srSpecOk (r : SRefined) : Bool :=
  readsNone r.IV r.IM r.spec.f.m.assume && r.spec.f.flags.all (fun p => readsNone (r.IV ++ flagVars r.spec.f.flags) r.IM p.2)
    && r.spec.f.m.step.all (fun p => readsNoneE r.IV r.IM p.2) && r.spec.f.m.init.all (fun p => readsNoneE (r.IV ++ r.spec.f.m.inputs) r.IM p.2)
    && r.spec.f.m.writes.all (fun w => readsNoneE r.IV r.IM w.2.1 && readsNoneE r.IV r.IM w.2.2)
    && r.spec.every.all (fun w => readsNoneE r.IV r.IM w.2.2)
    && r.spec.qflags.all (fun q => readsNone (r.IV ++ flagVars r.spec.f.flags ++ r.spec.qVars) r.IM q.2.2)
    && readsNone (r.X ++ r.SV) r.IM r.spec.f.m.pre && !readsC r.spec.f.m.pre
def srNamesOk (r : SRefined) : Bool :=
  r.SV.all (fun v => !r.IV.contains v) && r.spec.f.m.inputs.all (fun v => !(r.IV ++ r.SV).contains v)
    && r.SM.all (fun mp => !r.IM.contains mp) && r.spec.carried.all (fun mp => r.impl.carried.contains mp)
    && r.impl.carried.all (fun mp => !(r.IO ++ r.SM).contains mp)
    && r.wit.all (fun p => r.spec.f.m.inputs.contains p.1 && avoidsE r.W p.2) && avoids r.W r.stutter
    && r.impl.facts.isEmpty && r.spec.facts.isEmpty
def srOk (r : SRefined) : Bool := srImplOk r && srSpecOk r && srNamesOk r

theorem srImpl_parts {r : SRefined} (h : srImplOk r = true) :
    readsNone r.SV r.SM r.impl.f.m.pre = true ∧ readsNone r.SV r.SM r.impl.f.m.assume = true
      ∧ (∀ p ∈ r.impl.f.flags, readsNone r.SV r.SM p.2 = true) ∧ (∀ p ∈ r.impl.f.m.step, readsNoneE r.SV r.SM p.2 = true)
      ∧ (∀ p ∈ r.impl.f.m.init, readsNoneE r.SV r.SM p.2 = true)
      ∧ (∀ w ∈ r.impl.f.m.writes, readsNoneE r.SV r.SM w.2.1 = true ∧ readsNoneE r.SV r.SM w.2.2 = true)
      ∧ (∀ w ∈ r.impl.every, readsNoneE r.SV r.SM w.2.2 = true) ∧ (∀ q ∈ r.impl.qflags, readsNone r.SV r.SM q.2.2 = true) := by
  simp only [srImplOk, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem srSpec_parts {r : SRefined} (h : srSpecOk r = true) :
    readsNone r.IV r.IM r.spec.f.m.assume = true ∧ (∀ p ∈ r.spec.f.flags, readsNone (r.IV ++ flagVars r.spec.f.flags) r.IM p.2 = true)
      ∧ (∀ p ∈ r.spec.f.m.step, readsNoneE r.IV r.IM p.2 = true) ∧ (∀ p ∈ r.spec.f.m.init, readsNoneE (r.IV ++ r.spec.f.m.inputs) r.IM p.2 = true)
      ∧ (∀ w ∈ r.spec.f.m.writes, readsNoneE r.IV r.IM w.2.1 = true ∧ readsNoneE r.IV r.IM w.2.2 = true)
      ∧ (∀ w ∈ r.spec.every, readsNoneE r.IV r.IM w.2.2 = true)
      ∧ (∀ q ∈ r.spec.qflags, readsNone (r.IV ++ flagVars r.spec.f.flags ++ r.spec.qVars) r.IM q.2.2 = true)
      ∧ readsNone (r.X ++ r.SV) r.IM r.spec.f.m.pre = true ∧ readsC r.spec.f.m.pre = false := by
  simp only [srSpecOk, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem srNames_parts {r : SRefined} (h : srNamesOk r = true) :
    (∀ v ∈ r.SV, v ∉ r.IV) ∧ (∀ v ∈ r.spec.f.m.inputs, v ∉ r.IV ++ r.SV) ∧ (∀ mp ∈ r.SM, mp ∉ r.IM)
      ∧ (∀ mp ∈ r.spec.carried, mp ∈ r.impl.carried) ∧ (∀ mp ∈ r.impl.carried, mp ∉ r.IO ++ r.SM)
      ∧ (∀ p ∈ r.wit, p.1 ∈ r.spec.f.m.inputs ∧ avoidsE r.W p.2 = true) ∧ avoids r.W r.stutter = true
      ∧ r.impl.facts = [] ∧ r.spec.facts = [] := by
  simp only [srNamesOk, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨fun v hv hm => ?_, fun v hv hm => ?_, fun mp hm hm' => ?_, fun mp hm => List.contains_iff_mem.mp (h4 mp hm), fun mp hm hm' => ?_,
    fun p hp => ⟨List.contains_iff_mem.mp (h6 p hp).1, (h6 p hp).2⟩, h7, h8, h9⟩
  · have := h1 v hv; rw [List.contains_iff_mem.mpr hm] at this; cases this
  · have := h2 v hv; rw [List.contains_iff_mem.mpr hm] at this; cases this
  · have := h3 mp hm; rw [List.contains_iff_mem.mpr hm'] at this; cases this
  · have := h5 mp hm; rw [List.contains_iff_mem.mpr hm'] at this; cases this

/-! The implementation's runs, inside the composite's -/

section slift
variable (r : SRefined) (hok : srOk r = true)
include hok

theorem sr_impl : srImplOk r = true := by simp only [srOk, Bool.and_eq_true] at hok; exact hok.1.1
theorem sr_spec : srSpecOk r = true := by simp only [srOk, Bool.and_eq_true] at hok; exact hok.1.2
theorem sr_names : srNamesOk r = true := by simp only [srOk, Bool.and_eq_true] at hok; exact hok.2

-- One step of the composite from a state that agrees with the implementation's outside the spec's part, with the same
-- request: allowed alike, to states that still agree.
theorem srefine_step {ρ ρc : Nat → Nat} {M Mc : Nat → Nat → Nat} (hag : Agree r.SV ρc ρ) (hmag : ∀ mp, mp ∉ r.SM → Mc mp = M mp)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    evalC (sView r.full ρc Mc ι κ).1 (sView r.full ρc Mc ι κ).2 r.full.f.m.assume = evalC (sView r.impl ρ M ι κ).1 (sView r.impl ρ M ι κ).2 r.impl.f.m.assume
      ∧ Agree r.SV (sNext r.full ρc Mc ι κ).1 (sNext r.impl ρ M ι κ).1
      ∧ ∀ mp, mp ∉ r.SM → (sNext r.full ρc Mc ι κ).2 mp = (sNext r.impl ρ M ι κ).2 mp := by
  obtain ⟨_, ha, hf, hs, _, hw, he, hq⟩ := srImpl_parts (sr_impl r hok)
  have hN : ∀ mp, mp ∉ r.SM → withCarried r.full Mc κ mp = withCarried r.impl M κ mp := fun mp hmp => by
    show (if r.impl.carried.contains mp = true then κ mp else Mc mp) = (if r.impl.carried.contains mp = true then κ mp else M mp)
    by_cases hc : r.impl.carried.contains mp = true
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]; exact hmag mp hmp
  have hX : Agree r.SV (withInputs r.full.f.m.inputs ρc ι) (withInputs r.impl.f.m.inputs ρ ι) := fun i hi => by
    rw [sfull_inputs]; simp only [withInputs]; split
    · rfl
    · exact hag i hi
  -- The quantified flags: the composite's decide the implementation's alike, outside the spec's names.
  have hQ : Agree r.SV (decideQ r.full (withInputs r.full.f.m.inputs ρc ι) (withCarried r.full Mc κ))
      (decideQ r.impl (withInputs r.impl.f.m.inputs ρ ι) (withCarried r.impl M κ)) := by
    intro v hv
    rw [decideQ_of, decideQ_of, sfull_qflags, lookup_append]
    cases hl : lookup (fun q => q.1 == v) r.impl.qflags with
    | some q =>
      have hrd := hq q (lookup_some hl).1
      exact ite_all_congr (fun i hi _ => hX i (avoids_occ (rn_v hrd) hi)) (fun mp hmp => hN mp (avoidsMaps_occ (rn_m hrd) hmp))
    | none =>
      have hn : lookup (fun q => q.1 == v) (r.spec.qflags.map (fun q => (q.1, q.2.1, substC r.wit q.2.2))) = none :=
        lookup_none (fun q hq' => by
          simp only [beq_eq_false_iff_ne]; intro hqv
          obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq'
          exact hv (by simp only [SRefined.SV, SMachine.qVars, List.mem_append]; left; right; rw [← hqv]; exact List.mem_map.mpr ⟨q0, hq0, rfl⟩))
      simp only [hn]
      exact hX v hv
  -- The plain flags, likewise.
  have hD : Agree r.SV (decideFlags r.full.f.flags (decideQ r.full (withInputs r.full.f.m.inputs ρc ι) (withCarried r.full Mc κ)) (withCarried r.full Mc κ))
      (decideFlags r.impl.f.flags (decideQ r.impl (withInputs r.impl.f.m.inputs ρ ι) (withCarried r.impl M κ)) (withCarried r.impl M κ)) := by
    intro i hi
    have hif : i ∉ flagVars (r.spec.f.flags.map (fun p => (p.1, substC r.wit p.2))) := fun h' => hi (by
      simp only [flagVars, List.map_map] at h'; simp only [SRefined.SV, List.mem_append]; left; left; right
      simpa [flagVars, Function.comp_def] using h')
    rw [sfull_flags, decideFlags_of, decideFlags_of, flagOf_append_left hif]
    cases hfo : flagOf r.impl.f.flags i with
    | none => exact hQ i hi
    | some c =>
      obtain ⟨p, hp, rfl⟩ := flagOf_some hfo
      simp only
      rw [congrMC _ _ _ _ (fun mp hmp => hN mp (avoidsMaps_occ (rn_m (hf p hp)) hmp)),
        congrC _ _ _ _ (fun j hj => hQ j (avoids_occ (rn_v (hf p hp)) hj))]
  refine ⟨?_, fun i hi => ?_, fun mp hmp => ?_⟩
  · simp only [sView]
    rw [sfull_assume, congrMC _ _ _ _ (fun mp hmp => hN mp (avoidsMaps_occ (rn_m ha) hmp)), congrC _ _ _ _ (fun j hj => hD j (avoids_occ (rn_v ha) hj))]
  · simp only [sNext, sView]
    rw [sfull_step]
    have hit : i ∉ (r.spec.f.m.step.map (fun p => (p.1, E.ite r.stutter (.var p.1) (substE r.wit p.2)))).map (·.1) := fun h' => hi (by
      simp only [List.map_map] at h'; simp only [SRefined.SV, List.mem_append]; left; left; left; right; simpa [Function.comp_def] using h')
    rw [applyS_append_other hit]
    simp only [applyS]
    cases hst : assoc r.impl.f.m.step i with
    | none => exact hD i hi
    | some e =>
      have hm : (i, e) ∈ r.impl.f.m.step := by
        simp only [assoc, Option.map_eq_some_iff] at hst
        obtain ⟨q, hq', rfl⟩ := hst
        obtain ⟨hqm, hqv⟩ := lookup_some hq'
        simp only [beq_iff_eq] at hqv; rw [← hqv]; exact hqm
      dsimp only
      rw [congrME _ _ _ e (fun mp hmp => hN mp (avoidsMapsE_occ (rnE_m (hs (i, e) hm)) hmp)),
        congrE _ _ _ e (fun j hj => hD j (avoidsE_occ (rnE_v (hs (i, e) hm)) hj))]
  · funext key
    simp only [sNext, sView, everyMaps]
    rw [sfull_every, lookup_append]
    cases hl : lookup (fun w => w.1 == mp) r.impl.every with
    | some w =>
      have hrd := he w (lookup_some hl).1
      simp only
      rw [congrME _ _ _ w.2.2 (fun mp' h => hN mp' (avoidsMapsE_occ (rnE_m hrd) h)),
        congrE _ _ _ w.2.2 (fun j hj => upd_agree hD w.2.1 key j (avoidsE_occ (rnE_v hrd) hj))]
    | none =>
      have hn : lookup (fun w => w.1 == mp) (r.spec.every.map (fun w => (w.1, w.2.1, E.ite r.stutter (.get w.1 (.var w.2.1)) (substE r.wit w.2.2)))) = none :=
        lookup_none (fun w hw' => by
          simp only [beq_eq_false_iff_ne]; intro he'
          obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw'
          exact hmp (by simp only [SRefined.SM, List.mem_append]; right; rw [← he']; exact List.mem_map.mpr ⟨w0, hw0, rfl⟩))
      simp only [hn]
      have hwm : lookup (fun w : Nat × E × E => w.1 == mp) (r.spec.f.m.writes.map (fun w =>
          (w.1, substE r.wit w.2.1, E.ite r.stutter (.get w.1 (substE r.wit w.2.1)) (substE r.wit w.2.2)))) = none :=
        lookup_none (fun w hw' => by
          simp only [beq_eq_false_iff_ne]; intro he'
          obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw'
          exact hmp (by simp only [SRefined.SM, List.mem_append]; left; right; rw [← he']; exact List.mem_map.mpr ⟨w0, hw0, rfl⟩))
      simp only [writeMaps]
      rw [sfull_writes, lookup_append]
      cases hl2 : lookup (fun w => w.1 == mp) r.impl.f.m.writes with
      | none => simp only [hwm]; exact congrFun (hN mp hmp) key
      | some w =>
        obtain ⟨h1, h2⟩ := hw w (lookup_some hl2).1
        simp only
        rw [congrME _ _ _ w.2.1 (fun mp' h => hN mp' (avoidsMapsE_occ (rnE_m h1) h)), congrE _ _ _ w.2.1 (fun j hj => hD j (avoidsE_occ (rnE_v h1) hj)),
          congrME _ _ _ w.2.2 (fun mp' h => hN mp' (avoidsMapsE_occ (rnE_m h2) h)), congrE _ _ _ w.2.2 (fun j hj => hD j (avoidsE_occ (rnE_v h2) hj)), hN mp hmp]

/-- Every reachable state of the implementation is, outside the spec's part, a reachable state of the composite. -/
theorem srefine_lift (hmo : distinct (r.spec.f.m.maps0.map (·.1)) = true) :
    ∀ {ρ M}, SReach r.impl ρ M → ∃ ρc Mc, SReach r.full ρc Mc ∧ Agree r.SV ρc ρ ∧ ∀ mp, mp ∉ r.SM → Mc mp = M mp := by
  obtain ⟨hp, _, _, _, hi, _⟩ := srImpl_parts (sr_impl r hok)
  obtain ⟨_, _, hsm, _⟩ := srNames_parts (sr_names r hok)
  intro ρ M hr
  induction hr with
  | start ρ M hM h0 _ =>
    let Mc : Nat → Nat → Nat := fun mp => match lookup (fun p => p.1 == mp) r.spec.f.m.maps0 with
      | some p => fun _ => p.2
      | none => M mp
    have hMc : ∀ mp, mp ∉ r.SM → Mc mp = M mp := fun mp hmp => by
      simp only [Mc]
      rw [lookup_none (fun p hp' => by
        simp only [beq_eq_false_iff_ne]; intro he
        exact hmp (by simp only [SRefined.SM, List.mem_append]; left; left; rw [← he]; exact List.mem_map_of_mem hp'))]
    have hpre : evalC ρ Mc r.full.f.m.pre = true := by
      rw [sfull_pre, congrMC _ Mc M _ (fun mp hmp => hMc mp (avoidsMaps_occ (rn_m hp) hmp))]; exact h0
    have hstart : StartMaps r.full.f.m Mc := by
      intro p hp' key
      rw [sfull_maps0] at hp'
      rcases List.mem_append.mp hp' with hp' | hp'
      · have hn : p.1 ∉ r.SM := fun h' => hsm p.1 h' (by
          simp only [SRefined.IM, SRefined.IO, List.mem_append]; left; left; left; exact List.mem_map_of_mem hp')
        rw [hMc p.1 hn]; exact hM p hp' key
      · have hl : lookup (fun q => q.1 == p.1) r.spec.f.m.maps0 = some p := lookup_unique1 hmo hp'
        simp only [Mc, hl]
    have hfacts : ∀ l ∈ r.full.facts, l.Holds ρ Mc := fun l hl => by simp [SRefined.full] at hl
    refine ⟨_, Mc, SReach.start ρ Mc hstart hpre hfacts, fun i hi' => ?_, hMc⟩
    show applyS (r.impl.f.m.init ++ r.spec.f.m.init) ρ Mc i = applyS r.impl.f.m.init ρ M i
    rw [applyS_append_other (by
      intro h'; apply hi'; simp only [SRefined.SV, List.mem_append]; left; left; left; left; exact h')]
    simp only [applyS]
    cases hst : assoc r.impl.f.m.init i with
    | none => rfl
    | some e =>
      have hm : (i, e) ∈ r.impl.f.m.init := by
        simp only [assoc, Option.map_eq_some_iff] at hst
        obtain ⟨q, hq, rfl⟩ := hst
        obtain ⟨hqm, hqv⟩ := lookup_some hq
        simp only [beq_iff_eq] at hqv; rw [← hqv]; exact hqm
      exact congrME _ Mc M e (fun mp hmp => hMc mp (avoidsMapsE_occ (rnE_m (hi (i, e) hm)) hmp))
  | step ρ M ι κ _ ha ih =>
    obtain ⟨ρc, Mc, hrc, hag, hmag⟩ := ih
    obtain ⟨hA, hS, hW⟩ := srefine_step r hok hag hmag ι κ
    exact ⟨_, _, SReach.step ρc Mc ι κ hrc (by rw [hA]; exact ha), hS, hW⟩
end slift

/-! The spec's part of the composite's runs -/

theorem lookup_qmap (l : List (Nat × Nat × C)) (g : Nat × Nat × C → C) (v : Nat) :
    lookup (fun q : Nat × Nat × C => q.1 == v) (l.map (fun q => (q.1, q.2.1, g q))) = (lookup (fun q : Nat × Nat × C => q.1 == v) l).map (fun q => (q.1, q.2.1, g q)) := by
  rw [lookup_map_pred]
theorem lookup_emap (l : List (Nat × Nat × E)) (g : Nat × Nat × E → E) (v : Nat) :
    lookup (fun w : Nat × Nat × E => w.1 == v) (l.map (fun w => (w.1, w.2.1, g w))) = (lookup (fun w : Nat × Nat × E => w.1 == v) l).map (fun w => (w.1, w.2.1, g w)) := by
  rw [lookup_map_pred]

theorem sView_snd (s : SMachine) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    (sView s ρ M ι κ).2 = withCarried s M κ := rfl

section sproject
variable (r : SRefined) (hok : srOk r = true)
include hok

-- The maps the spec reads: alike in its view and the composite's.
theorem sr_maps {M Ms : Nat → Nat → Nat} (hmag : ∀ mp, mp ∉ r.IM → mp ∉ r.spec.carried → Ms mp = M mp) (κ : Nat → Nat → Nat) :
    ∀ mp, mp ∉ r.IM → withCarried r.spec Ms κ mp = withCarried r.full M κ mp := by
  obtain ⟨_, _, _, hcar, _⟩ := srNames_parts (sr_names r hok)
  intro mp hmp
  show (if r.spec.carried.contains mp = true then κ mp else Ms mp) = (if r.impl.carried.contains mp = true then κ mp else M mp)
  by_cases hs : r.spec.carried.contains mp = true
  · rw [if_pos hs, if_pos (List.contains_iff_mem.mpr (hcar mp (List.contains_iff_mem.mp hs)))]
  · have hi : ¬ r.impl.carried.contains mp = true := fun hc => hmp (by
      simp only [SRefined.IM, List.mem_append, List.mem_filter]; right; exact ⟨List.contains_iff_mem.mp hc, by simpa using hs⟩)
    rw [if_neg hs, if_neg hi]
    exact hmag mp hmp (fun h' => hs (List.contains_iff_mem.mpr h'))

theorem sr_W {v : Nat} (hv : v ∈ flagVars r.full.f.flags ∨ v ∈ r.full.qVars) : v ∈ r.W := by
  simp only [sfull_flags, flagVars, List.map_append, List.map_map, SMachine.qVars, sfull_qflags, List.mem_append] at hv
  simp only [SRefined.W, SMachine.qVars, flagVars, List.mem_append]
  rcases hv with (h | h) | (h | h)
  · left; left; left; left; left; exact h
  · left; left; left; left; right; simpa [Function.comp_def] using h
  · left; left; right; exact h
  · left; right; simpa [Function.comp_def] using h

-- A term the witness has, read in the composite's view, before its flags or with a key set: alike.
theorem sr_witE {ρ : Nat → Nat} {M : Nat → Nat → Nat} (ι : Nat → Nat) (κ : Nat → Nat → Nat) {e : E} (he : avoidsE r.W e = true) :
    evalE (decideFlags r.full.f.flags (decideQ r.full (withInputs r.full.f.m.inputs ρ ι) (withCarried r.full M κ)) (withCarried r.full M κ)) (withCarried r.full M κ) e
      = evalE (withInputs r.full.f.m.inputs ρ ι) (withCarried r.full M κ) e := by
  apply congrE; intro j hj
  have hjW := avoidsE_occ he hj
  rw [decide_other (fun h' => hjW (sr_W r hok (Or.inl h'))), decideQ_other (fun h' => hjW (sr_W r hok (Or.inr h')))]

theorem sr_wit_upd {X : Nat → Nat} {N : Nat → Nat → Nat} {e : E} (he : avoidsE r.W e = true) {k : Nat} (hk : k ∈ bkeys r.spec) (key : Nat) :
    evalE (upd X k key) N e = evalE X N e := by
  apply congrE; intro j hj
  simp only [upd]; split
  · rename_i h; subst h; exact absurd (by simp only [SRefined.W, List.mem_append]; right; exact hk) (avoidsE_occ he hj)
  · rfl

-- The witness's domain: spec inputs.
theorem sr_wdom {i : Nat} (hi : i ∉ r.spec.f.m.inputs) : i ∉ r.wit.map (·.1) := fun h' => by
  obtain ⟨_, _, _, _, _, hwit, _⟩ := srNames_parts (sr_names r hok)
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h'; exact hi (hwit p hp).1

theorem sr_wit_some {i : Nat} {e : E} (h : assoc r.wit i = some e) : (i, e) ∈ r.wit := by
  simp only [assoc, Option.map_eq_some_iff] at h
  obtain ⟨q, hq, rfl⟩ := h
  obtain ⟨hqm, hqv⟩ := lookup_some hq
  simp only [beq_iff_eq] at hqv; rw [← hqv]; exact hqm

-- The spec's quantified flags, decided over its view (its inputs as the witness reads them), agree with the composite's
-- with the witness put in, outside the implementation's names and the spec's plain flags.
theorem sr_q {ρ σ : Nat → Nat} {M Ms : Nat → Nat → Nat} (hag : Agree r.X σ ρ) (hmag : ∀ mp, mp ∉ r.IM → mp ∉ r.spec.carried → Ms mp = M mp)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    Agree (r.IV ++ flagVars r.spec.f.flags)
      (decideQ r.spec (withInputs r.spec.f.m.inputs σ (applyS r.wit (sView r.full ρ M ι κ).1 (withCarried r.full M κ))) (withCarried r.spec Ms κ))
      (applyS r.wit (decideQ r.full (withInputs r.full.f.m.inputs ρ ι) (withCarried r.full M κ)) (withCarried r.full M κ)) := by
  obtain ⟨_, _, _, _, _, _, hsq, _, _⟩ := srSpec_parts (sr_spec r hok)
  obtain ⟨hsv, hsi, _, _, _, hwit, _, _, _⟩ := srNames_parts (sr_names r hok)
  have hN := sr_maps r hok hmag κ
  intro v hv
  have hvI : v ∉ r.IV := fun h' => hv (List.mem_append_left _ h')
  have hvF : v ∉ flagVars r.spec.f.flags := fun h' => hv (List.mem_append_right _ h')
  -- Names of the spec's part are none of the spec's inputs.
  have hSI : ∀ i, i ∈ r.SV → i ∉ r.spec.f.m.inputs := fun i hi h' => hsi i h' (List.mem_append_right _ hi)
  have hIVq : ∀ i, i ∉ r.IV → i ∉ r.impl.qVars := fun i hi h' => hi (by simp only [SRefined.IV, List.mem_append]; left; right; exact h')
  have hIVi : ∀ i, i ∉ r.IV → i ∉ r.impl.f.m.inputs := fun i hi h' => hi (by simp only [SRefined.IV, List.mem_append]; left; left; left; left; left; exact h')
  have hIVf : ∀ i, i ∉ r.IV → i ∉ flagVars r.impl.f.flags := fun i hi h' => hi (by simp only [SRefined.IV, List.mem_append]; left; left; right; exact h')
  have hfull_q : ∀ i, i ∉ r.impl.qVars → i ∉ r.spec.qVars → i ∉ r.full.qVars := fun i h1 h2 h' => by
    simp only [SMachine.qVars, sfull_qflags, List.map_append, List.map_map, List.mem_append] at h'
    rcases h' with h' | h'
    · exact h1 h'
    · exact h2 (by simpa [SMachine.qVars, Function.comp_def] using h')
  have hfull_f : ∀ i, i ∉ flagVars r.impl.f.flags → i ∉ flagVars r.spec.f.flags → i ∉ flagVars r.full.f.flags := fun i h1 h2 h' => by
    simp only [sfull_flags, flagVars, List.map_append, List.map_map, List.mem_append] at h'
    rcases h' with h' | h'
    · exact h1 h'
    · exact h2 (by simpa [flagVars, Function.comp_def] using h')
  -- The spec inputs as the witness reads them: in the composite's view, or before its flags; the same.
  have hιs : ∀ i, i ∈ r.spec.f.m.inputs → applyS r.wit (sView r.full ρ M ι κ).1 (withCarried r.full M κ) i
      = applyS r.wit (decideQ r.full (withInputs r.full.f.m.inputs ρ ι) (withCarried r.full M κ)) (withCarried r.full M κ) i := fun i hi => by
    have hiI : i ∉ r.IV := fun h' => hsi i hi (List.mem_append_left _ h')
    have hiS : i ∉ r.SV := fun h' => hsi i hi (List.mem_append_right _ h')
    have hiF : i ∉ flagVars r.full.f.flags := hfull_f i (hIVf i hiI) (fun h' => hiS (by simp only [SRefined.SV, List.mem_append]; left; left; right; exact h'))
    simp only [applyS, sView]
    cases ha : assoc r.wit i with
    | none => exact decide_other hiF _ _
    | some e =>
      have hm := sr_wit_some r hok ha
      dsimp only
      rw [sr_witE r hok ι κ (hwit _ hm).2]
      exact (congrE _ _ _ e (fun j hj => decideQ_other (fun h' => avoidsE_occ (hwit _ hm).2 hj (sr_W r hok (Or.inr h'))) _ _)).symm
  by_cases hvq : v ∈ r.spec.qVars
  · -- A spec's quantified flag: its body over the spec's view; in the composite, with the witness put in.
    have hvi : v ∉ r.spec.f.m.inputs := hSI v (by simp only [SRefined.SV, List.mem_append]; left; right; exact hvq)
    rw [decideQ_of, applyS_other (sr_wdom r hok hvi), decideQ_of, sfull_qflags, lookup_append]
    have hn : lookup (fun q => q.1 == v) r.impl.qflags = none := lookup_none (fun q hq' => by
      simp only [beq_eq_false_iff_ne]; intro he; exact hIVq v hvI (by rw [← he]; exact List.mem_map_of_mem hq'))
    simp only [hn, lookup_qmap]
    cases hl : lookup (fun q => q.1 == v) r.spec.qflags with
    | none => exact absurd hvq (fun h' => by obtain ⟨q, hq, hqv⟩ := List.mem_map.mp h'; have := lookup_none_all hl q hq; simp [hqv] at this)
    | some q =>
      have hqm := (lookup_some hl).1
      have hrd := hsq q hqm
      have hk : q.2.1 ∈ bkeys r.spec := by simp only [bkeys, List.mem_append]; right; exact List.mem_map_of_mem hqm
      simp only [Option.map_some]
      have hc : (∀ key, holdsC (upd (withInputs r.full.f.m.inputs ρ ι) q.2.1 key) (withCarried r.full M κ) (substC r.wit q.2.2))
          ↔ (∀ key, holdsC (applyS r.wit (upd (withInputs r.full.f.m.inputs ρ ι) q.2.1 key) (withCarried r.full M κ)) (withCarried r.full M κ) q.2.2) := by
        apply forall_congr'; intro key; rw [← evalC_iff, ← evalC_iff, subst_evalC]
      rw [show (if ∀ key, holdsC (upd (withInputs r.full.f.m.inputs ρ ι) q.2.1 key) (withCarried r.full M κ) (substC r.wit q.2.2) then 1 else 0)
          = (if ∀ key, holdsC (applyS r.wit (upd (withInputs r.full.f.m.inputs ρ ι) q.2.1 key) (withCarried r.full M κ)) (withCarried r.full M κ) q.2.2 then 1 else 0) by
        simp only [hc]]
      have hkdom : q.2.1 ∉ r.wit.map (·.1) := sr_wdom r hok (hSI _ (by simp only [SRefined.SV, List.mem_append]; right; exact hk))
      -- Both sides as one condition over every key: compare the states they read the body at.
      have hall : ∀ key, evalC (upd (withInputs r.spec.f.m.inputs σ (applyS r.wit (sView r.full ρ M ι κ).1 (withCarried r.full M κ))) q.2.1 key) (withCarried r.spec Ms κ) q.2.2
          = evalC (applyS r.wit (upd (withInputs r.full.f.m.inputs ρ ι) q.2.1 key) (withCarried r.full M κ)) (withCarried r.full M κ) q.2.2 := by
        intro key
        rw [congrMC _ _ (withCarried r.full M κ) _ (fun mp hmp => hN mp (avoidsMaps_occ (rn_m hrd) hmp))]
        apply congrC; intro i hi
        have hiR := avoids_occ (rn_v hrd) hi
        simp only [List.mem_append, not_or] at hiR
        obtain ⟨⟨hiI, hiF⟩, hiQ⟩ := hiR
        by_cases hik : i = q.2.1
        · subst hik; simp only [upd, if_true]; rw [applyS_other hkdom]; simp [upd]
        · simp only [upd, hik, if_false]
          by_cases hii : i ∈ r.spec.f.m.inputs
          · simp only [withInputs, List.contains_iff_mem.mpr hii, if_true]
            rw [hιs i hii]
            simp only [applyS]
            cases ha : assoc r.wit i with
            | none => simp only [upd, hik, if_false]; exact decideQ_other (fun h' => hfull_q i (hIVq i hiI) hiQ h') _ _
            | some e =>
              have hm := sr_wit_some r hok ha
              dsimp only
              rw [sr_wit_upd r hok (hwit _ hm).2 hk]
              exact congrE _ _ _ e (fun j hj => decideQ_other (fun h' => avoidsE_occ (hwit _ hm).2 hj (sr_W r hok (Or.inr h'))) _ _)
          · rw [withInputs_other hii, applyS_other (sr_wdom r hok hii)]
            simp only [upd, hik, if_false]
            rw [sfull_inputs, withInputs_other (hIVi i hiI)]
            exact hag i (by simp only [SRefined.X, List.mem_append, not_or]; exact ⟨⟨⟨hiI, hiF⟩, hiQ⟩, hii⟩)
      simp only [show (∀ key, holdsC (upd (withInputs r.spec.f.m.inputs σ (applyS r.wit (sView r.full ρ M ι κ).1 (withCarried r.full M κ))) q.2.1 key) (withCarried r.spec Ms κ) q.2.2)
          ↔ (∀ key, holdsC (applyS r.wit (upd (withInputs r.full.f.m.inputs ρ ι) q.2.1 key) (withCarried r.full M κ)) (withCarried r.full M κ) q.2.2) from
        forall_congr' (fun key => by rw [← evalC_iff, ← evalC_iff, hall key])]
  · rw [decideQ_other hvq]
    by_cases hvi : v ∈ r.spec.f.m.inputs
    · simp only [withInputs, List.contains_iff_mem.mpr hvi, if_true]
      exact hιs v hvi
    · rw [withInputs_other hvi, applyS_other (sr_wdom r hok hvi), decideQ_other (hfull_q v (hIVq v hvI) hvq), sfull_inputs, withInputs_other (hIVi v hvI)]
      exact hag v (by simp only [SRefined.X, List.mem_append, not_or]; exact ⟨⟨⟨hvI, hvF⟩, hvq⟩, hvi⟩)

-- The spec's view of a step agrees with the composite's with the witness put in, outside the implementation's names.
theorem sr_view {ρ σ : Nat → Nat} {M Ms : Nat → Nat → Nat} (hag : Agree r.X σ ρ) (hmag : ∀ mp, mp ∉ r.IM → mp ∉ r.spec.carried → Ms mp = M mp)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    Agree r.IV (sView r.spec σ Ms (applyS r.wit (sView r.full ρ M ι κ).1 (withCarried r.full M κ)) κ).1
      (applyS r.wit (sView r.full ρ M ι κ).1 (withCarried r.full M κ)) := by
  obtain ⟨_, hsf, _, _, _, _, _, _, _⟩ := srSpec_parts (sr_spec r hok)
  obtain ⟨hsv, hsi, _, _, _, hwit, _, _, _⟩ := srNames_parts (sr_names r hok)
  have hN := sr_maps r hok hmag κ
  have hQ := sr_q r hok hag hmag ι κ
  simp only [sView] at hQ
  have hIVf : ∀ i, i ∉ r.IV → i ∉ flagVars r.impl.f.flags := fun i hi h' => hi (by simp only [SRefined.IV, List.mem_append]; left; left; right; exact h')
  intro v hv
  simp only [sView]
  by_cases hvf : v ∈ flagVars r.spec.f.flags
  · have hvi : v ∉ r.spec.f.m.inputs := fun h' => hsi v h' (List.mem_append_right _ (by simp only [SRefined.SV, List.mem_append]; left; left; right; exact hvf))
    cases hfo : flagOf r.spec.f.flags v with
    | none => exact absurd hvf (flagOf_none hfo)
    | some c =>
      obtain ⟨p, hp, rfl⟩ := flagOf_some hfo
      have hfull : flagOf r.full.f.flags v = some (substC r.wit p.2) := by
        rw [sfull_flags, flagOf_append_right (hIVf v hv), flagOf_map, hfo]; rfl
      rw [decideFlags_of, hfo, applyS_other (sr_wdom r hok hvi), decideFlags_of, hfull]
      simp only
      rw [subst_evalC, congrMC _ _ (withCarried r.full M κ) _ (fun mp hmp => hN mp (avoidsMaps_occ (rn_m (hsf p hp)) hmp))]
      rw [congrC _ (applyS r.wit (decideQ r.full (withInputs r.full.f.m.inputs ρ ι) (withCarried r.full M κ)) (withCarried r.full M κ)) _ p.2
        (fun j hj => hQ j (avoids_occ (rn_v (hsf p hp)) hj))]
  · rw [decide_other hvf]
    have hX : v ∉ r.IV ++ flagVars r.spec.f.flags := by simp only [List.mem_append, not_or]; exact ⟨hv, hvf⟩
    rw [hQ v hX]
    simp only [applyS]
    cases ha : assoc r.wit v with
    | none =>
      dsimp only
      rw [decide_other (fun h' => by
        simp only [sfull_flags, flagVars, List.map_append, List.map_map, List.mem_append] at h'
        rcases h' with h' | h'
        · exact hIVf v hv h'
        · exact hvf (by simpa [flagVars, Function.comp_def] using h'))]
    | some e =>
      have hm := sr_wit_some r hok ha
      dsimp only
      exact congrE _ _ _ e (fun j hj => (decide_other (fun h' => avoidsE_occ (hwit _ hm).2 hj (sr_W r hok (Or.inl h'))) _ _).symm)

-- A term of the spec, read in the spec's view, is the term with the witness put in, read in the composite's view; with a
-- bound key of the spec set, alike.
theorem sr_term {ρ σ : Nat → Nat} {M Ms : Nat → Nat → Nat} (hag : Agree r.X σ ρ) (hmag : ∀ mp, mp ∉ r.IM → mp ∉ r.spec.carried → Ms mp = M mp)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) {e : E} (he : readsNoneE r.IV r.IM e = true) :
    evalE (sView r.spec σ Ms (applyS r.wit (sView r.full ρ M ι κ).1 (withCarried r.full M κ)) κ).1 (withCarried r.spec Ms κ) e
      = evalE (sView r.full ρ M ι κ).1 (withCarried r.full M κ) (substE r.wit e) := by
  rw [subst_evalE, congrME _ _ (withCarried r.full M κ) e (fun mp hmp => sr_maps r hok hmag κ mp (avoidsMapsE_occ (rnE_m he) hmp))]
  exact congrE _ _ _ e (fun j hj => sr_view r hok hag hmag ι κ j (avoidsE_occ (rnE_v he) hj))

theorem sr_cond {ρ σ : Nat → Nat} {M Ms : Nat → Nat → Nat} (hag : Agree r.X σ ρ) (hmag : ∀ mp, mp ∉ r.IM → mp ∉ r.spec.carried → Ms mp = M mp)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) {c : C} (hc : readsNone r.IV r.IM c = true) :
    evalC (sView r.spec σ Ms (applyS r.wit (sView r.full ρ M ι κ).1 (withCarried r.full M κ)) κ).1 (withCarried r.spec Ms κ) c
      = evalC (sView r.full ρ M ι κ).1 (withCarried r.full M κ) (substC r.wit c) := by
  rw [subst_evalC, congrMC _ _ (withCarried r.full M κ) c (fun mp hmp => sr_maps r hok hmag κ mp (avoidsMaps_occ (rn_m hc) hmp))]
  exact congrC _ _ _ c (fun j hj => sr_view r hok hag hmag ι κ j (avoids_occ (rn_v hc) hj))

theorem sr_term_upd {ρ σ : Nat → Nat} {M Ms : Nat → Nat → Nat} (hag : Agree r.X σ ρ) (hmag : ∀ mp, mp ∉ r.IM → mp ∉ r.spec.carried → Ms mp = M mp)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) {e : E} (he : readsNoneE r.IV r.IM e = true) {k : Nat} (hk : k ∈ bkeys r.spec) (key : Nat) :
    evalE (upd (sView r.spec σ Ms (applyS r.wit (sView r.full ρ M ι κ).1 (withCarried r.full M κ)) κ).1 k key) (withCarried r.spec Ms κ) e
      = evalE (upd (sView r.full ρ M ι κ).1 k key) (withCarried r.full M κ) (substE r.wit e) := by
  obtain ⟨_, hsi, _, _, _, hwit, _, _, _⟩ := srNames_parts (sr_names r hok)
  have hkdom : k ∉ r.wit.map (·.1) := sr_wdom r hok (fun h' => hsi k h' (List.mem_append_right _ (by simp only [SRefined.SV, List.mem_append]; right; exact hk)))
  rw [subst_evalE, congrME _ _ (withCarried r.full M κ) e (fun mp hmp => sr_maps r hok hmag κ mp (avoidsMapsE_occ (rnE_m he) hmp))]
  apply congrE; intro j hj
  by_cases hjk : j = k
  · subst hjk; rw [applyS_other hkdom]; simp [upd]
  · have hv := sr_view r hok hag hmag ι κ j (avoidsE_occ (rnE_v he) hj)
    simp only [upd, hjk, if_false]
    rw [hv]
    simp only [applyS]
    cases ha : assoc r.wit j with
    | none => simp [upd, hjk]
    | some e' =>
      have hm := sr_wit_some r hok ha
      dsimp only
      exact (sr_wit_upd r hok (hwit _ hm).2 hk key).symm

-- A variable none of the names the composite's view sets, nor the spec's: each view reads it as its state does.
theorem sr_plain_full {ρ : Nat → Nat} {M : Nat → Nat → Nat} (ι : Nat → Nat) (κ : Nat → Nat → Nat) {v : Nat} (hv : v ∉ r.X) :
    (sView r.full ρ M ι κ).1 v = ρ v := by
  simp only [SRefined.X, SRefined.IV, List.mem_append, not_or] at hv
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hi, _⟩, _⟩, hf⟩, hq⟩, _⟩, hsf⟩, hsq⟩, _⟩ := hv
  simp only [sView]
  rw [decide_other (fun h' => by
    simp only [sfull_flags, flagVars, List.map_append, List.map_map, List.mem_append] at h'
    rcases h' with h' | h'
    · exact hf h'
    · exact hsf (by simpa [flagVars, Function.comp_def] using h'))]
  rw [decideQ_other (fun h' => by
    simp only [SMachine.qVars, sfull_qflags, List.map_append, List.map_map, List.mem_append] at h'
    rcases h' with h' | h'
    · exact hq h'
    · exact hsq (by simpa [SMachine.qVars, Function.comp_def] using h')), sfull_inputs]
  exact withInputs_other hi ρ ι

theorem sr_plain_spec {σ : Nat → Nat} {Ms : Nat → Nat → Nat} (ι : Nat → Nat) (κ : Nat → Nat → Nat) {v : Nat} (hv : v ∉ r.X) :
    (sView r.spec σ Ms ι κ).1 v = σ v := by
  simp only [SRefined.X, List.mem_append, not_or] at hv
  obtain ⟨⟨⟨_, hsf⟩, hsq⟩, hsi⟩ := hv
  simp only [sView]
  rw [decide_other hsf, decideQ_other hsq]
  exact withInputs_other hsi σ ι

/-- The spec's part of every reachable state of the composite is a reachable state of the spec, given that the spec's
precondition holds at every reachable state of the composite (one of its laws) and that, at every step the composite
takes, the spec stutters or allows the request it is sent (its step law). -/
theorem srefine_project (hpre : ∀ ρ M, SReach r.full ρ M → evalC ρ M r.spec.f.m.pre = true)
    (hallow : ∀ ρ M, SReach r.full ρ M → ∀ ι κ, evalC (sView r.full ρ M ι κ).1 (sView r.full ρ M ι κ).2 r.full.f.m.assume = true →
      evalC (sView r.full ρ M ι κ).1 (sView r.full ρ M ι κ).2 (.or r.stutter (substC r.wit r.spec.f.m.assume)) = true) :
    ∀ {ρ M}, SReach r.full ρ M → ∃ σ Ms, SReach r.spec σ Ms ∧ Agree r.X σ ρ ∧ ∀ mp, mp ∉ r.IM → mp ∉ r.spec.carried → Ms mp = M mp := by
  obtain ⟨hsa, _, hss, _, hsw, hse, _, hsp, _⟩ := srSpec_parts (sr_spec r hok)
  obtain ⟨_, _, _, _, hcarO, _, hst, _, hsfacts⟩ := srNames_parts (sr_names r hok)
  have hIVst : ∀ v, v ∉ r.IV → v ∉ r.impl.f.m.step.map (·.1) := fun v hv h' => hv (by simp only [SRefined.IV, List.mem_append]; left; left; left; right; exact h')
  -- A map of the spec's part, unwritten by the implementation, read where the request carries none: the state's.
  have hNc : ∀ (M : Nat → Nat → Nat) (κ : Nat → Nat → Nat) mp, mp ∉ r.IM → mp ∉ r.spec.carried → withCarried r.full M κ mp = M mp := fun M κ mp h1 h2 => by
    show (if r.impl.carried.contains mp = true then κ mp else M mp) = M mp
    rw [if_neg (fun hc => h1 (by
      simp only [SRefined.IM, List.mem_append, List.mem_filter]; right
      exact ⟨List.contains_iff_mem.mp hc, by simpa [List.contains_iff_mem] using h2⟩))]
  have hIMe : ∀ mp, mp ∉ r.IM → lookup (fun w => w.1 == mp) r.impl.every = none := fun mp h => lookup_none (fun w hw => by
    simp only [beq_eq_false_iff_ne]; intro he; exact h (by simp only [SRefined.IM, SRefined.IO, List.mem_append]; left; right; rw [← he]; exact List.mem_map_of_mem hw))
  have hIMw : ∀ mp, mp ∉ r.IM → lookup (fun w : Nat × E × E => w.1 == mp) r.impl.f.m.writes = none := fun mp h => lookup_none (fun w hw => by
    simp only [beq_eq_false_iff_ne]; intro he; exact h (by simp only [SRefined.IM, SRefined.IO, List.mem_append]; left; left; right; rw [← he]; exact List.mem_map_of_mem hw))
  intro ρ M hr
  induction hr with
  | start ρ M hM h0 _ =>
    have hp0 : evalC ρ M r.spec.f.m.pre = true := by
      have h := hpre _ M (SReach.start ρ M hM h0 (fun l hl => by simp [SRefined.full] at hl))
      have hag0 : ∀ i, occC i r.spec.f.m.pre = true → applyS r.full.f.m.init ρ M i = ρ i := fun i hi => applyS_other (fun h' => by
        apply avoids_occ (rn_v hsp) hi
        rw [sfull_init] at h'
        simp only [List.map_append, List.mem_append] at h'
        rcases h' with h' | h' <;> simp [SRefined.X, SRefined.IV, SRefined.SV, h']) ρ M
      rwa [congrC _ ρ M r.spec.f.m.pre hag0] at h
    have hMs : StartMaps r.spec.f.m M := fun p hp' key => hM p (by rw [sfull_maps0]; exact List.mem_append_right _ hp') key
    refine ⟨_, M, SReach.start ρ M hMs hp0 (fun l hl => by simp [hsfacts] at hl), fun i hi => ?_, fun _ _ _ => rfl⟩
    show applyS r.spec.f.m.init ρ M i = applyS (r.impl.f.m.init ++ r.spec.f.m.init) ρ M i
    rw [applyS_append_right (fun h' => hi (by simp [SRefined.X, SRefined.IV, h']))]
  | step ρ M ι κ hr ha ih =>
    obtain ⟨σ, Ms, hrs, hag, hmag⟩ := ih
    have hA := hallow ρ M hr ι κ ha
    simp only [evalC, Bool.or_eq_true, sView_snd] at hA
    -- The composite's step at a variable of the spec's part: kept where it stutters, the spec's term otherwise.
    have hstepS : ∀ v, v ∉ r.IV → (sNext r.full ρ M ι κ).1 v
        = applyS (r.spec.f.m.step.map (fun p => (p.1, E.ite r.stutter (.var p.1) (substE r.wit p.2)))) (sView r.full ρ M ι κ).1 (withCarried r.full M κ) v :=
      fun v hv => by simp only [sNext]; rw [sfull_step]; exact applyS_append_right (hIVst v hv) _ _
    have hstutK : ∀ k ∈ bkeys r.spec, ∀ key, evalC (upd (sView r.full ρ M ι κ).1 k key) (withCarried r.full M κ) r.stutter
        = evalC (sView r.full ρ M ι κ).1 (withCarried r.full M κ) r.stutter := fun k hk key => by
      apply congrC; intro j hj; simp only [upd]; split
      · rename_i h; subst h; exact absurd (by simp only [SRefined.W, List.mem_append]; right; exact hk) (avoids_occ hst hj)
      · rfl
    by_cases hstut : evalC (sView r.full ρ M ι κ).1 (withCarried r.full M κ) r.stutter = true
    · -- The spec doesn't step: its state is the same, and so is the composite's spec part.
      refine ⟨σ, Ms, hrs, fun v hv => ?_, fun mp hmp hmc => ?_⟩
      · rw [hstepS v (fun h' => hv (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h'))))]
        simp only [applyS]
        cases hl : assoc (r.spec.f.m.step.map (fun p => (p.1, E.ite r.stutter (.var p.1) (substE r.wit p.2)))) v with
        | none => dsimp only; rw [sr_plain_full r hok ι κ hv]; exact hag v hv
        | some e =>
          obtain ⟨q, hq, hqv, rfl⟩ : ∃ q ∈ r.spec.f.m.step, q.1 = v ∧ e = E.ite r.stutter (.var q.1) (substE r.wit q.2) := by
            simp only [assoc, Option.map_eq_some_iff] at hl
            obtain ⟨x, hx, rfl⟩ := hl
            obtain ⟨hxm, hxv⟩ := lookup_some hx
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hxm
            simp only [beq_iff_eq] at hxv
            exact ⟨q, hq, hxv, rfl⟩
          dsimp only
          simp only [evalE, hstut, if_true]
          rw [hqv, sr_plain_full r hok ι κ hv]; exact hag v hv
      · funext key
        rw [hmag mp hmp hmc]
        simp only [sNext, everyMaps, sView_snd]
        rw [sfull_every, lookup_append, hIMe mp hmp]
        simp only [lookup_emap]
        cases hw : lookup (fun w => w.1 == mp) r.spec.every with
        | some w =>
          have hwm := (lookup_some hw).2
          simp only [beq_iff_eq] at hwm
          have hk : w.2.1 ∈ bkeys r.spec := by simp only [bkeys, List.mem_append]; left; exact List.mem_map_of_mem (lookup_some hw).1
          simp only [Option.map_some, evalE]
          rw [hstutK _ hk key]
          simp only [hstut, if_true, upd, hwm, hNc M κ mp hmp hmc]
        | none =>
          simp only [Option.map_none, writeMaps]
          rw [sfull_writes, lookup_append, hIMw mp hmp]
          try dsimp only
          rw [lookup_writes_map]
          cases hw0 : lookup (fun w : Nat × E × E => w.1 == mp) r.spec.f.m.writes with
          | none => simp only [Option.map_none]; exact (congrFun (hNc M κ mp hmp hmc) key).symm
          | some w0 =>
            have hw0m := (lookup_some hw0).2
            simp only [beq_iff_eq] at hw0m
            simp only [Option.map_some, evalE, hstut, if_true, hw0m]
            by_cases hk : key = evalE (sView r.full ρ M ι κ).1 (withCarried r.full M κ) (substE r.wit w0.2.1)
            · rw [if_pos hk, ← hk]; exact (congrFun (hNc M κ mp hmp hmc) _).symm
            · rw [if_neg hk]; exact (congrFun (hNc M κ mp hmp hmc) key).symm
    · -- The spec steps, sent the witness's request, which it allows.
      have hX := hA.resolve_left hstut
      rw [← sr_cond r hok hag hmag ι κ (c := r.spec.f.m.assume) hsa] at hX
      refine ⟨_, _, SReach.step σ Ms _ κ hrs hX, fun v hv => ?_, fun mp hmp hmc => ?_⟩
      · rw [hstepS v (fun h' => hv (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h'))))]
        simp only [sNext, applyS, sView_snd]
        rw [assoc_map_fst]
        cases hl : lookup (fun q => q.1 == v) r.spec.f.m.step with
        | none =>
          have hn : assoc r.spec.f.m.step v = none := by simp only [assoc, hl, Option.map_none]
          rw [hn]; dsimp only
          rw [sr_plain_full r hok ι κ hv, sr_plain_spec r hok _ κ hv]; exact hag v hv
        | some q =>
          have hq := lookup_some hl
          simp only [beq_iff_eq] at hq
          have hn : assoc r.spec.f.m.step v = some q.2 := by simp only [assoc, hl, Option.map_some]
          rw [hn]; dsimp only
          simp only [Option.map_some, evalE, show evalC (sView r.full ρ M ι κ).1 (withCarried r.full M κ) r.stutter = false by simpa using hstut, Bool.false_eq_true, if_false]
          have hm : (v, q.2) ∈ r.spec.f.m.step := by rw [← hq.2]; exact hq.1
          exact sr_term r hok hag hmag ι κ (hss (v, q.2) hm)
      · funext key
        simp only [sNext, everyMaps, sView_snd]
        rw [sfull_every, lookup_append, hIMe mp hmp]
        simp only [lookup_emap]
        cases hw : lookup (fun w => w.1 == mp) r.spec.every with
        | some w =>
          have hk : w.2.1 ∈ bkeys r.spec := by simp only [bkeys, List.mem_append]; left; exact List.mem_map_of_mem (lookup_some hw).1
          simp only [Option.map_some, evalE]
          rw [hstutK _ hk key]
          simp only [show evalC (sView r.full ρ M ι κ).1 (withCarried r.full M κ) r.stutter = false by simpa using hstut, Bool.false_eq_true, if_false]
          exact sr_term_upd r hok hag hmag ι κ (hse w (lookup_some hw).1) hk key
        | none =>
          simp only [Option.map_none, writeMaps]
          rw [sfull_writes, lookup_append, hIMw mp hmp]
          try dsimp only
          rw [lookup_writes_map]
          cases hw0 : lookup (fun w : Nat × E × E => w.1 == mp) r.spec.f.m.writes with
          | none => simp only [Option.map_none]; exact congrFun (sr_maps r hok hmag κ mp hmp) key
          | some w0 =>
            obtain ⟨h1, h2⟩ := hsw w0 (lookup_some hw0).1
            simp only [Option.map_some, evalE, show evalC (sView r.full ρ M ι κ).1 (withCarried r.full M κ) r.stutter = false by simpa using hstut, Bool.false_eq_true, if_false]
            rw [sr_term r hok hag hmag ι κ h1, sr_term r hok hag hmag ι κ h2, sr_maps r hok hmag κ mp hmp]
end sproject

-- The composite's step law: on every request it takes, the spec stutters or allows the request it is sent.
def srStep (r : SRefined) (prime primeMaps : List (Nat × Nat)) (p : SProof) : SKStep :=
  ⟨⟨[trueC], r.allowed, [[]], prime, primeMaps, p.1, (p.2.2.2.2.1, p.2.2.2.2.2.2)⟩, [[]], p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.2.1, []⟩

/-- What a refinement over sets means: with the relation (and the spec's precondition, the j-th law) proven of the
composite, and its step law that the spec stutters or allows every request it is sent, every reachable state of the
implementation is, outside the spec's part, a reachable state of the composite, whose spec part is a reachable state of
the spec, the two related by every law. -/
theorem srefines (r : SRefined) (hok : srOk r = true) (hmo : distinct (r.spec.f.m.maps0.map (·.1)) = true) (ps : List SEntry)
    (hl : checkSMachine r.full ps = true)
    (j : Nat) (hj : (ps[j]?).map (·.law.holds) = some r.spec.f.m.pre ∧ (ps[j]?).map (·.law.key) = some none)
    (prime primeMaps : List (Nat × Nat)) (p : SProof) (hs : checkSKStep r.full ps (srStep r prime primeMaps p) = true)
    (hfresh : avoids (prime.map (·.2)) r.allowed = true ∧ avoidsMaps (primeMaps.map (·.2)) r.allowed = true)
    (hw : avoids r.full.wVars r.allowed = true) (hiq : r.full.f.m.inputs.all (fun i => !r.full.qVars.contains i) = true) :
    ∀ ρ M, SReach r.impl ρ M → ∃ ρc Mc σ Ms, SReach r.full ρc Mc ∧ Agree r.SV ρc ρ ∧ (∀ mp, mp ∉ r.SM → Mc mp = M mp)
      ∧ SReach r.spec σ Ms ∧ Agree r.X σ ρc ∧ (∀ mp, mp ∉ r.IM → mp ∉ r.spec.carried → Ms mp = Mc mp) ∧ ∀ e ∈ ps, e.Holds ρc Mc := by
  have hlaws := smachine_sound r.full ps hl
  have hpre : ∀ ρ M, SReach r.full ρ M → evalC ρ M r.spec.f.m.pre = true := by
    intro ρ M hr
    cases he : ps[j]? with
    | none => simp [he] at hj
    | some e =>
      simp only [he, Option.map_some, Option.some.injEq] at hj
      have h := SEntry.holds_law (hlaws ρ M hr e (List.mem_of_getElem? he))
      unfold MLaw.Holds at h
      rw [hj.2] at h
      simpa [hj.1] using h
  have hiq' : ∀ i, i ∈ r.full.f.m.inputs → i ∉ r.full.qVars := fun i hi hq => by
    simp only [List.all_eq_true, Bool.not_eq_true'] at hiq
    have := hiq i hi; rw [List.contains_iff_mem.mpr hq] at this; cases this
  have hallow : ∀ ρ M, SReach r.full ρ M → ∀ ι κ, evalC (sView r.full ρ M ι κ).1 (sView r.full ρ M ι κ).2 r.full.f.m.assume = true →
      evalC (sView r.full ρ M ι κ).1 (sView r.full ρ M ι κ).2 (.or r.stutter (substC r.wit r.spec.f.m.assume)) = true := by
    intro ρ M hr ι κ hA
    have h := skstep_sound r.full ps _ hl hs ρ M hr (ι, κ) [] rfl ⟨hA, by simp [trueC, evalC, evalE], trivial⟩
    have h' : evalC (primed prime (sNext r.full ρ M ι κ).1 (withExt r.full ρ (sReq r.full ρ M ι κ)))
        (primedMaps primeMaps (sNext r.full ρ M ι κ).2 (withCarried r.full M κ)) r.allowed = true := by
      simpa [srStep, sEnd, sExts, renEnv, renMaps, lookup] using h
    rw [unprimed_evalC hfresh.1 hfresh.2] at h'
    -- The request's extended variables, read as the step reads them: the inputs, and each quantified flag decided.
    have hE : ∀ v, v ∉ r.full.wVars → withExt r.full ρ (sReq r.full ρ M ι κ) v
        = decideQ r.full (withInputs r.full.f.m.inputs ρ ι) (withCarried r.full M κ) v := by
      intro v hv
      simp only [withExt, sReq]
      by_cases hi : v ∈ r.full.f.m.inputs
      · have hext : r.full.extVars.contains v = true := List.contains_iff_mem.mpr (by simp [SMachine.extVars, hi])
        rw [decideQ_other (hiq' v hi)]
        simp only [hext, if_true, List.contains_iff_mem.mpr hi, withInputs]
      · have hin : r.full.f.m.inputs.contains v = false := by simpa [List.contains_iff_mem] using hi
        by_cases hq : v ∈ r.full.qVars
        · have hext : r.full.extVars.contains v = true := List.contains_iff_mem.mpr (by simp [SMachine.extVars, hq])
          obtain ⟨q, hq0, rfl⟩ := List.mem_map.mp hq
          cases hl : lookup (fun q' => q'.1 == q.1) r.full.qflags with
          | none => have := lookup_none_all hl q hq0; simp at this
          | some q' => simp only [hext, if_true, hin, Bool.false_eq_true, if_false, hl]
        · have hext : r.full.extVars.contains v = false := by
            simp only [SMachine.extVars, List.contains_iff_mem, List.mem_append, not_or]
            simpa [List.contains_iff_mem] using (⟨hi, hq, hv⟩ : v ∉ r.full.f.m.inputs ∧ v ∉ r.full.qVars ∧ v ∉ r.full.wVars)
          rw [decideQ_other hq, withInputs_other hi]
          simp only [hext, Bool.false_eq_true, if_false]
    rw [congrC _ _ _ r.allowed (fun i hi => hE i (avoids_occ hw hi))] at h'
    simp only [SRefined.allowed] at h'
    rw [inline_evalC] at h'
    exact h'
  intro ρ M hr
  obtain ⟨ρc, Mc, hrc, hag, hmag⟩ := srefine_lift r hok hmo hr
  obtain ⟨σ, Ms, hrs, hags, hmags⟩ := srefine_project r hok hpre hallow hrc
  exact ⟨ρc, Mc, σ, Ms, hrc, hag, hmag, hrs, hags, hmags, hlaws ρc Mc hrc⟩

end Kern

#print axioms Kern.srefine_lift
#print axioms Kern.srefine_project
#print axioms Kern.srefines

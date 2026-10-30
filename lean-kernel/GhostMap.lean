import Ghost

/-!
GhostMap: ghost maps, proven. Ghost.lean's `sghost_reach` lets a machine gain ghost values (scalars the step keeps);
this file lets it gain ghost maps too: maps the original never reads, each starting at a constant and written by the
step at one key (`gwrites`) or at every key (`gevery`). A ghost map is a Skolem function the step keeps: a law of the
ghosted machine about every key k, reading the ghost map W at k, says that every k has a witness, W[k].

Lean checks that a ghosted machine is the original's parts plus each ghost's start and step (`SGhostedM.full`), with
new names read by no part of the original (`smghostOk`), and proves, for machines with maps, flags and sets:
- `smghost_reach`: every reachable state of the original is, outside the ghost variables and the ghost maps, a
  reachable state of the ghosted machine (the generalization of `sghost_reach` from ghost values to ghost maps);
- `smghost_laws`: a law of the ghosted machine that reads no ghost holds of the original;
- `some_of_ghostmap`: the laws of the ghosted machine give, at every reachable state of the original, ghost values and
  ghost maps (Skolem functions of the keys) that agree with the state elsewhere and where every law holds;
- `forall_some_of_ghostmap`: the ∀∃ reading. A law about every key kv that reads the ghost map W only at one key term t
  gives: for every value of kv, some natural x satisfies the law with each read of W replaced by x (`substRC [] (rdW W
  x)`), a statement about the original alone when that law reads no other ghost.
-/

namespace Kern
open Classical

structure SGhostedM where
  orig : SMachine
  ghosts : List (Nat × E × E)       -- ghost values: (variable, start over the params, step), as SGhosted's
  gmaps : List (Nat × Nat)          -- ghost maps: (map, its value at every key at the start)
  gwrites : List (Nat × E × E)      -- (ghost map, key, value): a write at one key
  gevery : List (Nat × Nat × E)     -- (ghost map, bound key, value): a write at every key

def SGhostedM.vars (g : SGhostedM) : List Nat := g.ghosts.map (·.1)
def SGhostedM.maps (g : SGhostedM) : List Nat := g.gmaps.map (·.1)

-- The ghosted machine: the original, each ghost's start and step added after the original's.
def SGhostedM.full (g : SGhostedM) : SMachine :=
  ⟨⟨⟨g.orig.f.m.inputs, g.orig.f.m.init ++ g.ghosts.map (fun x => (x.1, x.2.1)), g.orig.f.m.maps0 ++ g.gmaps,
      g.orig.f.m.step ++ g.ghosts.map (fun x => (x.1, x.2.2)), g.orig.f.m.writes ++ g.gwrites, g.orig.f.m.pre, g.orig.f.m.assume⟩, g.orig.f.flags⟩,
    g.orig.carried, g.orig.every ++ g.gevery, g.orig.qflags, g.orig.wits, g.orig.facts, g.orig.pfacts⟩

-- The original's maps, in any role: started, written at a key, written at every key, carried.
def origMaps (s : SMachine) : List Nat := s.f.m.maps0.map (·.1) ++ s.f.m.writes.map (·.1) ++ s.every.map (·.1) ++ s.carried

-- Reads none of the variables V and none of the maps MS.
def apartC (V MS : List Nat) (c : C) : Bool := avoids V c && avoidsMaps MS c
def apartE (V MS : List Nat) (e : E) : Bool := avoidsE V e && avoidsMapsE MS e

-- The ghosts are new names (variables and maps), the ghost writes write ghost maps, and no part of the original reads a
-- ghost.
def smghostOk (g : SGhostedM) : Bool :=
  distinct g.vars && distinct g.maps
    && g.vars.all (fun v => !(g.orig.extVars ++ g.orig.f.m.init.map (·.1) ++ g.orig.f.m.step.map (·.1) ++ flagVars g.orig.f.flags ++ bkeys g.orig).contains v)
    && g.maps.all (fun mp => !(origMaps g.orig).contains mp)
    && (g.gwrites.map (·.1) ++ g.gevery.map (·.1)).all (fun mp => g.maps.contains mp)
    && apartC g.vars g.maps g.orig.f.m.pre && apartC g.vars g.maps g.orig.f.m.assume
    && g.orig.f.flags.all (fun p => apartC g.vars g.maps p.2) && g.orig.qflags.all (fun q => apartC g.vars g.maps q.2.2)
    && g.orig.f.m.init.all (fun p => apartE g.vars g.maps p.2) && g.orig.f.m.step.all (fun p => apartE g.vars g.maps p.2)
    && g.orig.f.m.writes.all (fun w => apartE g.vars g.maps w.2.1 && apartE g.vars g.maps w.2.2)
    && g.orig.every.all (fun w => apartE g.vars g.maps w.2.2)
    && g.orig.facts.all (fun l => apartC g.vars g.maps l.holds) && g.orig.pfacts.all (fun f => apartC g.vars g.maps f.1.holds)

/-! Reading alike outside the ghosts -/

theorem apartC_parts {V MS : List Nat} {c : C} (h : apartC V MS c = true) : avoids V c = true ∧ avoidsMaps MS c = true := by
  simpa [apartC] using h
theorem apartE_parts {V MS : List Nat} {e : E} (h : apartE V MS e = true) : avoidsE V e = true ∧ avoidsMapsE MS e = true := by
  simpa [apartE] using h

theorem evalC_apart {V MS : List Nat} {c : C} (h : apartC V MS c = true) {ρ ρ' : Nat → Nat} {M M' : Nat → Nat → Nat}
    (hag : Agree V ρ ρ') (hm : ∀ mp, mp ∉ MS → M mp = M' mp) : evalC ρ M c = evalC ρ' M' c := by
  obtain ⟨hv, hmm⟩ := apartC_parts h
  rw [congrC ρ ρ' M c (fun i hi => hag i (avoids_occ hv hi)), congrMC ρ' M M' c (fun mp hmp => hm mp (avoidsMaps_occ hmm hmp))]

theorem evalE_apart {V MS : List Nat} {e : E} (h : apartE V MS e = true) {ρ ρ' : Nat → Nat} {M M' : Nat → Nat → Nat}
    (hag : Agree V ρ ρ') (hm : ∀ mp, mp ∉ MS → M mp = M' mp) : evalE ρ M e = evalE ρ' M' e := by
  obtain ⟨hv, hmm⟩ := apartE_parts h
  rw [congrE ρ ρ' M e (fun i hi => hag i (avoidsE_occ hv hi)), congrME ρ' M M' e (fun mp hmp => hm mp (avoidsMapsE_occ hmm hmp))]

-- Flags decided over states and maps that agree outside the ghosts, by conditions that read no ghost, agree there.
theorem decide_apart {fl : List (Nat × C)} {V MS : List Nat} (hav : ∀ p ∈ fl, apartC V MS p.2 = true) {X X' : Nat → Nat}
    {N N' : Nat → Nat → Nat} (h : Agree V X X') (hN : ∀ mp, mp ∉ MS → N mp = N' mp) : Agree V (decideFlags fl X N) (decideFlags fl X' N') := by
  intro i hi
  simp only [decideFlags, applyS, assoc_flagSub]
  cases hc : flagOf fl i with
  | none => exact h i hi
  | some c =>
    obtain ⟨p, hp, rfl⟩ := flagOf_some hc
    simp only [Option.map_some, evalE]
    rw [evalC_apart (hav p hp) h hN]

theorem lookup_append_none {α : Type} (p : α → Bool) (l1 l2 : List α) (h : lookup p l2 = none) : lookup p (l1 ++ l2) = lookup p l1 := by
  rw [lookup_append]; cases lookup p l1 <;> simp [h]

-- The ghost maps at their starts, every other map as it is.
def startWith (gm : List (Nat × Nat)) (M : Nat → Nat → Nat) : Nat → Nat → Nat := fun mp =>
  match lookup (fun p => p.1 == mp) gm with
  | some p => fun _ => p.2
  | none => M mp

-- The facts about several keys, read where maps agree on what they read.
theorem holdsOver_maps {l : MLaw} {MS : List Nat} (hm : avoidsMaps MS l.holds = true) {M M' : Nat → Nat → Nat}
    (hmag : ∀ mp, mp ∉ MS → M mp = M' mp) : ∀ (gs : List Nat) (ρ : Nat → Nat), holdsOver l M' gs ρ → holdsOver l M gs ρ
  | [], ρ, h => holds_transfer (V := []) l (by simp [avoids]) hm (fun _ _ => rfl) hmag h
  | _ :: gs, ρ, h => fun w => holdsOver_maps hm hmag gs _ (h w)

section smghost
variable (g : SGhostedM) (hg : smghostOk g = true)
include hg

theorem smghostOk_parts :
    distinct g.vars = true ∧ distinct g.maps = true
      ∧ (∀ mp ∈ g.maps, mp ∉ origMaps g.orig)
      ∧ (∀ mp ∈ g.gwrites.map (·.1) ++ g.gevery.map (·.1), mp ∈ g.maps)
      ∧ apartC g.vars g.maps g.orig.f.m.pre = true ∧ apartC g.vars g.maps g.orig.f.m.assume = true
      ∧ (∀ p ∈ g.orig.f.flags, apartC g.vars g.maps p.2 = true) ∧ (∀ q ∈ g.orig.qflags, apartC g.vars g.maps q.2.2 = true)
      ∧ (∀ p ∈ g.orig.f.m.init, apartE g.vars g.maps p.2 = true) ∧ (∀ p ∈ g.orig.f.m.step, apartE g.vars g.maps p.2 = true)
      ∧ (∀ w ∈ g.orig.f.m.writes, apartE g.vars g.maps w.2.1 = true ∧ apartE g.vars g.maps w.2.2 = true)
      ∧ (∀ w ∈ g.orig.every, apartE g.vars g.maps w.2.2 = true)
      ∧ (∀ l ∈ g.orig.facts, apartC g.vars g.maps l.holds = true) ∧ (∀ f ∈ g.orig.pfacts, apartC g.vars g.maps f.1.holds = true) := by
  simp only [smghostOk, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hdv, hdm⟩, _⟩, hom⟩, hw⟩, hp⟩, ha⟩, hf⟩, hq⟩, hi⟩, hs⟩, hwr⟩, he⟩, hfa⟩, hpf⟩ := hg
  exact ⟨hdv, hdm, fun mp hm => by simpa using hom mp hm, fun mp hm => by simpa using hw mp hm, hp, ha, hf, hq, hi, hs, hwr, he, hfa, hpf⟩

/-- One step from states and maps that agree outside the ghosts, with the same request: allowed alike, and to states
and maps that agree outside the ghosts. -/
theorem smghost_step {ρg ρ : Nat → Nat} {Mg M : Nat → Nat → Nat} (hag : Agree g.vars ρg ρ) (hmag : ∀ mp, mp ∉ g.maps → Mg mp = M mp)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    evalC (sView g.full ρg Mg ι κ).1 (sView g.full ρg Mg ι κ).2 g.full.f.m.assume = evalC (sView g.orig ρ M ι κ).1 (sView g.orig ρ M ι κ).2 g.orig.f.m.assume
      ∧ Agree g.vars (sNext g.full ρg Mg ι κ).1 (sNext g.orig ρ M ι κ).1
      ∧ ∀ mp, mp ∉ g.maps → (sNext g.full ρg Mg ι κ).2 mp = (sNext g.orig ρ M ι κ).2 mp := by
  obtain ⟨_, _, _, hw, _, ha, hf, hq, _, hs, hwr, he, _, _⟩ := smghostOk_parts g hg
  have hX : Agree g.vars (withInputs g.orig.f.m.inputs ρg ι) (withInputs g.orig.f.m.inputs ρ ι) := withInputs_agree hag ι
  have hN : ∀ mp, mp ∉ g.maps → withCarried g.orig Mg κ mp = withCarried g.orig M κ mp := fun mp hmp => by
    simp only [withCarried]; split
    · rfl
    · exact hmag mp hmp
  have hQ : Agree g.vars (decideQ g.orig (withInputs g.orig.f.m.inputs ρg ι) (withCarried g.orig Mg κ))
      (decideQ g.orig (withInputs g.orig.f.m.inputs ρ ι) (withCarried g.orig M κ)) := by
    intro v hv
    rw [decideQ_of, decideQ_of]
    cases hl : lookup (fun q => q.1 == v) g.orig.qflags with
    | some q =>
      obtain ⟨hqv, hqm⟩ := apartC_parts (hq q (lookup_some hl).1)
      exact ite_all_congr (fun i hi _ => hX i (avoids_occ hqv hi)) (fun mp hm => hN mp (avoidsMaps_occ hqm hm))
    | none => exact hX v hv
  have hD := decide_apart hf hQ hN
  -- The ghosted machine's lists are the original's with the ghosts' after them.
  have hstep : g.full.f.m.step = g.orig.f.m.step ++ g.ghosts.map (fun x => (x.1, x.2.2)) := rfl
  have hevery : g.full.every = g.orig.every ++ g.gevery := rfl
  have hwrites : g.full.f.m.writes = g.orig.f.m.writes ++ g.gwrites := rfl
  refine ⟨?_, fun i hi => ?_, fun mp hmp => ?_⟩
  · show evalC (decideFlags g.orig.f.flags (decideQ g.orig (withInputs g.orig.f.m.inputs ρg ι) (withCarried g.orig Mg κ)) (withCarried g.orig Mg κ)) (withCarried g.orig Mg κ) g.orig.f.m.assume = _
    exact evalC_apart ha hD hN
  · show applyS g.full.f.m.step (decideFlags g.orig.f.flags (decideQ g.orig (withInputs g.orig.f.m.inputs ρg ι) (withCarried g.orig Mg κ)) (withCarried g.orig Mg κ)) (withCarried g.orig Mg κ) i = _
    rw [hstep, applyS_append_other (by simpa [SGhostedM.vars] using hi)]
    simp only [sNext, sView, applyS]
    cases hst : assoc g.orig.f.m.step i with
    | none => exact hD i hi
    | some e =>
      have hm : (i, e) ∈ g.orig.f.m.step := by
        simp only [assoc, Option.map_eq_some_iff] at hst
        obtain ⟨q, hq', rfl⟩ := hst
        obtain ⟨hqm, hqv⟩ := lookup_some hq'
        simp only [beq_iff_eq] at hqv
        rw [← hqv]; exact hqm
      exact evalE_apart (hs (i, e) hm) hD hN
  · funext key
    show everyMaps g.full (decideFlags g.orig.f.flags (decideQ g.orig (withInputs g.orig.f.m.inputs ρg ι) (withCarried g.orig Mg κ)) (withCarried g.orig Mg κ)) (withCarried g.orig Mg κ) mp key
      = everyMaps g.orig (decideFlags g.orig.f.flags (decideQ g.orig (withInputs g.orig.f.m.inputs ρ ι) (withCarried g.orig M κ)) (withCarried g.orig M κ)) (withCarried g.orig M κ) mp key
    have hge : lookup (fun w => w.1 == mp) g.gevery = none :=
      lookup_none (fun w hw' => by
        simp only [beq_eq_false_iff_ne]; intro he'
        exact hmp (by rw [← he']; exact hw w.1 (List.mem_append_right _ (List.mem_map_of_mem hw'))))
    have hgw : lookup (fun w => w.1 == mp) g.gwrites = none :=
      lookup_none (fun w hw' => by
        simp only [beq_eq_false_iff_ne]; intro he'
        exact hmp (by rw [← he']; exact hw w.1 (List.mem_append_left _ (List.mem_map_of_mem hw'))))
    simp only [everyMaps, hevery, lookup_append_none _ g.orig.every _ hge]
    cases hl : lookup (fun w => w.1 == mp) g.orig.every with
    | some w => exact evalE_apart (he w (lookup_some hl).1) (upd_agree hD w.2.1 key) hN
    | none =>
      simp only [writeMaps, hwrites, lookup_append_none _ g.orig.f.m.writes _ hgw]
      cases hl2 : lookup (fun w => w.1 == mp) g.orig.f.m.writes with
      | none => exact congrFun (hN mp hmp) key
      | some w =>
        obtain ⟨h1, h2⟩ := hwr w (lookup_some hl2).1
        dsimp only
        rw [evalE_apart h1 hD hN, evalE_apart h2 hD hN, hN mp hmp]

/-- Every reachable state of the original is, outside the ghost variables and the ghost maps, a reachable state of the
ghosted machine. -/
theorem smghost_reach : ∀ {ρ M}, SReach g.orig ρ M → ∃ ρg Mg, SReach g.full ρg Mg ∧ Agree g.vars ρg ρ ∧ ∀ mp, mp ∉ g.maps → Mg mp = M mp := by
  obtain ⟨_, hdm, hom, _, hp, _, _, _, hi, _, _, _, hfa, hpf⟩ := smghostOk_parts g hg
  intro ρ M hr
  induction hr with
  | start ρ0 M0 hM h0 hfa0 hpf0 =>
    have hout : ∀ mp, mp ∉ g.maps → startWith g.gmaps M0 mp = M0 mp := fun mp hmp => by
      have hl : lookup (fun p => p.1 == mp) g.gmaps = none := lookup_none (fun p hp' => by
        simp only [beq_eq_false_iff_ne]; intro he'; exact hmp (by rw [← he']; exact List.mem_map_of_mem hp'))
      simp only [startWith, hl]
    have hstart : StartMaps g.full.f.m (startWith g.gmaps M0) := by
      intro p hp' key
      rcases List.mem_append.mp hp' with hp' | hp'
      · have hpo : p.1 ∉ g.maps := fun hm => hom p.1 hm (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hp'))))
        rw [hout p.1 hpo]; exact hM p hp' key
      · have hl : lookup (fun q => q.1 == p.1) g.gmaps = some p := lookup_unique (by simpa [SGhostedM.maps] using hdm) hp'
        simp only [startWith, hl]
    obtain ⟨_, hpm⟩ := apartC_parts hp
    refine ⟨applyS g.full.f.m.init ρ0 (startWith g.gmaps M0), startWith g.gmaps M0, SReach.start ρ0 _ hstart ?_ ?_ ?_, fun i hi' => ?_, hout⟩
    · show evalC ρ0 (startWith g.gmaps M0) g.orig.f.m.pre = true
      rw [congrMC ρ0 _ M0 _ (fun mp hm => hout mp (avoidsMaps_occ hpm hm))]; exact h0
    · intro l hl
      exact holds_transfer (V := []) l (by simp [avoids]) (apartC_parts (hfa l hl)).2 (fun _ _ => rfl) hout (hfa0 l hl)
    · intro f hf
      exact holdsOver_maps (apartC_parts (hpf f hf)).2 hout f.2 ρ0 (hpf0 f hf)
    · show applyS (g.orig.f.m.init ++ g.ghosts.map (fun x => (x.1, x.2.1))) ρ0 (startWith g.gmaps M0) i = applyS g.orig.f.m.init ρ0 M0 i
      rw [applyS_append_other (by simpa [SGhostedM.vars] using hi')]
      simp only [applyS]
      cases hst : assoc g.orig.f.m.init i with
      | none => rfl
      | some e =>
        have hm : (i, e) ∈ g.orig.f.m.init := by
          simp only [assoc, Option.map_eq_some_iff] at hst
          obtain ⟨q, hq', rfl⟩ := hst
          obtain ⟨hqm, hqv⟩ := lookup_some hq'
          simp only [beq_iff_eq] at hqv
          rw [← hqv]; exact hqm
        exact evalE_apart (hi (i, e) hm) (fun _ _ => rfl) hout
  | step ρ M ι κ _ ha ih =>
    obtain ⟨ρg, Mg, hrg, hag, hmag⟩ := ih
    obtain ⟨hA, hS, hW⟩ := smghost_step g hg hag hmag ι κ
    exact ⟨_, _, SReach.step ρg Mg ι κ hrg (by rw [hA]; exact ha), hS, hW⟩

/-- A law of the ghosted machine that reads no ghost holds in every reachable state of the original. -/
theorem smghost_laws (ps : List SEntry) (hl : checkSMachine g.full ps = true) :
    ∀ ρ M, SReach g.orig ρ M → ∀ e ∈ ps, avoids g.vars e.law.holds = true → avoidsMaps g.maps e.law.holds = true → e.Holds ρ M := by
  intro ρ M hr e he hav ham
  obtain ⟨ρg, Mg, hrg, hag, hmag⟩ := smghost_reach g hg hr
  exact sentry_transfer (V := g.vars) (MS := g.maps) hav ham (fun i hi => (hag i hi).symm) (fun mp hmp => (hmag mp hmp).symm)
    (smachine_sound g.full ps hl ρg Mg hrg e he)

/-- The laws of the ghosted machine, at every reachable state of the original: some ghost values and some ghost maps
(Skolem functions of the keys), the state and maps as they are elsewhere, where every law holds. -/
theorem some_of_ghostmap (ps : List SEntry) (hl : checkSMachine g.full ps = true) :
    ∀ ρ M, SReach g.orig ρ M → ∃ ρg Mg, Agree g.vars ρg ρ ∧ (∀ mp, mp ∉ g.maps → Mg mp = M mp) ∧ ∀ e ∈ ps, e.Holds ρg Mg := by
  intro ρ M hr
  obtain ⟨ρg, Mg, hrg, hag, hmag⟩ := smghost_reach g hg hr
  exact ⟨ρg, Mg, hag, hmag, smachine_sound g.full ps hl ρg Mg hrg⟩
end smghost

/-! The ∀∃ reading: a ghost map read at one key, as a natural -/

-- Every read of the map W is at the key term t.
mutual
def atKeyE (W : Nat) (t : E) : E → Bool
  | .var _ => true
  | .const _ => true
  | .add a b => atKeyE W t a && atKeyE W t b
  | .sub a b => atKeyE W t a && atKeyE W t b
  | .mul _ a => atKeyE W t a
  | .min a b => atKeyE W t a && atKeyE W t b
  | .max a b => atKeyE W t a && atKeyE W t b
  | .prod a b => atKeyE W t a && atKeyE W t b
  | .ite c a b => atKeyC W t c && atKeyE W t a && atKeyE W t b
  | .get m key => if m == W then beqE key t else atKeyE W t key
def atKeyC (W : Nat) (t : E) : C → Bool
  | .le a b => atKeyE W t a && atKeyE W t b
  | .lt a b => atKeyE W t a && atKeyE W t b
  | .eq a b => atKeyE W t a && atKeyE W t b
  | .and a b => atKeyC W t a && atKeyC W t b
  | .or a b => atKeyC W t a && atKeyC W t b
  | .not a => atKeyC W t a
end

-- A read of W as the variable x; any other read as it is.
def rdW (W x : Nat) : Nat → E → E := fun m k => if m == W then .var x else .get m k

-- The maps with W the constant v.
def withConst (W v : Nat) (M : Nat → Nat → Nat) : Nat → Nat → Nat := fun m => if m == W then fun _ => v else M m

section atkey
variable (W : Nat) (t : E) (ρ : Nat → Nat) (M : Nat → Nat → Nat)
mutual
theorem atKey_evalE : (e : E) → atKeyE W t e = true → evalE ρ M e = evalE ρ (withConst W (M W (evalE ρ M t)) M) e
  | .var _, _ => rfl
  | .const _, _ => rfl
  | .add a b, h => by simp only [atKeyE, Bool.and_eq_true] at h; simp only [evalE, atKey_evalE a h.1, atKey_evalE b h.2]
  | .sub a b, h => by simp only [atKeyE, Bool.and_eq_true] at h; simp only [evalE, atKey_evalE a h.1, atKey_evalE b h.2]
  | .mul _ a, h => by simp only [atKeyE] at h; simp only [evalE, atKey_evalE a h]
  | .min a b, h => by simp only [atKeyE, Bool.and_eq_true] at h; simp only [evalE, atKey_evalE a h.1, atKey_evalE b h.2]
  | .max a b, h => by simp only [atKeyE, Bool.and_eq_true] at h; simp only [evalE, atKey_evalE a h.1, atKey_evalE b h.2]
  | .prod a b, h => by simp only [atKeyE, Bool.and_eq_true] at h; simp only [evalE, atKey_evalE a h.1, atKey_evalE b h.2]
  | .ite c a b, h => by
    simp only [atKeyE, Bool.and_eq_true] at h
    simp only [evalE, atKey_evalC c h.1.1, atKey_evalE a h.1.2, atKey_evalE b h.2]
  | .get m key, h => by
    simp only [atKeyE] at h
    by_cases hm : m = W
    · subst hm
      simp only [beq_self_eq_true, ite_true] at h
      rw [beqE_eq h]
      simp [evalE, withConst]
    · have hb : (m == W) = false := by simp [hm]
      simp only [hb, Bool.false_eq_true, ite_false] at h
      simp only [evalE, withConst, hb, Bool.false_eq_true, ite_false, ← atKey_evalE key h]
theorem atKey_evalC : (c : C) → atKeyC W t c = true → evalC ρ M c = evalC ρ (withConst W (M W (evalE ρ M t)) M) c
  | .le a b, h => by simp only [atKeyC, Bool.and_eq_true] at h; simp only [evalC, atKey_evalE a h.1, atKey_evalE b h.2]
  | .lt a b, h => by simp only [atKeyC, Bool.and_eq_true] at h; simp only [evalC, atKey_evalE a h.1, atKey_evalE b h.2]
  | .eq a b, h => by simp only [atKeyC, Bool.and_eq_true] at h; simp only [evalC, atKey_evalE a h.1, atKey_evalE b h.2]
  | .and a b, h => by simp only [atKeyC, Bool.and_eq_true] at h; simp only [evalC, atKey_evalC a h.1, atKey_evalC b h.2]
  | .or a b, h => by simp only [atKeyC, Bool.and_eq_true] at h; simp only [evalC, atKey_evalC a h.1, atKey_evalC b h.2]
  | .not a, h => by simp only [atKeyC] at h; simp only [evalC, atKey_evalC a h]
end
end atkey

-- A condition that reads W only at t, with each read of W replaced by a fresh x, read where x is W's value at t.
theorem rdW_evalC (W x : Nat) (t : E) (c : C) (hat : atKeyC W t c = true) (hx : occC x c = false) (ρ : Nat → Nat) (M : Nat → Nat → Nat) :
    evalC (upd ρ x (M W (evalE ρ M t))) M (substRC [] (rdW W x) c) = evalC ρ M c := by
  have hrd : ∀ m k, evalE (upd ρ x (M W (evalE ρ M t))) M (rdW W x m k)
      = withConst W (M W (evalE ρ M t)) M m (evalE (upd ρ x (M W (evalE ρ M t))) M k) := by
    intro m k
    by_cases hm : m = W
    · subst hm; simp [rdW, withConst, evalE, upd]
    · have hb : (m == W) = false := by simp [hm]
      simp [rdW, withConst, evalE, hb]
  rw [substR_evalC [] (rdW W x) _ M _ hrd c, applyS_nil, atKey_evalC W t ρ M c hat]
  exact congrC _ _ _ c (fun i hi => by
    simp only [upd]; split
    · rename_i hix; subst hix; simp [hx] at hi
    · rfl)

/-- The ∀∃ reading of a ghost map: a law of the ghosted machine about every value of kv (no further keys) that reads
the ghost map W only at the key term t gives, at every reachable state of the original, for every value of kv some
natural x where the law holds with each read of W replaced by x; when that condition reads no ghost, it is a statement
about the original alone. -/
theorem forall_some_of_ghostmap (g : SGhostedM) (hg : smghostOk g = true) (ps : List SEntry) (hl : checkSMachine g.full ps = true)
    (e : SEntry) (he : e ∈ ps) (kv : Nat) (hk : e.law.key = some kv) (hk2 : e.keys2 = []) (W x : Nat) (t : E)
    (hat : atKeyC W t e.law.holds = true) (hx : occC x e.law.holds = false)
    (hav : avoids g.vars (substRC [] (rdW W x) e.law.holds) = true) (ham : avoidsMaps g.maps (substRC [] (rdW W x) e.law.holds) = true) :
    ∀ ρ M, SReach g.orig ρ M → ∀ v, ∃ val, evalC (upd (upd ρ kv v) x val) M (substRC [] (rdW W x) e.law.holds) = true := by
  intro ρ M hr v
  obtain ⟨ρg, Mg, hrg, hag, hmag⟩ := smghost_reach g hg hr
  have hall := smachine_sound g.full ps hl ρg Mg hrg e he
  simp only [SEntry.Holds, hk2, holdsOver, MLaw.Holds, hk] at hall
  refine ⟨Mg W (evalE (upd ρg kv v) Mg t), ?_⟩
  have h1 := rdW_evalC W x t e.law.holds hat hx (upd ρg kv v) Mg
  rw [hall v] at h1
  have hagx : Agree g.vars (upd (upd ρ kv v) x (Mg W (evalE (upd ρg kv v) Mg t))) (upd (upd ρg kv v) x (Mg W (evalE (upd ρg kv v) Mg t))) :=
    upd_agree (upd_agree (fun i hi => (hag i hi).symm) kv v) x _
  rw [congrC _ _ M _ (fun i hi => hagx i (avoids_occ hav hi)),
    congrMC _ M Mg _ (fun mp hmp => (hmag mp (avoidsMaps_occ ham hmp)).symm)]
  exact h1

end Kern

#print axioms Kern.smghost_reach
#print axioms Kern.smghost_laws
#print axioms Kern.some_of_ghostmap
#print axioms Kern.forall_some_of_ghostmap

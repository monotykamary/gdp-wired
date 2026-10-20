import Live

/-!
What a ghost means, proven: compose.ts's `ghost(m, vars)` adds state that watches a machine without changing it. Lean
checks that a ghosted machine is the original's parts plus each ghost's start and step, read by no part of the original
(`sghostOk`), and proves, for machines with maps, flags and sets:
- `sghost_reach`: every reachable state of the original is, outside the ghosts, a reachable state of the ghosted
  machine, so a law of the ghosted machine that reads no ghost is a law of the original (`sghost_laws`);
- `sghost_run`: every run of the original is, outside the ghosts, a run of the ghosted machine taking the same requests;
- `sever_meaning`: along a run, a ghost that starts at 0 and is set to 1 by a step where `c` holds (compose.ts's `ever`)
  is 1 exactly when some step before took a request where `c` held.
-/

namespace Kern
open Classical

theorem lookup_unique_fst {p : Nat × E} {l : List (Nat × E)} (hd : distinct (l.map (·.1)) = true) (hp : p ∈ l) :
    lookup (fun q => q.1 == p.1) l = some p := by
  induction l with
  | nil => simp at hp
  | cons a as ih =>
    simp only [List.map_cons] at hd
    obtain ⟨hna, hd'⟩ := distinct_cons hd
    simp only [lookup]
    rcases List.mem_cons.mp hp with rfl | hp'
    · simp
    · have hne : (a.1 == p.1) = false := by
        simp only [beq_eq_false_iff_ne]; intro he; exact hna (by rw [he]; exact List.mem_map_of_mem hp')
      simp only [hne, Bool.false_eq_true, ite_false]; exact ih hd' hp'

theorem assoc_append_none {σ τ : List (Nat × E)} {i : Nat} (h : i ∉ τ.map (·.1)) : assoc (σ ++ τ) i = assoc σ i := by
  have hτ : lookup (fun p => p.1 == i) τ = none :=
    lookup_none (fun p hp => by simp only [beq_eq_false_iff_ne]; intro he; exact h (by rw [← he]; exact List.mem_map_of_mem hp))
  simp only [assoc, lookup_append]
  cases hσ : lookup (fun p => p.1 == i) σ <;> simp [hτ]

theorem applyS_append_other {σ τ : List (Nat × E)} {i : Nat} (h : i ∉ τ.map (·.1)) (ρ : Nat → Nat) (M : Nat → Nat → Nat) :
    applyS (σ ++ τ) ρ M i = applyS σ ρ M i := by
  simp only [applyS, assoc_append_none h]

-- The keys a machine's every-key writes and quantified flags bind.
def bkeys (s : SMachine) : List Nat := s.every.map (·.2.1) ++ s.qflags.flatMap (·.2.1)

-- A flag that holds at every value of its keys, decided over states that agree where its body reads (its keys aside), is
-- decided alike.
theorem ite_all_congr {X X' : Nat → Nat} {N N' : Nat → Nat → Nat} {ks : List Nat} {c : C}
    (hv : ∀ i, occC i c = true → i ∉ ks → X i = X' i) (hm : ∀ mp, occMC mp c = true → N mp = N' mp) :
    (if ∀ k, holdsC (atKeys X ks k) N c then 1 else 0) = (if ∀ k, holdsC (atKeys X' ks k) N' c then 1 else 0) := by
  have h : (∀ k, holdsC (atKeys X ks k) N c) ↔ (∀ k, holdsC (atKeys X' ks k) N' c) := by
    apply forall_congr'; intro k
    rw [← evalC_iff, ← evalC_iff, congrMC _ N N' c hm]
    rw [congrC (atKeys X ks k) (atKeys X' ks k) N' c (fun i hi => by
      by_cases hik : i ∈ ks
      · rw [atKeys_in hik, atKeys_in hik]
      · rw [atKeys_out hik, atKeys_out hik]; exact hv i hi hik)]
  simp only [h]

theorem decideQ_of (s : SMachine) (X : Nat → Nat) (N : Nat → Nat → Nat) (v : Nat) :
    decideQ s X N v = match lookup (fun q => q.1 == v) s.qflags with
      | some q => if ∀ k, holdsC (atKeys X q.2.1 k) N q.2.2 then 1 else 0
      | none => X v := rfl

theorem upd_agree {V : List Nat} {X X' : Nat → Nat} (h : Agree V X X') (k v : Nat) : Agree V (upd X k v) (upd X' k v) := fun i hi => by
  simp only [upd]; split
  · rfl
  · exact h i hi

/-! Ghosts -/

structure SGhosted where
  orig : SMachine
  ghosts : List (Nat × E × E)   -- (variable, start over the params, step over the state before, the request and flags)

def SGhosted.vars (g : SGhosted) : List Nat := g.ghosts.map (·.1)

-- The ghosted machine: the original, each ghost's start and step added.
def SGhosted.full (g : SGhosted) : SMachine :=
  ⟨⟨⟨g.orig.f.m.inputs, g.orig.f.m.init ++ g.ghosts.map (fun x => (x.1, x.2.1)), g.orig.f.m.maps0,
      g.orig.f.m.step ++ g.ghosts.map (fun x => (x.1, x.2.2)), g.orig.f.m.writes, g.orig.f.m.pre, g.orig.f.m.assume⟩, g.orig.f.flags⟩,
    g.orig.carried, g.orig.every, g.orig.qflags, g.orig.wits, g.orig.facts, g.orig.pfacts⟩

-- The ghosts are new names, and nothing of the original reads them.
def sghostOk (g : SGhosted) : Bool :=
  distinct g.vars
    && g.vars.all (fun v => !(g.orig.extVars ++ g.orig.f.m.init.map (·.1) ++ g.orig.f.m.step.map (·.1) ++ flagVars g.orig.f.flags ++ bkeys g.orig).contains v)
    && avoids g.vars g.orig.f.m.pre && avoids g.vars g.orig.f.m.assume && g.orig.f.flags.all (fun p => avoids g.vars p.2)
    && g.orig.f.m.step.all (fun p => avoidsE g.vars p.2) && g.orig.f.m.init.all (fun p => avoidsE g.vars p.2)
    && g.orig.f.m.writes.all (fun w => avoidsE g.vars w.2.1 && avoidsE g.vars w.2.2)
    && g.orig.every.all (fun w => avoidsE g.vars w.2.2) && g.orig.qflags.all (fun q => avoids g.vars q.2.2)
    && g.orig.facts.all (fun l => avoids g.vars l.holds)

-- The ghosted machine reads requests and decides flags as the original does.
theorem sview_full (g : SGhosted) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    sView g.full ρ M ι κ = sView g.orig ρ M ι κ := rfl

-- A run of the original lifted to the ghosted machine from a ghosted state s0 that agrees with its first: the ghosts
-- move with each request the run takes.
noncomputable def sghostFrom (g : SGhosted) (run : SRun g.orig) (s0 : (Nat → Nat) × (Nat → Nat → Nat)) : Nat → (Nat → Nat) × (Nat → Nat → Nat)
  | 0 => s0
  | n + 1 => sNext g.full (sghostFrom g run s0 n).1 (sghostFrom g run s0 n).2 (run.req n).1 (run.req n).2

section sghost
variable (g : SGhosted) (hg : sghostOk g = true)
include hg

theorem sghostOk_parts :
    distinct g.vars = true
      ∧ (∀ v ∈ g.vars, v ∉ g.orig.extVars ++ g.orig.f.m.init.map (·.1) ++ g.orig.f.m.step.map (·.1) ++ flagVars g.orig.f.flags ++ bkeys g.orig)
      ∧ avoids g.vars g.orig.f.m.pre = true ∧ avoids g.vars g.orig.f.m.assume = true ∧ (∀ p ∈ g.orig.f.flags, avoids g.vars p.2 = true)
      ∧ (∀ p ∈ g.orig.f.m.step, avoidsE g.vars p.2 = true) ∧ (∀ p ∈ g.orig.f.m.init, avoidsE g.vars p.2 = true)
      ∧ (∀ w ∈ g.orig.f.m.writes, avoidsE g.vars w.2.1 = true ∧ avoidsE g.vars w.2.2 = true)
      ∧ (∀ w ∈ g.orig.every, avoidsE g.vars w.2.2 = true) ∧ (∀ q ∈ g.orig.qflags, avoids g.vars q.2.2 = true)
      ∧ (∀ l ∈ g.orig.facts, avoids g.vars l.holds = true) := by
  simp only [sghostOk, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hd, hn⟩, hp⟩, ha⟩, hf⟩, hs⟩, hi⟩, hw⟩, he⟩, hq⟩, hfa⟩ := hg
  exact ⟨hd, fun v hv h => (by have := hn v hv; rw [List.contains_iff_mem.mpr h] at this; cases this), hp, ha, hf, hs, hi, hw, he, hq, hfa⟩

-- One step from states that agree outside the ghosts, with the same request: allowed alike, and to states that agree
-- outside the ghosts, with the same maps.
theorem sghost_step {ρ ρg : Nat → Nat} (hag : Agree g.vars ρg ρ) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    evalC (sView g.full ρg M ι κ).1 (sView g.full ρg M ι κ).2 g.full.f.m.assume = evalC (sView g.orig ρ M ι κ).1 (sView g.orig ρ M ι κ).2 g.orig.f.m.assume
      ∧ Agree g.vars (sNext g.full ρg M ι κ).1 (sNext g.orig ρ M ι κ).1
      ∧ (sNext g.full ρg M ι κ).2 = (sNext g.orig ρ M ι κ).2 := by
  obtain ⟨_, _, _, ha, hf, hs, _, hw, he, hq, _⟩ := sghostOk_parts g hg
  have hX : Agree g.vars (withInputs g.orig.f.m.inputs ρg ι) (withInputs g.orig.f.m.inputs ρ ι) := fun i hi => by
    simp only [withInputs]; split
    · rfl
    · exact hag i hi
  have hQ : Agree g.vars (decideQ g.orig (withInputs g.orig.f.m.inputs ρg ι) (withCarried g.orig M κ))
      (decideQ g.orig (withInputs g.orig.f.m.inputs ρ ι) (withCarried g.orig M κ)) := by
    intro v hv
    rw [decideQ_of, decideQ_of]
    cases hl : lookup (fun q => q.1 == v) g.orig.qflags with
    | some q => exact ite_all_congr (fun i hi _ => hX i (avoids_occ (hq q (lookup_some hl).1) hi)) (fun _ _ => rfl)
    | none => exact hX v hv
  have hD := decide_agree_on hf (withCarried g.orig M κ) hQ
  refine ⟨?_, fun i hi => ?_, ?_⟩
  · show evalC (decideFlags g.orig.f.flags (decideQ g.orig (withInputs g.orig.f.m.inputs ρg ι) (withCarried g.orig M κ)) (withCarried g.orig M κ)) _ g.orig.f.m.assume = _
    exact congrC _ _ _ _ (fun i hi => hD i (avoids_occ ha hi))
  · show applyS (g.orig.f.m.step ++ g.ghosts.map (fun x => (x.1, x.2.2))) (decideFlags g.orig.f.flags (decideQ g.orig (withInputs g.orig.f.m.inputs ρg ι) (withCarried g.orig M κ)) (withCarried g.orig M κ)) (withCarried g.orig M κ) i = _
    rw [applyS_append_other (by simpa [SGhosted.vars] using hi)]
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
      exact congrE _ _ _ e (fun j hj => hD j (avoidsE_occ (hs (i, e) hm) hj))
  · funext mp key
    show everyMaps g.orig (decideFlags g.orig.f.flags (decideQ g.orig (withInputs g.orig.f.m.inputs ρg ι) (withCarried g.orig M κ)) (withCarried g.orig M κ)) (withCarried g.orig M κ) mp key
      = everyMaps g.orig (decideFlags g.orig.f.flags (decideQ g.orig (withInputs g.orig.f.m.inputs ρ ι) (withCarried g.orig M κ)) (withCarried g.orig M κ)) (withCarried g.orig M κ) mp key
    simp only [everyMaps]
    cases hl : lookup (fun w => w.1 == mp) g.orig.every with
    | some w => exact congrE _ _ _ w.2.2 (fun j hj => upd_agree hD w.2.1 key j (avoidsE_occ (he w (lookup_some hl).1) hj))
    | none =>
      simp only [writeMaps]
      cases hl2 : lookup (fun w => w.1 == mp) g.orig.f.m.writes with
      | none => rfl
      | some w =>
        obtain ⟨h1, h2⟩ := hw w (lookup_some hl2).1
        simp only [congrE _ _ _ w.2.1 (fun j hj => hD j (avoidsE_occ h1 hj)), congrE _ _ _ w.2.2 (fun j hj => hD j (avoidsE_occ h2 hj))]

/-- Every reachable state of the original is, outside the ghosts, a reachable state of the ghosted machine. -/
theorem sghost_reach : ∀ {ρ M}, SReach g.orig ρ M → ∃ ρg, SReach g.full ρg M ∧ Agree g.vars ρg ρ := by
  intro ρ M hr
  induction hr with
  | start ρ M hM h0 hfa hpf =>
    refine ⟨applyS g.full.f.m.init ρ M, SReach.start ρ M hM h0 hfa hpf, fun i hi => ?_⟩
    show applyS (g.orig.f.m.init ++ g.ghosts.map (fun x => (x.1, x.2.1))) ρ M i = applyS g.orig.f.m.init ρ M i
    exact applyS_append_other (by simpa [SGhosted.vars] using hi) ρ M
  | step ρ M ι κ _ ha ih =>
    obtain ⟨ρg, hrg, hag⟩ := ih
    obtain ⟨hA, hS, hW⟩ := sghost_step g hg hag M ι κ
    refine ⟨_, ?_, hS⟩
    rw [← hW]
    exact SReach.step ρg M ι κ hrg (by rw [hA]; exact ha)

/-- A law of the ghosted machine that reads no ghost holds in every reachable state of the original. -/
theorem sghost_laws (ps : List SEntry) (hl : checkSMachine g.full ps = true) :
    ∀ ρ M, SReach g.orig ρ M → ∀ e ∈ ps, avoids g.vars e.law.holds = true → e.Holds ρ M := by
  intro ρ M hr e he hav
  obtain ⟨ρg, hrg, hag⟩ := sghost_reach g hg hr
  exact sentry_transfer (V := g.vars) (MS := []) hav (by simp [avoidsMaps]) (fun i hi => (hag i hi).symm) (fun _ _ => rfl)
    (smachine_sound g.full ps hl ρg M hrg e he)

theorem sghostFrom_agree (run : SRun g.orig) (s0 : (Nat → Nat) × (Nat → Nat → Nat)) (hM0 : s0.2 = (run.st 0).2) (hA0 : Agree g.vars s0.1 (run.st 0).1) :
    ∀ n, (sghostFrom g run s0 n).2 = (run.st n).2 ∧ Agree g.vars (sghostFrom g run s0 n).1 (run.st n).1
  | 0 => ⟨hM0, hA0⟩
  | n + 1 => by
    obtain ⟨hM, hag⟩ := sghostFrom_agree run s0 hM0 hA0 n
    obtain ⟨_, hS, hW⟩ := sghost_step g hg hag (run.st n).2 (run.req n).1 (run.req n).2
    rw [run.next n]
    simp only [sghostFrom, hM]
    exact ⟨hW, hS⟩

omit hg in
noncomputable def sghostRun (hg : sghostOk g = true) (run : SRun g.orig) (s0 : (Nat → Nat) × (Nat → Nat → Nat)) (hr : SReach g.full s0.1 s0.2)
    (hM0 : s0.2 = (run.st 0).2) (hA0 : Agree g.vars s0.1 (run.st 0).1) : SRun g.full :=
  ⟨sghostFrom g run s0, run.req, hr,
    fun n => by
      obtain ⟨hM, hag⟩ := sghostFrom_agree g hg run s0 hM0 hA0 n
      obtain ⟨hA, _, _⟩ := sghost_step g hg hag (run.st n).2 (run.req n).1 (run.req n).2
      rw [hM, hA]; exact run.allowed n,
    fun n => rfl⟩

/-- Every run of the original is, outside the ghosts, a run of the ghosted machine taking the same requests. -/
theorem sghost_run (run : SRun g.orig) : ∃ run' : SRun g.full, run'.req = run.req ∧ ∀ n, (run'.st n).2 = (run.st n).2 ∧ Agree g.vars (run'.st n).1 (run.st n).1 :=
  ⟨sghostRun g hg run (Classical.choose (sghost_reach g hg run.start), (run.st 0).2) (Classical.choose_spec (sghost_reach g hg run.start)).1 rfl
      (Classical.choose_spec (sghost_reach g hg run.start)).2, rfl,
    sghostFrom_agree g hg run (Classical.choose (sghost_reach g hg run.start), (run.st 0).2) rfl (Classical.choose_spec (sghost_reach g hg run.start)).2⟩
/-- A run of the original from its start lifts to one of the ghosted machine from its start: each ghost at its start term. -/
theorem sghost_run_start (run : SRun g.orig) {ρ0 : Nat → Nat} {M0 : Nat → Nat → Nat} (hM : StartMaps g.orig.f.m M0)
    (hp : evalC ρ0 M0 g.orig.f.m.pre = true) (hfa : ∀ l ∈ g.orig.facts, l.Holds ρ0 M0) (hpf : g.orig.PFacts ρ0 M0) (hst : run.st 0 = (applyS g.orig.f.m.init ρ0 M0, M0)) :
    ∃ run' : SRun g.full, run'.req = run.req ∧ run'.st 0 = (applyS g.full.f.m.init ρ0 M0, M0)
      ∧ ∀ n, (run'.st n).2 = (run.st n).2 ∧ Agree g.vars (run'.st n).1 (run.st n).1 := by
  have hA0 : Agree g.vars (applyS g.full.f.m.init ρ0 M0) (run.st 0).1 := fun i hi => by
    rw [hst]
    show applyS (g.orig.f.m.init ++ g.ghosts.map (fun x => (x.1, x.2.1))) ρ0 M0 i = applyS g.orig.f.m.init ρ0 M0 i
    exact applyS_append_other (by simpa [SGhosted.vars] using hi) ρ0 M0
  have hM0 : M0 = (run.st 0).2 := by rw [hst]
  exact ⟨sghostRun g hg run (applyS g.full.f.m.init ρ0 M0, M0) (SReach.start ρ0 M0 hM hp hfa hpf) hM0 hA0, rfl, rfl,
    sghostFrom_agree g hg run (applyS g.full.f.m.init ρ0 M0, M0) hM0 hA0⟩

-- A condition that reads no ghost, read where a step reads (its request, its flags decided), reads alike in a run and
-- its lift.
theorem sghost_view (run : SRun g.orig) (run' : SRun g.full) (hreq : run'.req = run.req)
    (hag : ∀ n, (run'.st n).2 = (run.st n).2 ∧ Agree g.vars (run'.st n).1 (run.st n).1) {c : C} (hc : avoids g.vars c = true) (n : Nat) :
    evalC (sView g.orig (run'.st n).1 (run'.st n).2 (run'.req n).1 (run'.req n).2).1 (sView g.orig (run'.st n).1 (run'.st n).2 (run'.req n).1 (run'.req n).2).2 c
      = evalC (sView g.orig (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2).1 (sView g.orig (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2).2 c := by
  obtain ⟨_, _, _, _, hf, _, _, _, _, hq, _⟩ := sghostOk_parts g hg
  obtain ⟨hM, hA⟩ := hag n
  rw [hM, hreq]
  have hX : Agree g.vars (withInputs g.orig.f.m.inputs (run'.st n).1 (run.req n).1) (withInputs g.orig.f.m.inputs (run.st n).1 (run.req n).1) := fun i hi => by
    simp only [withInputs]; split
    · rfl
    · exact hA i hi
  have hQ : Agree g.vars (decideQ g.orig (withInputs g.orig.f.m.inputs (run'.st n).1 (run.req n).1) (withCarried g.orig (run.st n).2 (run.req n).2))
      (decideQ g.orig (withInputs g.orig.f.m.inputs (run.st n).1 (run.req n).1) (withCarried g.orig (run.st n).2 (run.req n).2)) := by
    intro v hv
    rw [decideQ_of, decideQ_of]
    cases hl : lookup (fun q => q.1 == v) g.orig.qflags with
    | some q => exact ite_all_congr (fun i hi _ => hX i (avoids_occ (hq q (lookup_some hl).1) hi)) (fun _ _ => rfl)
    | none => exact hX v hv
  exact congrC _ _ _ c (fun i hi => decide_agree_on hf _ hQ i (avoids_occ hc hi))
end sghost

/-- What `ever` means: along a run of the ghosted machine where the ghost x starts at 0, with x's step `if c then 1
else x`, x is 1 at step n exactly when some step before n took a request where c held (read where that step reads: its
request, its flags decided). -/
theorem sever_meaning (g : SGhosted) (hg : sghostOk g = true) {x : Nat} {s0 : E} {c : C} (hx : (x, s0, .ite c (.const 1) (.var x)) ∈ g.ghosts)
    (run : SRun g.full) (h0 : (run.st 0).1 x = 0) :
    ∀ n, (run.st n).1 x = 1 ↔ ∃ i, i < n ∧ evalC (sView g.orig (run.st i).1 (run.st i).2 (run.req i).1 (run.req i).2).1
      (sView g.orig (run.st i).1 (run.st i).2 (run.req i).1 (run.req i).2).2 c = true := by
  obtain ⟨hd, hn, _⟩ := sghostOk_parts g hg
  have hxv : x ∈ g.vars := List.mem_map_of_mem hx
  have hxo := hn x hxv
  have hassoc : assoc g.full.f.m.step x = some (.ite c (.const 1) (.var x)) := by
    show assoc (g.orig.f.m.step ++ g.ghosts.map (fun y => (y.1, y.2.2))) x = _
    simp only [assoc, lookup_append]
    rw [lookup_none (fun p hp => by simp only [beq_eq_false_iff_ne]; intro he; exact hxo (by
      rw [← he]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hp)))))]
    have hl : lookup (fun p => p.1 == x) (g.ghosts.map (fun y => (y.1, y.2.2))) = some (x, .ite c (.const 1) (.var x)) := by
      have hd' : distinct ((g.ghosts.map (fun y => (y.1, y.2.2))).map (·.1)) = true := by rw [List.map_map]; exact hd
      exact lookup_unique_fst hd' (List.mem_map.mpr ⟨_, hx, rfl⟩)
    simp [hl]
  have hxe : x ∉ g.orig.extVars := fun h => hxo (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))))
  have hxf : x ∉ flagVars g.orig.f.flags := fun h => hxo (List.mem_append_left _ (List.mem_append_right _ h))
  simp only [SMachine.extVars, SMachine.qVars, List.mem_append, not_or] at hxe
  intro n
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have hst : (run.st (n + 1)).1 x = if evalC (sView g.orig (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2).1
        (sView g.orig (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2).2 c = true then 1 else (run.st n).1 x := by
      rw [run.next n]
      simp only [sNext, applyS, hassoc, evalE]
      rw [sview_full]
      congr 1
      simp only [sView]
      rw [decide_other hxf, decideQ_other (by simpa [SMachine.qVars] using hxe.1.2), withInputs_other hxe.1.1]
    rw [hst]
    constructor
    · intro h1
      by_cases hc : evalC (sView g.orig (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2).1 (sView g.orig (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2).2 c = true
      · exact ⟨n, Nat.lt_succ_self n, hc⟩
      · rw [if_neg hc] at h1
        obtain ⟨i, hi, hci⟩ := ih.mp h1
        exact ⟨i, Nat.lt_succ_of_lt hi, hci⟩
    · rintro ⟨i, hi, hci⟩
      by_cases hc : evalC (sView g.orig (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2).1 (sView g.orig (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2).2 c = true
      · rw [if_pos hc]
      · rw [if_neg hc]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact ih.mpr ⟨i, hi, hci⟩
        · exact absurd hci hc

end Kern

#print axioms Kern.sghost_reach
#print axioms Kern.sghost_laws
#print axioms Kern.sghost_run
#print axioms Kern.sever_meaning
#print axioms Kern.sghost_run_start

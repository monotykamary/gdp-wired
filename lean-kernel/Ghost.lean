import Live

/-!
What a ghost means, proven: compose.ts's `ghost(m, vars)` adds state that watches a machine without changing it. Lean
checks that a ghosted machine is the original's parts plus each ghost's start and step, read by no part of the original
(`ghostOk`), and proves:
- `ghost_reach`: every reachable state of the original is, outside the ghosts, a reachable state of the ghosted machine,
  so a law of the ghosted machine that reads no ghost is a law of the original (`ghost_laws`);
- `ghost_run`: every run of the original is, outside the ghosts, a run of the ghosted machine that takes the same requests;
- `ever_meaning`: along a run, a ghost that starts at 0 and is set to 1 by a step where `c` holds (compose.ts's `ever`) is
  1 exactly when some step before took a request where `c` held.
-/

namespace Kern

structure Ghosted where
  orig : FMMachine
  ghosts : List (Nat × E × E)   -- (variable, start over the params, step over the state before, the request and flags)

def Ghosted.vars (g : Ghosted) : List Nat := g.ghosts.map (·.1)

-- The ghosted machine: the original, each ghost's start and step added.
def Ghosted.full (g : Ghosted) : FMMachine :=
  ⟨{ g.orig.m with init := g.orig.m.init ++ g.ghosts.map (fun x => (x.1, x.2.1)), step := g.orig.m.step ++ g.ghosts.map (fun x => (x.1, x.2.2)) }, g.orig.flags⟩

-- The ghosts are new names, and nothing of the original reads them.
def ghostOk (g : Ghosted) : Bool :=
  distinct g.vars
    && g.vars.all (fun v => !(g.orig.m.inputs ++ g.orig.m.init.map (·.1) ++ g.orig.m.step.map (·.1) ++ flagVars g.orig.flags).contains v)
    && avoids g.vars g.orig.m.pre && avoids g.vars g.orig.m.assume && g.orig.flags.all (fun p => avoids g.vars p.2)
    && g.orig.m.step.all (fun p => avoidsE g.vars p.2) && g.orig.m.init.all (fun p => avoidsE g.vars p.2)
    && g.orig.m.writes.all (fun w => avoidsE g.vars w.2.1 && avoidsE g.vars w.2.2)

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

-- A run of the original lifted to the ghosted machine from a ghosted state s0 that agrees with its first: the ghosts
-- move with each request the run takes.
def ghostFrom (g : Ghosted) (run : FRun g.orig) (s0 : (Nat → Nat) × (Nat → Nat → Nat)) : Nat → (Nat → Nat) × (Nat → Nat → Nat)
  | 0 => s0
  | n + 1 => ((applyS g.full.m.step (decideFlags g.full.flags (withInputs g.full.m.inputs (ghostFrom g run s0 n).1 (run.req n)) (ghostFrom g run s0 n).2) (ghostFrom g run s0 n).2),
      writeMaps g.full.m.writes (decideFlags g.full.flags (withInputs g.full.m.inputs (ghostFrom g run s0 n).1 (run.req n)) (ghostFrom g run s0 n).2) (ghostFrom g run s0 n).2)

section ghost
variable (g : Ghosted) (hg : ghostOk g = true)
include hg

theorem ghostOk_parts :
    distinct g.vars = true ∧ (∀ v ∈ g.vars, v ∉ g.orig.m.inputs ++ g.orig.m.init.map (·.1) ++ g.orig.m.step.map (·.1) ++ flagVars g.orig.flags)
      ∧ avoids g.vars g.orig.m.pre = true ∧ avoids g.vars g.orig.m.assume = true ∧ (∀ p ∈ g.orig.flags, avoids g.vars p.2 = true)
      ∧ (∀ p ∈ g.orig.m.step, avoidsE g.vars p.2 = true) ∧ (∀ p ∈ g.orig.m.init, avoidsE g.vars p.2 = true)
      ∧ (∀ w ∈ g.orig.m.writes, avoidsE g.vars w.2.1 = true ∧ avoidsE g.vars w.2.2 = true) := by
  simp only [ghostOk, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨hd, hn⟩, hp⟩, ha⟩, hf⟩, hs⟩, hi⟩, hw⟩ := hg
  exact ⟨hd, fun v hv h => (by have := hn v hv; rw [List.contains_iff_mem.mpr h] at this; cases this), hp, ha, hf, hs, hi, hw⟩

-- One step from states that agree outside the ghosts, with the same request: allowed alike, and to states that agree
-- outside the ghosts, with the same maps.
theorem ghost_step {ρ ρg : Nat → Nat} (hag : Agree g.vars ρg ρ) (M : Nat → Nat → Nat) (ι : Nat → Nat) :
    (evalC (decideFlags g.full.flags (withInputs g.full.m.inputs ρg ι) M) M g.full.m.assume
        = evalC (decideFlags g.orig.flags (withInputs g.orig.m.inputs ρ ι) M) M g.orig.m.assume)
      ∧ Agree g.vars (applyS g.full.m.step (decideFlags g.full.flags (withInputs g.full.m.inputs ρg ι) M) M)
          (applyS g.orig.m.step (decideFlags g.orig.flags (withInputs g.orig.m.inputs ρ ι) M) M)
      ∧ writeMaps g.full.m.writes (decideFlags g.full.flags (withInputs g.full.m.inputs ρg ι) M) M
          = writeMaps g.orig.m.writes (decideFlags g.orig.flags (withInputs g.orig.m.inputs ρ ι) M) M := by
  obtain ⟨_, hn, _, ha, hf, hs, _, hw⟩ := ghostOk_parts g hg
  have hin : Agree g.vars (withInputs g.orig.m.inputs ρg ι) (withInputs g.orig.m.inputs ρ ι) := fun i hi => by
    simp only [withInputs]; split
    · rfl
    · exact hag i hi
  have hD := decide_agree_on hf M hin
  refine ⟨?_, fun i hi => ?_, ?_⟩
  · show evalC (decideFlags g.orig.flags (withInputs g.orig.m.inputs ρg ι) M) M g.orig.m.assume = _
    exact congrC _ _ M _ (fun i hi => hD i (avoids_occ ha hi))
  · show applyS (g.orig.m.step ++ g.ghosts.map (fun x => (x.1, x.2.2))) (decideFlags g.orig.flags (withInputs g.orig.m.inputs ρg ι) M) M i = _
    rw [applyS_append_other (by simpa [Ghosted.vars] using hi)]
    simp only [applyS]
    cases hst : assoc g.orig.m.step i with
    | none => exact hD i hi
    | some e =>
      have hm : (i, e) ∈ g.orig.m.step := by
        simp only [assoc, Option.map_eq_some_iff] at hst
        obtain ⟨q, hq, rfl⟩ := hst
        obtain ⟨hqm, hqv⟩ := lookup_some hq
        simp only [beq_iff_eq] at hqv
        rw [← hqv]; exact hqm
      exact congrE _ _ M e (fun j hj => hD j (avoidsE_occ (hs (i, e) hm) hj))
  · show writeMaps g.orig.m.writes (decideFlags g.orig.flags (withInputs g.orig.m.inputs ρg ι) M) M = _
    funext mp key
    simp only [writeMaps]
    cases hl : lookup (fun w => w.1 == mp) g.orig.m.writes with
    | none => rfl
    | some w =>
      obtain ⟨h1, h2⟩ := hw w (lookup_some hl).1
      simp only [congrE _ _ M w.2.1 (fun j hj => hD j (avoidsE_occ h1 hj)), congrE _ _ M w.2.2 (fun j hj => hD j (avoidsE_occ h2 hj))]

/-- Every reachable state of the original is, outside the ghosts, a reachable state of the ghosted machine. -/
theorem ghost_reach : ∀ {ρ M}, FMReach g.orig ρ M → ∃ ρg, FMReach g.full ρg M ∧ Agree g.vars ρg ρ := by
  obtain ⟨_, _, hp, _, _, _, hi, _⟩ := ghostOk_parts g hg
  intro ρ M hr
  induction hr with
  | start ρ M hM h0 =>
    refine ⟨applyS g.full.m.init ρ M, FMReach.start ρ M hM h0, fun i hi => ?_⟩
    show applyS (g.orig.m.init ++ g.ghosts.map (fun x => (x.1, x.2.1))) ρ M i = applyS g.orig.m.init ρ M i
    exact applyS_append_other (by simpa [Ghosted.vars] using hi) ρ M
  | step ρ M ι _ ha ih =>
    obtain ⟨ρg, hrg, hag⟩ := ih
    obtain ⟨hA, hS, hW⟩ := ghost_step g hg hag M ι
    refine ⟨_, ?_, hS⟩
    rw [← hW]
    exact FMReach.step ρg M ι hrg (by rw [hA]; exact ha)

/-- A law of the ghosted machine that reads no ghost holds in every reachable state of the original. -/
theorem ghost_laws (ps : List MEntry) (hl : checkFMMachine g.full ps = true) :
    ∀ ρ M, FMReach g.orig ρ M → ∀ e ∈ ps, avoids g.vars e.law.holds = true → e.law.Holds ρ M := by
  intro ρ M hr e he hav
  obtain ⟨ρg, hrg, hag⟩ := ghost_reach g hg hr
  exact holds_transfer (V := g.vars) (MS := []) e.law hav (by simp [avoidsMaps]) (fun i hi => (hag i hi).symm) (fun _ _ => rfl)
    (fmmachine_sound g.full ps hl ρg M hrg e he)
theorem ghostFrom_agree (run : FRun g.orig) (s0 : (Nat → Nat) × (Nat → Nat → Nat)) (hM0 : s0.2 = (run.st 0).2) (hA0 : Agree g.vars s0.1 (run.st 0).1) :
    ∀ n, (ghostFrom g run s0 n).2 = (run.st n).2 ∧ Agree g.vars (ghostFrom g run s0 n).1 (run.st n).1
  | 0 => ⟨hM0, hA0⟩
  | n + 1 => by
    obtain ⟨hM, hag⟩ := ghostFrom_agree run s0 hM0 hA0 n
    obtain ⟨_, hS, hW⟩ := ghost_step g hg hag (run.st n).2 (run.req n)
    rw [run.next n]
    simp only [ghostFrom, hM]
    exact ⟨hW, hS⟩

omit hg in
def ghostRun (hg : ghostOk g = true) (run : FRun g.orig) (s0 : (Nat → Nat) × (Nat → Nat → Nat)) (hr : FMReach g.full s0.1 s0.2) (hM0 : s0.2 = (run.st 0).2)
    (hA0 : Agree g.vars s0.1 (run.st 0).1) : FRun g.full :=
  ⟨ghostFrom g run s0, run.req, hr,
    fun n => by
      obtain ⟨hM, hag⟩ := ghostFrom_agree g hg run s0 hM0 hA0 n
      obtain ⟨hA, _, _⟩ := ghost_step g hg hag (run.st n).2 (run.req n)
      rw [hM, hA]; exact run.allowed n,
    fun n => rfl⟩

/-- Every run of the original is, outside the ghosts, a run of the ghosted machine taking the same requests. -/
theorem ghost_run (run : FRun g.orig) : ∃ run' : FRun g.full, run'.req = run.req ∧ ∀ n, (run'.st n).2 = (run.st n).2 ∧ Agree g.vars (run'.st n).1 (run.st n).1 :=
  ⟨ghostRun g hg run (Classical.choose (ghost_reach g hg run.start), (run.st 0).2) (Classical.choose_spec (ghost_reach g hg run.start)).1 rfl
      (Classical.choose_spec (ghost_reach g hg run.start)).2, rfl,
    ghostFrom_agree g hg run (Classical.choose (ghost_reach g hg run.start), (run.st 0).2) rfl (Classical.choose_spec (ghost_reach g hg run.start)).2⟩

/-- A run of the original from its start lifts to one of the ghosted machine from its start: each ghost at its start term. -/
theorem ghost_run_start (run : FRun g.orig) {ρ0 : Nat → Nat} {M0 : Nat → Nat → Nat} (hM : StartMaps g.orig.m M0) (hp : evalC ρ0 M0 g.orig.m.pre = true)
    (hst : run.st 0 = (applyS g.orig.m.init ρ0 M0, M0)) :
    ∃ run' : FRun g.full, run'.req = run.req ∧ run'.st 0 = (applyS g.full.m.init ρ0 M0, M0) ∧ ∀ n, (run'.st n).2 = (run.st n).2 ∧ Agree g.vars (run'.st n).1 (run.st n).1 := by
  have hA0 : Agree g.vars (applyS g.full.m.init ρ0 M0) (run.st 0).1 := fun i hi => by
    rw [hst]
    show applyS (g.orig.m.init ++ g.ghosts.map (fun x => (x.1, x.2.1))) ρ0 M0 i = applyS g.orig.m.init ρ0 M0 i
    exact applyS_append_other (by simpa [Ghosted.vars] using hi) ρ0 M0
  have hM0 : M0 = (run.st 0).2 := by rw [hst]
  exact ⟨ghostRun g hg run (applyS g.full.m.init ρ0 M0, M0) (FMReach.start ρ0 M0 hM hp) hM0 hA0, rfl, rfl, ghostFrom_agree g hg run (applyS g.full.m.init ρ0 M0, M0) hM0 hA0⟩

-- The flags a step decides read alike in a run and its lift: the flag conditions read no ghost.
theorem ghost_view (run : FRun g.orig) (run' : FRun g.full) (hreq : run'.req = run.req)
    (hag : ∀ n, (run'.st n).2 = (run.st n).2 ∧ Agree g.vars (run'.st n).1 (run.st n).1) {c : C} (hc : avoids g.vars c = true) (n : Nat) :
    evalC (decideFlags g.orig.flags (withInputs g.orig.m.inputs (run'.st n).1 (run'.req n)) (run'.st n).2) (run'.st n).2 c
      = evalC (decideFlags g.orig.flags (withInputs g.orig.m.inputs (run.st n).1 (run.req n)) (run.st n).2) (run.st n).2 c := by
  obtain ⟨_, _, _, _, hf, _, _, _⟩ := ghostOk_parts g hg
  obtain ⟨hM, hA⟩ := hag n
  rw [hM, hreq]
  have hin : Agree g.vars (withInputs g.orig.m.inputs (run'.st n).1 (run.req n)) (withInputs g.orig.m.inputs (run.st n).1 (run.req n)) := fun i hi => by
    simp only [withInputs]; split
    · rfl
    · exact hA i hi
  exact congrC _ _ _ c (fun i hi => decide_agree_on hf (run.st n).2 hin i (avoids_occ hc hi))
end ghost

/-- What `ever` means: along a run of the ghosted machine where the ghost x starts at 0, with x's step `if c then 1
else x`, x is 1 at step n exactly when some step before n took a request where c held (read where that step reads:
its request, its flags decided). -/
theorem ever_meaning (g : Ghosted) (hg : ghostOk g = true) {x : Nat} {s0 : E} {c : C} (hx : (x, s0, .ite c (.const 1) (.var x)) ∈ g.ghosts)
    (run : FRun g.full) (h0 : (run.st 0).1 x = 0) :
    ∀ n, (run.st n).1 x = 1 ↔ ∃ i, i < n ∧ evalC (decideFlags g.orig.flags (withInputs g.orig.m.inputs (run.st i).1 (run.req i)) (run.st i).2) (run.st i).2 c = true := by
  obtain ⟨hd, hn, _⟩ := ghostOk_parts g hg
  have hxv : x ∈ g.vars := List.mem_map_of_mem hx
  have hxo := hn x hxv
  -- x's step term in the ghosted machine is its ghost step.
  have hassoc : assoc g.full.m.step x = some (.ite c (.const 1) (.var x)) := by
    show assoc (g.orig.m.step ++ g.ghosts.map (fun y => (y.1, y.2.2))) x = _
    simp only [assoc, lookup_append]
    rw [lookup_none (fun p hp => by simp only [beq_eq_false_iff_ne]; intro he; exact hxo (by rw [← he]; exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hp))))]
    have hl : lookup (fun p => p.1 == x) (g.ghosts.map (fun y => (y.1, y.2.2))) = some (x, .ite c (.const 1) (.var x)) := by
      have hd' : distinct ((g.ghosts.map (fun y => (y.1, y.2.2))).map (·.1)) = true := by
        rw [List.map_map]; exact hd
      have hm : (x, E.ite c (.const 1) (.var x)) ∈ g.ghosts.map (fun y => (y.1, y.2.2)) := List.mem_map.mpr ⟨_, hx, rfl⟩
      exact lookup_unique_fst hd' hm
    simp [hl]
  intro n
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have hnext := run.next n
    have hst : (run.st (n + 1)).1 x = if evalC (decideFlags g.orig.flags (withInputs g.orig.m.inputs (run.st n).1 (run.req n)) (run.st n).2) (run.st n).2 c = true
        then 1 else (run.st n).1 x := by
      rw [hnext]
      show applyS g.full.m.step (decideFlags g.orig.flags (withInputs g.orig.m.inputs (run.st n).1 (run.req n)) (run.st n).2) (run.st n).2 x = _
      simp only [applyS, hassoc, evalE]
      rw [decide_other (fun h => hxo (List.mem_append_right _ h)), withInputs_other (fun h => hxo (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))))]
    rw [hst]
    constructor
    · intro h1
      by_cases hc : evalC (decideFlags g.orig.flags (withInputs g.orig.m.inputs (run.st n).1 (run.req n)) (run.st n).2) (run.st n).2 c = true
      · exact ⟨n, Nat.lt_succ_self n, hc⟩
      · rw [if_neg hc] at h1
        obtain ⟨i, hi, hci⟩ := ih.mp h1
        exact ⟨i, Nat.lt_succ_of_lt hi, hci⟩
    · rintro ⟨i, hi, hci⟩
      by_cases hc : evalC (decideFlags g.orig.flags (withInputs g.orig.m.inputs (run.st n).1 (run.req n)) (run.st n).2) (run.st n).2 c = true
      · rw [if_pos hc]
      · rw [if_neg hc]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact ih.mpr ⟨i, hi, hci⟩
        · exact absurd hci hc

end Kern

#print axioms Kern.ghost_reach
#print axioms Kern.ghost_laws
#print axioms Kern.ghost_run
#print axioms Kern.ever_meaning
#print axioms Kern.ghost_run_start

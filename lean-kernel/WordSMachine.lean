import WordReach

/-! Generic trusted certificate extension: the original machine guards and goal
hypothesis membership remain mandatory. Extras are semantics, not assumptions. -/
namespace Kern.WordSMachine
open Kern

def checkInWithFacts (base extra : List C) (k : Cert) : Bool :=
  checkIn (base ++ extra) k

def checkSMachineWithFacts (s : SMachine) (ps : List SEntry) (extra : List C) : Bool :=
  sOk s && avoids (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)) s.f.m.pre && !readsC s.f.m.pre
    && sTermsOk s (flagVars s.f.flags) && factsOk s
    && ps.all fun e =>
      avoids (s.extVars ++ flagVars s.f.flags) e.law.holds && avoidsMaps s.carried e.law.holds
        && !(s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains e.sk
        && ps.all (fun e' => !occC e.sk e'.law.holds) && !occC e.sk s.f.m.pre && s.f.m.init.all (fun p => !occE e.sk p.2)
        && skFresh s e.sk && key2Ok s ps e
        && checkIn (sStartGoal s e ++ extra) e.start
        && checkIn (sStepGoal s ps e ++ extra) e.step

theorem sound_in_with (base extra : List C) (k : Cert)
    (h : checkInWithFacts base extra k = true) (X : Nat → Nat) (N : Nat → Nat → Nat)
    (hextra : ∀ c ∈ extra, evalC X N c = true) :
    ¬ ∀ c ∈ base, evalC X N c = true := by
  intro hbase
  exact sound_in (base ++ extra) k h X N (fun c hc => by
    rcases List.mem_append.mp hc with hc | hc
    · exact hbase c hc
    · exact hextra c hc)


variable (extra : List C)
variable {P : (Nat → Nat → Nat) → Prop}

theorem word_sOk_of {s : SMachine} {ps : List SEntry} (hl : checkSMachineWithFacts s ps extra = true) : sOk s = true := by
  simp only [checkSMachineWithFacts, Bool.and_eq_true] at hl; exact hl.1.1.1.1.1

theorem word_spre_parts {s : SMachine} {ps : List SEntry} (hl : checkSMachineWithFacts s ps extra = true) :
    avoids (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)) s.f.m.pre = true ∧ readsC s.f.m.pre = false := by
  simp only [checkSMachineWithFacts, Bool.and_eq_true] at hl; exact ⟨hl.1.1.1.1.2, by simpa using hl.1.1.1.2⟩

theorem word_sfacts_ok {s : SMachine} {ps : List SEntry} (hl : checkSMachineWithFacts s ps extra = true) : factsOk s = true := by
  simp only [checkSMachineWithFacts, Bool.and_eq_true] at hl; exact hl.1.2

theorem word_slaws_avoid {s : SMachine} {ps : List SEntry} (hl : checkSMachineWithFacts s ps extra = true) :
    ∀ l ∈ ps.map (·.law), avoids s.extVars l.holds = true ∧ avoidsMaps s.carried l.holds = true := by
  simp only [checkSMachineWithFacts, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hl
  intro l hl'
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp hl'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hl.2 e' he'
  refine ⟨?_, h2⟩
  simp only [avoids, List.all_append, Bool.and_eq_true] at h1 ⊢; exact h1.1

theorem word_skey2_parts {s : SMachine} {ps : List SEntry} (h : checkSMachineWithFacts s ps extra = true) {e : SEntry} (he : e ∈ ps) {g : Nat} (hg : g ∈ e.keys2) :
    skFresh s g = true ∧ (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains g = false
      ∧ occC g s.f.m.pre = false ∧ (∀ p ∈ s.f.m.init, occE g p.2 = false) ∧ (∀ e' ∈ ps, occC g e'.law.holds = false ∨ g ∈ e'.keys2)
      ∧ e.law.key ≠ some g := by
  simp only [checkSMachineWithFacts, List.all_eq_true, Bool.and_eq_true] at h
  have hk := (h.2 e he).1.1.2
  simp only [key2Ok, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, Bool.or_eq_true, List.contains_iff_mem] at hk
  obtain ⟨⟨⟨⟨⟨hkey, hf⟩, hc⟩, hp⟩, hi⟩, hall⟩ := hk g hg
  exact ⟨hf, hc, hp, hi, fun e' he' => (by have := (hall e' he').1; simpa using this), hkey⟩

theorem word_skeys_apart {s : SMachine} {ps : List SEntry} (h : checkSMachineWithFacts s ps extra = true) : ∀ e ∈ ps, ∀ k, e.law.key = some k → k ∉ e.keys2 :=
  fun e he k hk hg => (word_skey2_parts extra h he hg).2.2.2.2.2 hk

/-- The start: at params that meet the precondition and the facts, with maps as declared, every law holds. -/
theorem word_sstart_case (s : SMachine) (ps : List SEntry) (extra : List C) (h : checkSMachineWithFacts s ps extra = true)
    (hExtra : ∀ X N, P N → ∀ c ∈ extra, evalC X N c = true) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hWorld : P M)
    (hM : StartMaps s.f.m M) (h0 : evalC ρ M s.f.m.pre = true) (hfa : ∀ l ∈ s.facts, l.Holds ρ M) (hpf : s.PFacts ρ M) :
    ∀ e ∈ ps, e.law.Holds (applyS s.f.m.init ρ M) M := by
  simp only [checkSMachineWithFacts, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hfok⟩, h⟩ := h
  intro e he
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hfresh⟩, hslaw⟩, hspre⟩, hsinit⟩, hskf⟩, _⟩, hst⟩, _⟩ := h e he
  refine goalOf_holds e.law (hslaw e he) _ M (fun v => ?_)
  apply Decidable.byContradiction; intro hn
  apply sound_in_with (sStartGoal s e) extra e.start hst (upd ρ e.sk v) M (hExtra _ _ hWorld)
  intro c hc
  simp only [sStartGoal, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | hc) | rfl
  · rw [congrC _ ρ M s.f.m.pre (fun i hi => by
      simp only [upd]; split
      · rename_i hik; subst hik; simp [hspre] at hi
      · rfl)]
    exact h0
  · -- The facts hold at the start, and read not the skolem.
    exact facthyps_true s e.finsts e.pfinsts _ M (fun f hf => (pfactsOk_parts hfok f hf).2.2)
      (facts_frame s hfok [e.sk] [] (fun l hl => by simp [avoids, (skFresh_parts hskf).2.2.2.2.2.2 l hl])
        (fun _ _ => by simp [avoidsMaps]) (fun i _ hik => by simp only [upd]; rw [if_neg (by simpa using hik)]) (fun _ _ _ => rfl) hfa)
      (pfacts_frame s hfok [e.sk] [] (fun f hf => by simp [avoids, skFresh_pfacts hskf f hf])
        (fun _ _ => by simp [avoidsMaps]) (fun i _ hik => by simp only [upd]; rw [if_neg (by simpa using hik)]) (fun _ _ _ => rfl) hpf) c hc
  · have hrd : ∀ mp k, evalE (upd ρ e.sk v) M (rdStart s.f.m mp k) = M mp (evalE (upd ρ e.sk v) M k) := by
      intro mp k
      simp only [rdStart]
      split
      · rename_i p hp
        have ⟨hm, hq⟩ := lookup_some hp
        simp only [beq_iff_eq] at hq
        simp only [evalE]; rw [← hq, hM p hm]
      · rfl
    simp only [evalC, substR_evalC _ _ _ M M hrd]
    rw [applyS_upd (fun h => by simp [h] at hfresh) (by simpa [List.all_eq_true] using hsinit)]
    simpa using hn


theorem word_sstep_case (s : SMachine) (ps : List SEntry) (extra : List C) (h : checkSMachineWithFacts s ps extra = true)
    (hExtra : ∀ X N, P N → ∀ c ∈ extra, evalC X N c = true) (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) (hWorld : P (withCarried s M κ)) (hp0 : evalC ρ M s.f.m.pre = true) (hfa : ∀ l ∈ s.facts, l.Holds ρ M) (hpf : s.PFacts ρ M)
    (ih : ∀ e ∈ ps, e.Holds ρ M) (ha : evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume = true) :
    ∀ e ∈ ps, e.law.Holds (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2 := by
  have hlav := word_slaws_avoid extra h
  have hkk := word_skeys_apart extra h
  simp only [checkSMachineWithFacts, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hs, hpre⟩, hrp⟩, hterms⟩, hfok⟩, h⟩ := h
  obtain ⟨hfav, hstp, hwr, hev⟩ := sTermsOk_parts hterms
  intro e he
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hlx, hlm⟩, hfresh⟩, hslaw⟩, hspre⟩, _⟩, hskf⟩, _⟩, _⟩, hst⟩ := h e he
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩ := skFresh_parts hskf
  have hnot : e.sk ∉ s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1) := fun hm => by
    rw [List.contains_iff_mem.mpr hm] at hfresh; cases hfresh
  have hskE : e.sk ∉ s.extVars := fun hm => hnot (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hm)))
  have hskF : e.sk ∉ flagVars s.f.flags := fun hm => hnot (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hm)))
  -- The law at the next state with the carried maps in place reads as at the next state: it reads none of them.
  refine holds_transfer (V := []) (MS := s.carried) (ρ' := (sNext s ρ M ι κ).1) (M' := withCarried s (sNext s ρ M ι κ).2 κ) e.law (by simp [avoids]) hlm (fun i _ => rfl)
    (fun mp hmp => by simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmp)]) ?_
  refine goalOf_holds e.law (hslaw e he) _ _ (fun v => ?_)
  apply Decidable.byContradiction; intro hn
  -- The frame runs from the state with the skolem set to v: the machine reads it nowhere, so the step is the same.
  obtain ⟨hNext, hView, _⟩ := fresh_parts hskf (by simpa [List.contains_iff_mem] using hnot) ρ M ι κ v
  let W := withExt s (upd ρ e.sk v) (sReq s (upd ρ e.sk v) M ι κ)
  let M0 := withCarried s M κ
  have hH : ∀ Z, SHead s Z [] W M0 [] getRd (upd ρ e.sk v) M [] [] ι κ := fun Z => by
    refine ⟨fun i _ => ?_, fun mp k _ => ?_⟩
    · show applyS (frameSub [] []) W M0 i = W i
      simp only [frameSub, List.map_nil, List.append_nil, applyS_nil']
    · simp [frameRd, getRd, lookup, evalE, M0]
  have hD : SDenotes s (flagVars s.f.flags) [] W M0 [] getRd (upd ρ e.sk v) M := by
    refine ⟨fun i hie _ => ?_, fun mp k hmp _ => ?_⟩
    · rw [applyS_nil']; simp only [W, withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hie)]
    · simp only [getRd, evalE, M0, withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmp)]
  have hD' := sstep_denotes s (flagVars s.f.flags) [] W M0 hs (fun v hv => hv) hfav [] [] ι κ hD (hH _) (fun p hp => by simp at hp)
    hstp (fun w hw => (hwr w hw).1) hev (fun _ _ => by simp [avoidsMapsE]) (fun _ _ => by simp [avoidsMapsE]) (fun _ _ => by simp [avoidsMapsE])
  apply sound_in_with (sStepGoal s ps e) extra e.step hst W M0 (hExtra _ _ (by simpa [M0] using hWorld))
  intro c hc
  simp only [sStepGoal, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, List.mem_map] at hc
  rcases hc with ((rfl | hc) | ⟨c', hc', rfl⟩) | rfl
  · -- The precondition: it reads no map, no request and not the skolem.
    rw [noReadsC W M0 M s.f.m.pre hrp, congrC W ρ M s.f.m.pre (fun i hi => ?_)]
    · exact hp0
    · have hi1 := avoids_occ hpre hi
      have hik : i ≠ e.sk := fun h' => by rw [h'] at hi; simp [hspre] at hi
      simp only [W, withExt]
      rw [if_neg (fun h' => hi1 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.contains_iff_mem.mp h')))))]
      simp only [upd, if_neg hik]
  · -- The facts: they read no request, not the skolem, and no map a request carries.
    exact facthyps_true s e.finsts e.pfinsts W M0 (fun f hf => (pfactsOk_parts hfok f hf).2.2)
      (facts_frame s hfok [e.sk] [] (fun l hl => by simp [avoids, hf7 l hl])
        (fun _ _ => by simp [avoidsMaps])
        (fun i hie hik => by simp only [W, withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hie)]; simp only [upd]; rw [if_neg (by simpa using hik)])
        (fun mp hmc _ => by simp only [M0, withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmc)]) hfa)
      (pfacts_frame s hfok [e.sk] [] (fun f hf => by simp [avoids, skFresh_pfacts hskf f hf])
        (fun _ _ => by simp [avoidsMaps])
        (fun i hie hik => by simp only [W, withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hie)]; simp only [upd]; rw [if_neg (by simpa using hik)])
        (fun mp hmc _ => by simp only [M0, withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmc)]) hpf) c hc
  · -- The entries hold at the state with the skolem set (their laws don't read it), so in the goal's view of it, and so
    -- does each pair's law; the assumption reads the skolem nowhere either.
    have hA : evalC (sView s (upd ρ e.sk v) M ι κ).1 (sView s (upd ρ e.sk v) M ι κ).2 s.f.m.assume = true := by
      rw [hView]; dsimp only
      rw [congrC _ (sView s ρ M ι κ).1 _ _ (fun i hi => by
        have hik : i ≠ e.sk := fun h' => by rw [h', hf3] at hi; cases hi
        simp only [upd, if_neg hik])]
      exact ha
    have hallY : ∀ e' ∈ ps, e'.Holds W M0 := fun e' he' =>
      sentry_transfer (hlav e'.law (List.mem_map_of_mem he')).1 (hlav e'.law (List.mem_map_of_mem he')).2
        (fun i hi => by simp only [W, withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hi)])
        (fun mp hmp => by simp only [M0, withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmp)])
        (sentry_upd (Or.inl (hslaw e' he')) v (ih e' he'))
    exact sframe_hyps s [] [] W M0 hs (sLaws ps e.pinsts) (sInsts ps e.insts e.pinsts) e.qinsts
      (fun l hl => by
        rcases List.mem_append.mp hl with hl | hl
        · obtain ⟨e', he', rfl⟩ := List.mem_map.mp hl; exact SEntry.holds_law (hallY e' he')
        · exact pairLaws_hold ps e.pinsts hkk hallY l hl)
      (hH []) (fun _ _ => by simp [avoids]) (fun _ _ => by simp [avoids]) (fun _ _ => by simp [avoidsMaps]) hA (by simp [trueC, evalC, evalE]) c' hc'
  · -- The goal, read across the step: the maps a request carries read as carried, the rest as the step leaves them.
    have hrd' : ∀ mp k, evalE W M0 (stepRdS s (frameSub [] []) (frameRd [] getRd) mp k) = withCarried s (sNext s ρ M ι κ).2 κ mp (evalE W M0 k) := by
      intro mp k
      by_cases hmp : mp ∈ s.carried
      · have hne : lookup (fun w => w.1 == mp) s.every = none := lookup_none (fun w hw => by
          simp only [beq_eq_false_iff_ne]; intro h'; exact (hev w hw).2.2.2.2.1 (by rw [h']; exact hmp))
        have hnw : lookup (fun w : Nat × E × E => w.1 == mp) s.f.m.writes = none := lookup_none (fun w hw => by
          simp only [beq_eq_false_iff_ne]; intro h'; exact (hwr w hw).2 (by rw [h']; exact hmp))
        simp only [stepRdS, hne, stepRd, hnw]
        simp [frameRd, getRd, lookup, evalE, M0, withCarried, hmp]
      · rw [hD'.2 mp k hmp (by simp), hNext]; simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmp)]
    simp only [evalC]
    rw [substR_evalC _ _ W M0 _ hrd', goalOf_agree e.law e.sk _ (X' := upd (sNext s ρ M ι κ).1 e.sk v)
      (by rw [hD'.1 e.sk hskE hskF, hNext]) (fun i hi => ?_)]
    · simpa using hn
    · have hi1 := avoids_occ hlx hi
      rw [hD'.1 i (fun h' => hi1 (List.mem_append_left _ h')) (fun h' => hi1 (List.mem_append_right _ h')), hNext]

/-- The induction rule with sets: for params that meet the precondition, maps that start as declared and functions that
meet the facts, every entry of an accepted proof holds in every reachable state (a law about several keys at every value
of its further keys), whatever maps each request carries. -/

theorem machine_sound_under_world (s : SMachine) (ps : List SEntry) (extra : List C) (h : checkSMachineWithFacts s ps extra = true)
    (hExtra : ∀ X N, P N → ∀ c ∈ extra, evalC X N c = true)
    (hWorld : ∀ ρ M, SReach s ρ M → P M) (hCarried : ∀ M κ, P M → P (withCarried s M κ)) :
    ∀ ρ M, SReach s ρ M → ∀ e ∈ ps, e.Holds ρ M := by
  have hpre := word_spre_parts extra h
  have hfok := word_sfacts_ok extra h
  -- Facts at a state hold with a further key set: they read no further key.
  have hfacts : ∀ {ρ : Nat → Nat} {M : Nat → Nat → Nat} {g : Nat}, skFresh s g = true → (∀ l ∈ s.facts, l.Holds ρ M) → ∀ w, ∀ l ∈ s.facts, l.Holds (upd ρ g w) M := by
    intro ρ M g hf hfa w
    exact facts_frame s hfok [g] [] (fun l hl => by simp [avoids, (skFresh_parts hf).2.2.2.2.2.2 l hl]) (fun _ _ => by simp [avoidsMaps])
      (fun i _ hig' => by simp only [upd]; rw [if_neg (by simpa using hig')]) (fun _ _ _ => rfl) hfa
  have hpfacts : ∀ {ρ : Nat → Nat} {M : Nat → Nat → Nat} {g : Nat}, skFresh s g = true → s.PFacts ρ M → ∀ w, s.PFacts (upd ρ g w) M := by
    intro ρ M g hf hpf w
    exact pfacts_frame s hfok [g] [] (fun f hfm => by simp [avoids, skFresh_pfacts hf f hfm]) (fun _ _ => by simp [avoidsMaps])
      (fun i _ hig' => by simp only [upd]; rw [if_neg (by simpa using hig')]) (fun _ _ _ => rfl) hpf
  have hpreu : ∀ {ρ : Nat → Nat} {M : Nat → Nat → Nat} {g : Nat}, occC g s.f.m.pre = false → evalC ρ M s.f.m.pre = true → ∀ w, evalC (upd ρ g w) M s.f.m.pre = true := by
    intro ρ M g hpg h0 w
    rw [congrC _ ρ M s.f.m.pre (fun i hi => by have hig' : i ≠ g := (fun h' => by rw [h', hpg] at hi; cases hi); simp only [upd, if_neg hig'])]; exact h0
  intro ρ M hr
  induction hr with
  | start ρ M hM h0 hfa hpf =>
    intro e he
    -- Each further key set in turn, from a start state that meets the precondition and the facts.
    suffices hs : ∀ gs : List Nat, (∀ g ∈ gs, g ∈ e.keys2) → ∀ ρ', evalC ρ' M s.f.m.pre = true → (∀ l ∈ s.facts, l.Holds ρ' M) →
        s.PFacts ρ' M → holdsOver e.law M gs (applyS s.f.m.init ρ' M) from hs e.keys2 (fun g hg => hg) ρ h0 hfa hpf
    intro gs
    induction gs with
    | nil => intro _ ρ' hp hf hq; exact word_sstart_case s ps extra h hExtra ρ' M (hWorld _ _ (SReach.start _ _ hM hp hf hq)) hM hp hf hq e he
    | cons g gs ih =>
      intro hsub ρ' hp hf hq w
      obtain ⟨hfr, hc, hpg, hig, _, _⟩ := word_skey2_parts extra h he (hsub g List.mem_cons_self)
      have hI := (fresh_parts hfr hc ρ' M (fun _ => 0) (fun _ _ => 0) 0).2.2
      rw [← applyS_upd hI (by simpa [List.all_eq_true] using hig)]
      exact ih (fun g' hg' => hsub g' (List.mem_cons_of_mem _ hg')) (upd ρ' g w) (hpreu hpg hp w) (hfacts hfr hf w) (hpfacts hfr hq w)
  | step ρ M ι κ hr ha ih =>
    intro e he
    suffices hs : ∀ gs : List Nat, (∀ g ∈ gs, g ∈ e.keys2) → ∀ ρ', evalC ρ' M s.f.m.pre = true → (∀ l ∈ s.facts, l.Holds ρ' M) →
        s.PFacts ρ' M → (∀ e' ∈ ps, e'.Holds ρ' M) → evalC (sView s ρ' M ι κ).1 (sView s ρ' M ι κ).2 s.f.m.assume = true →
        holdsOver e.law (sNext s ρ' M ι κ).2 gs (sNext s ρ' M ι κ).1 from
      hs e.keys2 (fun g hg => hg) ρ (pre_sreach s hpre.1 hpre.2 hr) (facts_sreach s hfok hr) (pfacts_sreach s hfok hr) ih ha
    intro gs
    induction gs with
    | nil => intro _ ρ' hp hf hq hi ha'; exact word_sstep_case s ps extra h hExtra ρ' M ι κ (hCarried M κ (hWorld _ _ hr)) hp hf hq hi ha' e he
    | cons g gs ihg =>
      intro hsub ρ' hp hf hq hi ha' w
      obtain ⟨hfr, hc, hpg, _, hall, _⟩ := word_skey2_parts extra h he (hsub g List.mem_cons_self)
      obtain ⟨hNext, hView, _⟩ := fresh_parts hfr hc ρ' M ι κ w
      have := ihg (fun g' hg' => hsub g' (List.mem_cons_of_mem _ hg')) (upd ρ' g w) (hpreu hpg hp w) (hfacts hfr hf w) (hpfacts hfr hq w)
        (fun e' he' => sentry_upd (hall e' he') w (hi e' he'))
        (by
          rw [hView]; dsimp only
          rw [congrC _ (sView s ρ' M ι κ).1 _ _ (fun i hi => by
            have hig' : i ≠ g := fun h' => by rw [h', (skFresh_parts hfr).2.2.1] at hi; cases hi
            simp only [upd, if_neg hig'])]
          exact ha')
      rw [hNext] at this; exact this
theorem concrete_smachine_sound (w : WordReach.WordSMachine) (ps : List SEntry) (extra : List C) (h : checkSMachineWithFacts w.s ps extra = true)
    (hExtra : ∀ X N, WordReach.WordInterpret w.reserved w.value N → ∀ c ∈ extra, evalC X N c = true) :
    ∀ ρ M, WordReach.WordSReach w ρ M → ∀ e ∈ ps, e.Holds ρ M := by
  let s := w.s
  have hpre := word_spre_parts extra h
  have hfok := word_sfacts_ok extra h
  -- Facts at a state hold with a further key set: they read no further key.
  have hfacts : ∀ {ρ : Nat → Nat} {M : Nat → Nat → Nat} {g : Nat}, skFresh s g = true → (∀ l ∈ s.facts, l.Holds ρ M) → ∀ w, ∀ l ∈ s.facts, l.Holds (upd ρ g w) M := by
    intro ρ M g hf hfa w
    exact facts_frame s hfok [g] [] (fun l hl => by simp [avoids, (skFresh_parts hf).2.2.2.2.2.2 l hl]) (fun _ _ => by simp [avoidsMaps])
      (fun i _ hig' => by simp only [upd]; rw [if_neg (by simpa using hig')]) (fun _ _ _ => rfl) hfa
  have hpfacts : ∀ {ρ : Nat → Nat} {M : Nat → Nat → Nat} {g : Nat}, skFresh s g = true → s.PFacts ρ M → ∀ w, s.PFacts (upd ρ g w) M := by
    intro ρ M g hf hpf w
    exact pfacts_frame s hfok [g] [] (fun f hfm => by simp [avoids, skFresh_pfacts hf f hfm]) (fun _ _ => by simp [avoidsMaps])
      (fun i _ hig' => by simp only [upd]; rw [if_neg (by simpa using hig')]) (fun _ _ _ => rfl) hpf
  have hpreu : ∀ {ρ : Nat → Nat} {M : Nat → Nat → Nat} {g : Nat}, occC g s.f.m.pre = false → evalC ρ M s.f.m.pre = true → ∀ w, evalC (upd ρ g w) M s.f.m.pre = true := by
    intro ρ M g hpg h0 w
    rw [congrC _ ρ M s.f.m.pre (fun i hi => by have hig' : i ≠ g := (fun h' => by rw [h', hpg] at hi; cases hi); simp only [upd, if_neg hig'])]; exact h0
  intro ρ M hr
  induction hr with
  | start ρ base hM h0 hfa hpf =>
    let M := WordReach.overlay w.reserved w.value base
    intro e he
    -- Each further key set in turn, from a start state that meets the precondition and the facts.
    suffices hs : ∀ gs : List Nat, (∀ g ∈ gs, g ∈ e.keys2) → ∀ ρ', evalC ρ' M s.f.m.pre = true → (∀ l ∈ s.facts, l.Holds ρ' M) →
        s.PFacts ρ' M → holdsOver e.law M gs (applyS s.f.m.init ρ' M) from hs e.keys2 (fun g hg => hg) ρ h0 hfa hpf
    intro gs
    induction gs with
    | nil => intro _ ρ' hp hf hq; exact word_sstart_case s ps extra h hExtra ρ' M (WordReach.overlay_interpret _ _ _) (WordReach.overlay_start w base hM) hp hf hq e he
    | cons g gs ih =>
      intro hsub ρ' hp hf hq w
      obtain ⟨hfr, hc, hpg, hig, _, _⟩ := word_skey2_parts extra h he (hsub g List.mem_cons_self)
      have hI := (fresh_parts hfr hc ρ' M (fun _ => 0) (fun _ _ => 0) 0).2.2
      rw [← applyS_upd hI (by simpa [List.all_eq_true] using hig)]
      exact ih (fun g' hg' => hsub g' (List.mem_cons_of_mem _ hg')) (upd ρ' g w) (hpreu hpg hp w) (hfacts hfr hf w) (hpfacts hfr hq w)
  | step ρ M ι κ hr ha ih =>
    intro e he
    suffices hs : ∀ gs : List Nat, (∀ g ∈ gs, g ∈ e.keys2) → ∀ ρ', evalC ρ' M s.f.m.pre = true → (∀ l ∈ s.facts, l.Holds ρ' M) →
        s.PFacts ρ' M → (∀ e' ∈ ps, e'.Holds ρ' M) → evalC (sView s ρ' M ι κ).1 (sView s ρ' M ι κ).2 s.f.m.assume = true →
        holdsOver e.law (sNext s ρ' M ι κ).2 gs (sNext s ρ' M ι κ).1 from
      hs e.keys2 (fun g hg => hg) ρ (pre_sreach s hpre.1 hpre.2 (WordReach.word_sreach_sreach w hr)) (facts_sreach s hfok (WordReach.word_sreach_sreach w hr)) (pfacts_sreach s hfok (WordReach.word_sreach_sreach w hr)) ih ha
    intro gs
    induction gs with
    | nil => intro _ ρ' hp hf hq hi ha'; exact word_sstep_case s ps extra h hExtra ρ' M ι κ (WordReach.carried_interpret w (WordReach.word_sreach_interpret w hr)) hp hf hq hi ha' e he
    | cons g gs ihg =>
      intro hsub ρ' hp hf hq hi ha' w
      obtain ⟨hfr, hc, hpg, _, hall, _⟩ := word_skey2_parts extra h he (hsub g List.mem_cons_self)
      obtain ⟨hNext, hView, _⟩ := fresh_parts hfr hc ρ' M ι κ w
      have := ihg (fun g' hg' => hsub g' (List.mem_cons_of_mem _ hg')) (upd ρ' g w) (hpreu hpg hp w) (hfacts hfr hf w) (hpfacts hfr hq w)
        (fun e' he' => sentry_upd (hall e' he') w (hi e' he'))
        (by
          rw [hView]; dsimp only
          rw [congrC _ (sView s ρ' M ι κ).1 _ _ (fun i hi => by
            have hig' : i ≠ g := fun h' => by rw [h', (skFresh_parts hfr).2.2.1] at hi; cases hi
            simpa only [s, upd, if_neg hig'])]
          exact ha')
      rw [hNext] at this; exact this


/-- Every original k-step guard, plus disjointness of reserved IDs from frame map targets. -/
def checkSKStepWithFacts (w : WordReach.WordSMachine) (ps : List SEntry) (sl : SKStep) (extra : List C) : Bool :=
  let s := w.s
  sl.k.whens.length == sl.k.ren.length && sl.mren.length == sl.k.ren.length && sl.k.ren.head? == some [] && sl.mren.head? == some []
    && distinct (tgts sl.k.ren) && distinct (tgts sl.mren)
    && sl.k.ren.all (fun r => r.all fun p => s.extVars.contains p.1)
    && sl.k.ren.tail.all (fun r => s.extVars.all fun i => r.any (·.1 == i))
    && sl.mren.all (fun r => r.all fun p => s.carried.contains p.1)
    && sl.mren.tail.all (fun r => s.carried.all fun mp => r.any (·.1 == mp))
    && sl.k.prime.all (fun q => !s.extVars.contains q.1 && !(szone s sl).contains q.1)
    && sl.k.primeMaps.all (fun q => !s.carried.contains q.1 && !(tgts sl.mren).contains q.1)
    && avoids (szone s sl) s.f.m.pre
    && sl.k.whens.all (fun w => (sFrameHyps s (sLaws ps sl.pinsts) (sInsts ps sl.k.insts sl.pinsts) [] w).all (fun c => avoids (szone s sl) c)
      && (sFrameHyps s (sLaws ps sl.pinsts) (sInsts ps sl.k.insts sl.pinsts) sl.qinsts w).all (fun c => avoidsMaps (tgts sl.mren) c))
    && s.qflags.all (fun q => avoids (szone s sl) q.2.2)
    && sTermsOk s (szone s sl) && sMapsOk s (tgts sl.mren)
    && checkInWithFacts (sKGoal s ps sl) extra ⟨sl.k.proof.1, sl.used, sl.k.proof.2⟩
    && distinct (tgts sl.k.ren ++ tgts sl.names)
    && sl.names.all (fun n => n.all fun p => !s.extVars.contains p.1 && !(szone s sl).contains p.1)
    && avoids (tgts sl.names) sl.k.then_
    && (tgts sl.mren).all (fun mp => !w.reserved.contains mp)

/-- The same k-step conclusion, restricted to concrete-word reachable states. -/
def WordSKStepHolds (w : WordReach.WordSMachine) (sl : SKStep) : Prop :=
  ∀ ρ M, WordReach.WordSReach w ρ M → ∀ q₁ qs, qs.length + 1 = sl.k.whens.length → SAllowed w.s sl.k.whens ρ M (q₁ :: qs) →
    evalC (primed sl.k.prime (sEnd w.s ρ M (q₁ :: qs)).1 (renEnv sl.k.ren (sExts w.s ρ M (q₁ :: qs)) (withExt w.s ρ (sReq w.s ρ M q₁.1 q₁.2))))
      (primedMaps sl.k.primeMaps (sEnd w.s ρ M (q₁ :: qs)).2 (renMaps sl.mren ((q₁ :: qs).map (·.2)) (withCarried w.s M q₁.2))) sl.k.then_ = true

theorem word_skrun_sound (machine : WordReach.WordSMachine) (ps : List SEntry) (extra : List C) (hl : checkSMachineWithFacts machine.s ps extra = true) (Z MZ : List Nat) (laws : List MLaw) (insts : List (Nat × E)) (qinsts : List (Nat × List E))
    (hlY : ∀ ρ M ι κ, WordReach.WordSReach machine ρ M → ∀ l ∈ laws, l.Holds (withExt machine.s ρ (sReq machine.s ρ M ι κ)) (withCarried machine.s M κ))
    (W : Nat → Nat) (M0 : Nat → Nat → Nat)
    (hfz : ∀ v ∈ flagVars machine.s.f.flags, v ∈ Z) (hterms : sTermsOk machine.s Z = true) (hmaps : sMapsOk machine.s MZ = true)
    (hqb : ∀ q ∈ machine.s.qflags, avoids Z q.2.2 = true) :
    ∀ (ws : List C) (rs mrs ns : List (List (Nat × Nat))) (qs : List SRequest) (σ : List (Nat × E)) (rd : Nat → E → E)
      (ρ : Nat → Nat) (M : Nat → Nat → Nat),
      ws.length = rs.length → ws.length = mrs.length → ws.length = qs.length →
      (∀ whenC ∈ ws, (∀ c ∈ sFrameHyps machine.s laws insts [] whenC, avoids Z c = true) ∧ ∀ c ∈ sFrameHyps machine.s laws insts qinsts whenC, avoidsMaps MZ c = true) →
      (∀ r ∈ rs, ∀ p ∈ r, p.1 ∈ machine.s.extVars) →
      (∀ r ∈ rs.tail, ∀ i ∈ machine.s.extVars, ∃ p ∈ r, p.1 = i) →
      (∀ r ∈ mrs, ∀ p ∈ r, p.1 ∈ machine.s.carried) →
      (∀ r ∈ mrs.tail, ∀ mp ∈ machine.s.carried, ∃ p ∈ r, p.1 = mp) →
      RenOK W rs.tail (sExts machine.s ρ M qs).tail → MRenOK M0 mrs.tail (qs.map (·.2)).tail →
      (∀ n ∈ ns, ∀ p ∈ n, p.1 ∉ machine.s.extVars ∧ p.1 ∉ Z) → RenOK W ns (sStates machine.s ρ M qs) →
      WordReach.WordSReach machine ρ M → SDenotes machine.s Z MZ W M0 σ rd ρ M → SHeadL machine.s Z MZ W M0 σ rd ρ M rs mrs qs → SAllowed machine.s ws ρ M qs →
      (∀ c ∈ (sRun machine.s laws insts qinsts ws rs mrs ns σ rd).1, evalC W M0 c = true)
        ∧ SDenotes machine.s Z MZ W M0 (sRun machine.s laws insts qinsts ws rs mrs ns σ rd).2.1 (sRun machine.s laws insts qinsts ws rs mrs ns σ rd).2.2
            (sEnd machine.s ρ M qs).1 (sEnd machine.s ρ M qs).2
  | [], rs, mrs, ns, qs, σ, rd, ρ, M, hl1, hl2, hl3, _, _, _, _, _, _, _, _, _, _, hD, _, _ => by
    cases rs with
    | cons _ _ => simp at hl1
    | nil =>
      cases mrs with
      | cons _ _ => simp at hl2
      | nil =>
        cases qs with
        | cons _ _ => simp at hl3
        | nil => exact ⟨fun c hc => by simp [sRun] at hc, hD⟩
  | whenC :: ws, rs, mrs, ns, qs, σ, rd, ρ, M, hl1, hl2, hl3, hav, hkeys, hcov, hmkeys, hmcov, hren, hmren, hnsrc, hnok, hr, hD, hH, hK => by
    rcases rs with _ | ⟨r, rs⟩
    · simp at hl1
    rcases mrs with _ | ⟨mr, mrs⟩
    · simp at hl2
    rcases qs with _ | ⟨q, qs⟩
    · simp at hl3
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl1 hl2 hl3
    simp only [List.tail_cons] at hcov hmcov
    have hren1 : RenOK W rs (sExts machine.s (sNext machine.s ρ M q.1 q.2).1 (sNext machine.s ρ M q.1 q.2).2 qs) := hren
    have hmren1 : MRenOK M0 mrs (qs.map (·.2)) := hmren
    obtain ⟨hA, hW, hK'⟩ := hK
    have hH1 : SHead machine.s Z MZ W M0 σ rd ρ M r mr q.1 q.2 := hH
    obtain ⟨hfav, hstp, hwr, hev⟩ := sTermsOk_parts hterms
    obtain ⟨hstm, hwrm, hevm⟩ := sMapsOk_parts hmaps
    have hD' := sstep_denotes machine.s Z MZ W M0 (word_sOk_of extra hl) hfz hfav r mr q.1 q.2 hD hH1 (hkeys r List.mem_cons_self) hstp
      (fun machine hw => (hwr machine hw).1) hev hstm hwrm hevm
    have hr' : WordReach.WordSReach machine (sNext machine.s ρ M q.1 q.2).1 (sNext machine.s ρ M q.1 q.2).2 := WordReach.WordSReach.step ρ M q.1 q.2 hr hA
    -- Each fresh variable names the next state value of its source variable.
    have hnames : ∀ p ∈ ns.headD [], W p.2 = (sNext machine.s ρ M q.1 q.2).1 p.1 := by
      cases ns with
      | nil => intro p hp; simp at hp
      | cons n ns' => exact hnok.1
    have hnsrc1 : ∀ p ∈ ns.headD [], p.1 ∉ machine.s.extVars ∧ p.1 ∉ Z := by
      cases ns with
      | nil => intro p hp; simp at hp
      | cons n ns' => exact hnsrc n List.mem_cons_self
    have hD'' : SDenotes machine.s Z MZ W M0 (frameSub (ns.headD []) (stepSub machine.s.f (frameSub r σ) (frameRd mr rd))) (stepRdS machine.s (frameSub r σ) (frameRd mr rd))
        (sNext machine.s ρ M q.1 q.2).1 (sNext machine.s ρ M q.1 q.2).2 := by
      refine ⟨fun v hve hvz => ?_, hD'.2⟩
      by_cases hin : ∃ p ∈ ns.headD [], p.1 = v
      · exact applyS_frame_in hin hnames
      · rw [applyS_frame_out (fun p hp he => hin ⟨p, hp, he⟩)]; exact hD'.1 v hve hvz
    -- The next frame agrees with the successor state and request.
    have hH' : SHeadL machine.s Z MZ W M0 (frameSub (ns.headD []) (stepSub machine.s.f (frameSub r σ) (frameRd mr rd))) (stepRdS machine.s (frameSub r σ) (frameRd mr rd))
        (sNext machine.s ρ M q.1 q.2).1 (sNext machine.s ρ M q.1 q.2).2 rs mrs qs := by
      rcases rs with _ | ⟨r', rs'⟩
      · exact trivial
      rcases mrs with _ | ⟨mr', mrs'⟩
      · exact trivial
      rcases qs with _ | ⟨q', qs'⟩
      · exact trivial
      have hr1 : ∀ p ∈ r', W p.2 = sReq machine.s (sNext machine.s ρ M q.1 q.2).1 (sNext machine.s ρ M q.1 q.2).2 q'.1 q'.2 p.1 := hren1.1
      have hm1 : ∀ p ∈ mr', M0 p.2 = q'.2 p.1 := hmren1.1
      refine ⟨fun v hvz => ?_, fun mp k hmz => ?_⟩
      · by_cases hve : v ∈ machine.s.extVars
        · rw [applyS_frame_in (hcov r' List.mem_cons_self v hve) hr1]
          simp only [withExt]; rw [if_pos (List.contains_iff_mem.mpr hve)]
        · rw [applyS_frame_out (fun p hp he => hve (by rw [← he]; exact hkeys r' (List.mem_cons_of_mem _ List.mem_cons_self) p hp)),
            hD''.1 v hve hvz]
          simp only [withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hve)]
      · by_cases hmc : mp ∈ machine.s.carried
        · cases hlk : lookup (fun p : Nat × Nat => p.1 == mp) mr' with
          | none =>
            obtain ⟨p, hp, hp1⟩ := hmcov mr' List.mem_cons_self mp hmc
            have := lookup_none_all hlk p hp
            simp [hp1] at this
          | some p0 =>
            have hp0 := lookup_some hlk
            simp only [beq_iff_eq] at hp0
            simp only [frameRd, hlk, evalE]
            rw [hm1 p0 hp0.1, hp0.2]; simp only [withCarried]; rw [if_pos (List.contains_iff_mem.mpr hmc)]
        · have hlk : lookup (fun p : Nat × Nat => p.1 == mp) mr' = none := lookup_none (fun p hp => by
            simp only [beq_eq_false_iff_ne]; intro he
            exact hmc (by rw [← he]; exact hmkeys mr' (List.mem_cons_of_mem _ List.mem_cons_self) p hp))
          simp only [frameRd, hlk]
          rw [hD'.2 mp k hmc hmz]; simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmc)]
    have hren' : RenOK W rs.tail (sExts machine.s (sNext machine.s ρ M q.1 q.2).1 (sNext machine.s ρ M q.1 q.2).2 qs).tail := by
      rcases rs with _ | ⟨r', rs'⟩
      · exact trivial
      rcases qs with _ | ⟨q', qs'⟩
      · cases rs' <;> exact trivial
      exact hren1.2
    have hmren' : MRenOK M0 mrs.tail (qs.map (·.2)).tail := by
      rcases mrs with _ | ⟨mr', mrs'⟩
      · exact trivial
      rcases qs with _ | ⟨q', qs'⟩
      · cases mrs' <;> exact trivial
      exact hmren1.2
    have hnsrc' : ∀ n ∈ ns.tail, ∀ p ∈ n, p.1 ∉ machine.s.extVars ∧ p.1 ∉ Z := fun n hn => hnsrc n (List.mem_of_mem_tail hn)
    have hnok' : RenOK W ns.tail (sStates machine.s (sNext machine.s ρ M q.1 q.2).1 (sNext machine.s ρ M q.1 q.2).2 qs) := by
      cases ns with
      | nil => exact trivial
      | cons n ns' => exact hnok.2
    obtain ⟨ih1, ih2⟩ := word_skrun_sound machine ps extra hl Z MZ laws insts qinsts hlY W M0 hfz hterms hmaps hqb ws rs mrs ns.tail qs _ _ _ _ hl1 hl2 hl3
      (fun machine' hw' => hav machine' (List.mem_cons_of_mem _ hw'))
      (fun r' hr'' => hkeys r' (List.mem_cons_of_mem _ hr''))
      (fun r' hr'' => hcov r' (List.mem_of_mem_tail hr''))
      (fun r' hr'' => hmkeys r' (List.mem_cons_of_mem _ hr''))
      (fun r' hr'' => hmcov r' (List.mem_of_mem_tail hr''))
      hren' hmren' hnsrc' hnok' hr' hD'' hH' hK'
    refine ⟨fun c hc => ?_, ih2⟩
    simp only [sRun, List.mem_append, List.mem_map] at hc
    rcases hc with (⟨c', hc', rfl⟩ | hc) | hc
    · exact sframe_hyps machine.s Z MZ W M0 (word_sOk_of extra hl) laws insts qinsts (hlY ρ M q.1 q.2 hr)
        hH1 (hav whenC List.mem_cons_self).1 hqb (hav whenC List.mem_cons_self).2 hA hW c' hc'
    · -- Each fresh name equals the successor value denoted by its term.
      simp only [nameHyps, List.mem_map] at hc
      obtain ⟨p, hp, rfl⟩ := hc
      simp only [evalC]
      apply decide_eq_true
      show W p.2 = evalE W M0 ((assoc (stepSub machine.s.f (frameSub r σ) (frameRd mr rd)) p.1).getD (.var p.1))
      rw [hnames p hp, evalE_assoc_getD]
      exact (hD'.1 p.1 (hnsrc1 p hp).1 (hnsrc1 p hp).2).symm
    · exact ih1 c hc

theorem word_skstep_sound (w : WordReach.WordSMachine) (ps : List SEntry) (sl : SKStep) (extra : List C)
    (hl : checkSMachineWithFacts w.s ps extra = true) (hExtra : ∀ X N, WordReach.WordInterpret w.reserved w.value N → ∀ c ∈ extra, evalC X N c = true)
    (hc : checkSKStepWithFacts w ps sl extra = true) : WordSKStepHolds w sl := by
  let s := w.s
  intro ρ M hr q₁ qs hlen hK
  simp only [checkSKStepWithFacts, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨hc, hnotarget⟩ := hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlw, hlm⟩, hhead⟩, hmhead⟩, hdist⟩, hmdist⟩, hkeys⟩, hcov⟩, hmkeys⟩, hmcov⟩, hpr⟩, hpm⟩, hpre⟩, hws⟩, hqb⟩, hterms⟩, hmaps⟩, hgoal⟩, hnd⟩, hnsrc⟩, hnthen⟩ := hc
  obtain ⟨hpreS, hrp⟩ := word_spre_parts extra hl
  have hflags : ∀ v ∈ flagVars s.f.flags, v ∈ szone s sl := fun v hv => List.mem_append_left _ (List.mem_append_right _ hv)
  obtain ⟨rs, hrs⟩ : ∃ rs, sl.k.ren = [] :: rs := by
    cases h : sl.k.ren with
    | nil => rw [h] at hhead; simp at hhead
    | cons r rs => rw [h] at hhead; simp only [List.head?_cons, Option.some.injEq] at hhead; exact ⟨rs, by rw [hhead]⟩
  obtain ⟨mrs, hmrs⟩ : ∃ mrs, sl.mren = [] :: mrs := by
    cases h : sl.mren with
    | nil => rw [h] at hmhead; simp at hmhead
    | cons r rs => rw [h] at hmhead; simp only [List.head?_cons, Option.some.injEq] at hmhead; exact ⟨rs, by rw [hmhead]⟩
  -- The goal's environment: each later request at its fresh variables, and each step's state at its names.
  let W0 := renEnv sl.k.ren (sExts s ρ M (q₁ :: qs)) (withExt s ρ (sReq s ρ M q₁.1 q₁.2))
  let W := renEnv sl.names (sStates s ρ M (q₁ :: qs)) W0
  obtain ⟨_, hndn, hndis⟩ := distinct_append hnd
  have hWn : ∀ v, v ∉ tgts sl.names → W v = W0 v := fun v hv => renEnv_other _ _ _ v hv
  let M0 := renMaps sl.mren ((q₁ :: qs).map (·.2)) (withCarried s M q₁.2)
  have hWo : ∀ v, v ∉ szone s sl → W v = withExt s ρ (sReq s ρ M q₁.1 q₁.2) v := fun v hv => by
    rw [hWn v (fun h => hv (List.mem_append_right _ h))]
    exact renEnv_other _ _ _ v (fun h => hv (List.mem_append_left _ (List.mem_append_left _ h)))
  have hMo : ∀ mp, mp ∉ tgts sl.mren → M0 mp = withCarried s M q₁.2 mp := fun mp hmp => renMaps_other _ _ _ mp hmp
  have hD0 : SDenotes s (szone s sl) (tgts sl.mren) W M0 [] getRd ρ M := by
    refine ⟨fun v hve hvz => ?_, fun mp k hmc hmz => ?_⟩
    · rw [applyS_nil', hWo v hvz]; simp only [withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hve)]
    · simp only [getRd, evalE]; rw [hMo mp hmz]; simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmc)]
  have hH0 : SHeadL s (szone s sl) (tgts sl.mren) W M0 [] getRd ρ M sl.k.ren sl.mren (q₁ :: qs) := by
    rw [hrs, hmrs]
    show SHead s (szone s sl) (tgts ([] :: mrs)) W M0 [] getRd ρ M [] [] q₁.1 q₁.2
    refine ⟨fun v hvz => ?_, fun mp k hmz => ?_⟩
    · simp only [frameSub, List.map_nil, List.append_nil, applyS_nil']; exact hWo v hvz
    · simp only [frameRd, lookup, getRd, evalE]; rw [hMo mp (by rw [hmrs]; exact hmz)]
  have hren0 : RenOK W sl.k.ren.tail (sExts s ρ M (q₁ :: qs)).tail := by
    have h : RenOK W sl.k.ren (sExts s ρ M (q₁ :: qs)) :=
      renOK_congr _ _ (fun v hv => hWn v (hndis v hv)) (renEnv_ok sl.k.ren _ _ hdist)
    rw [hrs] at h ⊢; exact h.2
  have hmren0 : MRenOK M0 sl.mren.tail ((q₁ :: qs).map (·.2)).tail := by
    have h : MRenOK M0 sl.mren ((q₁ :: qs).map (·.2)) := renMaps_ok sl.mren _ _ hmdist
    rw [hmrs] at h ⊢; exact h.2
  -- Every entry holds at each reachable state, so each law (and each pair's) holds in the goal's view of it.
  have hlY : ∀ ρ M ι κ, WordReach.WordSReach w ρ M → ∀ l ∈ sLaws ps sl.pinsts, l.Holds (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ) := by
    intro ρ M ι κ hr l hl'
    have hall : ∀ e ∈ ps, e.Holds (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ) := fun e he =>
      sentry_transfer (word_slaws_avoid extra hl e.law (List.mem_map_of_mem he)).1 (word_slaws_avoid extra hl e.law (List.mem_map_of_mem he)).2
        (fun i hi => by simp only [withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hi)])
        (fun mp hmp => by simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmp)])
        (concrete_smachine_sound w ps extra hl hExtra ρ M hr e he)
    rcases List.mem_append.mp hl' with hl' | hl'
    · obtain ⟨e', he', rfl⟩ := List.mem_map.mp hl'; exact SEntry.holds_law (hall e' he')
    · exact pairLaws_hold ps sl.pinsts (word_skeys_apart extra hl) hall l hl'
  obtain ⟨hh, hfin⟩ := word_skrun_sound w ps extra hl (szone s sl) (tgts sl.mren) (sLaws ps sl.pinsts) (sInsts ps sl.k.insts sl.pinsts) sl.qinsts hlY W M0 hflags hterms hmaps hqb
    sl.k.whens sl.k.ren sl.mren sl.names (q₁ :: qs) [] getRd ρ M hlw (by omega) (by simp only [List.length_cons]; omega)
    hws (fun r hr p hp => List.contains_iff_mem.mp (hkeys r hr p hp))
    (fun r hr i hi => by have := hcov r hr i hi; simpa only [List.any_eq_true, beq_iff_eq] using this)
    (fun r hr p hp => List.contains_iff_mem.mp (hmkeys r hr p hp))
    (fun r hr i hi => by have := hmcov r hr i hi; simpa only [List.any_eq_true, beq_iff_eq] using this)
    hren0 hmren0
    (fun n hn p hp => by
      have h := hnsrc n hn p hp
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at h
      exact ⟨by simpa using h.1, by simpa using h.2⟩)
    (renEnv_ok sl.names _ _ hndn) hr hD0 hH0 hK
  have hfin' : SDenotes s (szone s sl) (tgts sl.mren) W M0 (sKOut s ps sl).2.1 (sKOut s ps sl).2.2
      (sEnd s ρ M (q₁ :: qs)).1 (sEnd s ρ M (q₁ :: qs)).2 := hfin
  apply Decidable.byContradiction; intro hn
  -- `then` reads none of the names, so the goal's environment reads it as the claim's does.
  have hn' : ¬ evalC (primed sl.k.prime (sEnd s ρ M (q₁ :: qs)).1 W) (primedMaps sl.k.primeMaps (sEnd s ρ M (q₁ :: qs)).2 M0) sl.k.then_ = true := by
    rw [congrC (primed sl.k.prime (sEnd s ρ M (q₁ :: qs)).1 W) (primed sl.k.prime (sEnd s ρ M (q₁ :: qs)).1 W0) _ sl.k.then_ (fun i hi => by
      simp only [primed]; split
      · rfl
      · exact hWn i (avoids_occ hnthen hi))]
    exact hn
  have hworld : WordReach.WordInterpret w.reserved w.value M0 := by
    intro mp hm key
    have htarget : mp ∉ tgts sl.mren := by
      intro ht
      have hn := hnotarget mp ht
      have hyes : w.reserved.contains mp = true := List.contains_iff_mem.mpr hm
      rw [hyes] at hn
      cases hn
    rw [hMo mp htarget]
    exact WordReach.carried_interpret w (WordReach.word_sreach_interpret w hr) mp hm key
  apply sound_in_with (sKGoal s ps sl) extra ⟨sl.k.proof.1, sl.used, sl.k.proof.2⟩ hgoal W M0 (hExtra W M0 hworld)
  intro c hc
  simp only [sKGoal, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ((rfl | hc) | hc) | rfl
  · -- The precondition: at the first state (it reads no map, no request and no fresh variable).
    rw [noReadsC W M0 M s.f.m.pre hrp, congrC W ρ M s.f.m.pre (fun j hj => ?_)]
    · exact pre_sreach s hpreS hrp (WordReach.word_sreach_sreach w hr)
    · rw [hWo j (avoids_occ hpre hj)]; simp only [withExt]
      rw [if_neg (fun h' => avoids_occ hpreS hj (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.contains_iff_mem.mp h')))))]
  · -- The facts, at the first frame: it agrees with the first state away from the zone and the request.
    exact facthyps_true s sl.finsts sl.pfinsts W M0 (fun f hf => (pfactsOk_parts (word_sfacts_ok extra hl) f hf).2.2)
      (facts_frame s (word_sfacts_ok extra hl) (szone s sl) (tgts sl.mren) (sTermsOk_facts hterms) (sMapsOk_facts hmaps)
        (fun i hie hiz => by rw [hWo i hiz]; simp only [withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hie)])
        (fun mp hmc hmz => by rw [hMo mp hmz]; simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmc)])
        (facts_sreach s (word_sfacts_ok extra hl) (WordReach.word_sreach_sreach w hr)))
      (pfacts_frame s (word_sfacts_ok extra hl) (szone s sl) (tgts sl.mren) (sTermsOk_pfacts hterms) (sMapsOk_pfacts hmaps)
        (fun i hie hiz => by rw [hWo i hiz]; simp only [withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hie)])
        (fun mp hmc hmz => by rw [hMo mp hmz]; simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmc)])
        (pfacts_sreach s (word_sfacts_ok extra hl) (WordReach.word_sreach_sreach w hr))) c hc
  · exact hh c hc
  · -- `then`, read across the run, is what SKStepHolds reads.
    have hrdE : ∀ mp k, evalE W M0 (kEndRd sl.k (sKOut s ps sl).2.2 mp k)
        = primedMaps sl.k.primeMaps (sEnd s ρ M (q₁ :: qs)).2 M0 mp (evalE W M0 k) := by
      intro mp k
      simp only [kEndRd, primedMaps]
      cases hq : lookup (fun q => q.2 == mp) sl.k.primeMaps with
      | none => simp [evalE]
      | some q =>
        have hq1 := hpm q (lookup_some hq).1
        simp only [Bool.not_eq_true'] at hq1
        exact hfin'.2 q.1 k (by simpa using hq1.1) (by simpa using hq1.2)
    have henv : applyS (kEndSub sl.k (sKOut s ps sl).2.1 (sKOut s ps sl).2.2) W M0
        = primed sl.k.prime (sEnd s ρ M (q₁ :: qs)).1 W := by
      funext i
      rw [kEndSub, applyS_primes]
      simp only [primed]
      cases hq : lookup (fun q => q.2 == i) sl.k.prime with
      | none => rfl
      | some q =>
        have hq1 := hpr q (lookup_some hq).1
        simp only [Bool.not_eq_true'] at hq1
        have hqi : q.1 ∉ s.extVars := by simpa using hq1.1
        have hqz : q.1 ∉ szone s sl := by simpa using hq1.2
        show evalE W M0 (substRE (sKOut s ps sl).2.1 (sKOut s ps sl).2.2 (.var q.1)) = (sEnd s ρ M (q₁ :: qs)).1 q.1
        rw [substR_var]; exact hfin'.1 q.1 hqi hqz
    simp only [evalC, substR_evalC _ _ W M0 _ hrdE, henv]
    simpa using hn'

end Kern.WordSMachine

#print axioms Kern.WordSMachine.concrete_smachine_sound
#print axioms Kern.WordSMachine.word_skstep_sound

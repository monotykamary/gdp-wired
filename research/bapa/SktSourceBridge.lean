import SktSourceInvariant
import SktSourceTarget
open Kern
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

 theorem skt_unowned_body (ρ M) (h : SktSourceInv ρ M) (k n) :
    (ρ 41 ≤ n ∨ M 1 (cpair k n) = 0) ↔ M 1 (cpair k n) ≠ 1 := by
  have hb := h.1 (cpair k n)
  by_cases hn : ρ 41 ≤ n
  · have hz := h.2.2 k n hn
    simp [hn, hz]
  · simp only [hn, false_or]
    omega

 theorem skt_q_eq (ρ M ι) (h : SktSourceInv ρ M) :
    decideQ skt_source (withInputs [0,1,2,3,4] ρ ι) M =
    decideQ skt_target (withInputs [0,1,2,3,4] ρ ι) (sktProject M) := by
  classical
  funext v
  by_cases hv : 31 = v
  · subst v
    have hq : (∀ k : Nat → Nat, ρ 41 ≤ k 39 ∨ M 1 (cpair (ι 2) (k 39)) = 0) ↔
        (∀ k : Nat → Nat, M 1 (cpair (ι 2) (k 39)) ≠ 1) :=
      forall_congr' (fun k => skt_unowned_body ρ M h (ι 2) (k 39))
    simpa [decideQ, skt_source, skt_target, lookup, holdsC, evalE, atKeys,
      withInputs, sktProject, Nat.lt_one_iff] using
      congrArg (fun p : Prop => if p then (1 : Nat) else 0) (propext hq)
  · simp [decideQ, skt_source, skt_target, lookup, hv]

 theorem skt_plain_flags (D M) (ho : ∀ k, M 1 k ≤ 1) (hm : ∀ k, M 2 k ≤ 1) :
    decideFlags skt_source.f.flags D M = decideFlags skt_target.f.flags D (sktProject M) := by
  funext v
  by_cases h32 : 32 = v
  · subst v; rfl
  by_cases h33 : 33 = v
  · subst v; rfl
  by_cases h34 : 34 = v
  · subst v; rfl
  by_cases h35 : 35 = v
  · subst v; rfl
  by_cases h36 : 36 = v
  · subst v
    have hb : M 2 (cpair (D 1) (cpair (D 2) (D 3))) = 0 ∨ M 2 (cpair (D 1) (cpair (D 2) (D 3))) = 1 := by
      have hh := hm (cpair (D 1) (cpair (D 2) (D 3))); omega
    rcases hb with hb | hb <;>
      by_cases hop : D 0 = 3 <;> by_cases hstarted : D 5 = 1 <;>
      simp [decideFlags, skt_source, skt_target, flagSub, applyS, assoc,
        lookup, evalC, evalE, sktProject, hb, hop, hstarted]
  by_cases h37 : 37 = v
  · subst v
    have hb : M 1 (cpair (D 2) (D 1)) = 0 ∨ M 1 (cpair (D 2) (D 1)) = 1 := by
      have hh := ho (cpair (D 2) (D 1)); omega
    rcases hb with hb | hb <;>
      by_cases hop : D 0 = 4 <;> by_cases hstarted : D 5 = 1 <;>
      simp [decideFlags, skt_source, skt_target, flagSub, applyS, assoc,
        lookup, evalC, evalE, sktProject, hb, hop, hstarted]
  simp [decideFlags, skt_source, skt_target, flagSub, applyS, assoc,
    lookup, h32, h33, h34, h35, h36, h37]

 theorem skt_view_eq (ρ M ι κ) (h : SktSourceInv ρ M) :
    (sView skt_source ρ M ι κ).1 = (sView skt_target ρ (sktProject M) ι κ).1 := by
  change decideFlags skt_source.f.flags (decideQ skt_source (withInputs [0,1,2,3,4] ρ ι) M) M =
    decideFlags skt_target.f.flags (decideQ skt_target (withInputs [0,1,2,3,4] ρ ι) (sktProject M)) (sktProject M)
  rw [skt_q_eq ρ M ι h]
  exact skt_plain_flags _ M h.1 h.2.1

 theorem skt_tuple_components (k a b c : Nat) :
    ((cun k).1 = a ∧ (cun (cun k).2).1 = b ∧ (cun (cun k).2).2 = c) ↔ k = cpair a (cpair b c) := by
  constructor
  · rintro ⟨ha, hb, hc⟩
    calc
      k = cpair (cun k).1 (cun k).2 := (cpair_cun_eq k).symm
      _ = cpair a (cpair (cun (cun k).2).1 (cun (cun k).2).2) := by rw [ha, cpair_cun_eq]
      _ = cpair a (cpair b c) := by rw [hb, hc]
  · intro h; subst k; simp

 theorem skt_tuple_bool (k a b c : Nat) :
    (decide ((cun k).1 = a) && (decide ((cun (cun k).2).1 = b) && decide ((cun (cun k).2).2 = c))) =
      decide (k = cpair a (cpair b c)) := by
  rw [← Bool.decide_and, ← Bool.decide_and]
  exact decide_eq_decide.mpr (skt_tuple_components k a b c)

 theorem skt_pair_eq (a b c d : Nat) : (cpair a b = cpair c d) ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun x => (cun x).1) h,
      by simpa using congrArg (fun x => (cun x).2) h⟩
  · rintro ⟨rfl, rfl⟩; rfl

 theorem skt_maps_step (D M) (h : SktSourceInv D M) :
    sktProject (everyMaps skt_source D M) = everyMaps skt_target D (sktProject M) := by
  funext mp k
  by_cases h0 : mp = 0
  · subst mp; rfl
  by_cases h1 : mp = 1
  · subst mp
    have hb : M 1 (cpair (D 2) (D 1)) = 0 ∨ M 1 (cpair (D 2) (D 1)) = 1 := by
      have hh := h.1 (cpair (D 2) (D 1)); omega
    rcases hb with hb | hb <;>
      by_cases ha : D 33 = 1 <;> by_cases hc : D 36 = 1 <;> by_cases hr : D 35 = 1 <;>
      simp [sktProject, everyMaps, writeMaps, skt_source, skt_target, lookup, evalC, evalE, hb, ha, hc, hr]
  by_cases h2 : mp = 2
  · subst mp
    have hb : M 2 k = 0 ∨ M 2 k = 1 := by have hh := h.2.1 k; omega
    rcases hb with hb | hb <;>
      by_cases hs : D 35 = 1 <;> by_cases hr : D 36 = 1 <;>
      by_cases hsend : k = cpair (D 4) (cpair (D 2) (D 3)) <;>
      by_cases hrecv : k = cpair (D 1) (cpair (D 2) (D 3)) <;>
      simp_all [sktProject, everyMaps, skt_source, skt_target, lookup, evalC, evalE, upd,
        pickP, skt_tuple_bool, skt_pair_eq]
  by_cases h3 : mp = 3
  · subst mp
    simp [sktProject, everyMaps, writeMaps, skt_target, lookup]
  · simp [sktProject, everyMaps, writeMaps, skt_source, skt_target, lookup,
      h0, h1, h2, h3, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3]

 theorem skt_step_eq (ρ M ι κ) (h : SktSourceInv ρ M) :
    (sNext skt_source ρ M ι κ).1 = (sNext skt_target ρ (sktProject M) ι κ).1 ∧
    sktProject (sNext skt_source ρ M ι κ).2 = (sNext skt_target ρ (sktProject M) ι κ).2 := by
  have hv := skt_view_eq ρ M ι κ h
  constructor
  · change applyS skt_source.f.m.step (sView skt_source ρ M ι κ).1 M =
      applyS skt_target.f.m.step (sView skt_target ρ (sktProject M) ι κ).1 (sktProject M)
    rw [hv]
    funext v
    by_cases he : 5 = v
    · subst v; rfl
    · simp [applyS, assoc, lookup, skt_source, skt_target, he]
  · change sktProject (everyMaps skt_source (sView skt_source ρ M ι κ).1 M) =
      everyMaps skt_target (sView skt_target ρ (sktProject M) ι κ).1 (sktProject M)
    rw [← hv]
    apply skt_maps_step
    simpa only [SktSourceInv, skt_source_view_nodes] using h

 theorem skt_admission (ρ M ι κ) (h : SktSourceInv ρ M)
    (ha : evalC (sView skt_source ρ M ι κ).1 (sView skt_source ρ M ι κ).2 skt_source.f.m.assume = true) :
    evalC (sView skt_target ρ (sktProject M) ι κ).1
      (sView skt_target ρ (sktProject M) ι κ).2 skt_target.f.m.assume = true := by
  rw [← skt_view_eq ρ M ι κ h]
  have hh := (evalC_iff _ _ skt_source.f.m.assume).mp ha
  apply (evalC_iff _ _ skt_target.f.m.assume).mpr
  have hop : (sView skt_source ρ M ι κ).1 0 < 5 := hh.1
  simpa only [skt_target, holdsC, evalE, Nat.le_refl, and_true] using hop

 theorem skt_init_state (ρ M) :
    applyS skt_source.f.m.init ρ M = applyS skt_target.f.m.init ρ (sktProject M) := by
  funext v
  by_cases he : 5 = v <;> simp [applyS, assoc, lookup, skt_source, skt_target, evalE, he]

 theorem skt_init_maps (M) (hM : StartMaps skt_source.f.m M) : StartMaps skt_target.f.m (sktProject M) := by
  intro p hp k
  simp [skt_target] at hp
  rcases hp with rfl | rfl | rfl
  · simpa [sktProject] using hM (0,0) (by simp [skt_source]) k
  · simpa [sktProject] using hM (1,0) (by simp [skt_source]) k
  · simpa [sktProject] using hM (2,0) (by simp [skt_source]) k

 theorem skt_source_init (ρ M) (hM : StartMaps skt_source.f.m M) :
    SReach skt_target (applyS skt_source.f.m.init ρ M) (sktProject M) := by
  rw [skt_init_state]
  exact SReach.start ρ (sktProject M) (skt_init_maps M hM) (by rfl)
    (by simp [skt_target]) (by simp [SMachine.PFacts, skt_target])

 theorem skt_source_reach : ∀ {ρ M}, SReach skt_source ρ M → SReach skt_target ρ (sktProject M) := by
  intro ρ M hr
  induction hr with
  | start ρ M hM hp hf hpf =>
    exact skt_source_init ρ M hM
  | step ρ M ι κ hr ha ih =>
    have hi := skt_source_invariant hr
    have ht := SReach.step ρ (sktProject M) ι κ ih (skt_admission ρ M ι κ hi ha)
    rcases skt_step_eq ρ M ι κ hi with ⟨hs, hm⟩
    rw [← hs, ← hm] at ht
    exact ht

/-- Conditional projection only: no target-family safety proof is assumed to
have been checked. The unresolved safety premise is explicit in this theorem. -/
theorem skt_source_public_law_conditional
    (safe : ∀ ρ M, SReach Bapa.ShardedKvSnapshot.machine ρ M →
      holdsOver Bapa.ShardedKvSnapshot.entry2.law M Bapa.ShardedKvSnapshot.entry2.keys2 ρ)
    (ρ M) (hr : SReach skt_source ρ M) : holdsOver skt_source_law M skt_source_keys ρ := by
  have ht := skt_source_reach hr
  rw [skt_target_identity] at ht
  have hg := safe ρ (sktProject M) ht
  change ∀ b k v u a, evalC (upd (upd (upd (upd (upd ρ 9 b) 10 k) 11 v) 12 u) 8 a) M skt_source_law.holds = true
  intro b k v u a
  have hh := hg b k v u a
  simp [Bapa.ShardedKvSnapshot.entry2, evalC, evalE, upd, sktProject] at hh
  simp [skt_source_law, evalC, evalE, upd]
  omega

#print axioms skt_q_eq
#print axioms skt_view_eq
#print axioms skt_maps_step
#print axioms skt_step_eq
#print axioms skt_admission
#print axioms skt_init_state
#print axioms skt_init_maps
#print axioms skt_source_init
#print axioms skt_source_reach
#print axioms skt_source_public_law_conditional

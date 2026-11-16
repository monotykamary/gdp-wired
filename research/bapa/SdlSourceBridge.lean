import SdlExactTransport
import SdlTargetData
import SdlSourceDefs
open Kern
open Bapa.SimpleDecentralizedLockTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

-- The source uses a >=1 relation read and a numeric stuttering write. The
-- retained target uses equality-to-1 and Boolean-normalized writes. They agree
-- on the Message kind invariant, obtained from the complete checked family.
theorem sdl_view_eq (ρ M ι κ) (hcell : M 0 (cpair (ι 1) (ι 2)) ≤ 1) :
    sView sdl_source ρ M ι κ = sView sdl_target_data ρ M ι κ := by
  have hz : M 0 (cpair (ι 1) (ι 2)) = 0 ∨ M 0 (cpair (ι 1) (ι 2)) = 1 := by omega
  apply Prod.ext
  · funext v
    rcases hz with hz | hz <;>
      by_cases h15 : 15 = v <;> by_cases h16 : 16 = v <;> by_cases h17 : 17 = v <;>
      simp [sView, sdl_source, sdl_target_data, decideQ, withCarried, decideFlags,
        flagSub, applyS, assoc, lookup, withInputs, evalC, evalE, hz, h15, h16, h17]
  · rfl

theorem sdl_maps_step_eq (D M) (hcell : M 0 (cpair (D 1) (D 2)) ≤ 1) :
    everyMaps sdl_source D M = everyMaps sdl_target_data D M := by
  have hz : M 0 (cpair (D 1) (D 2)) = 0 ∨ M 0 (cpair (D 1) (D 2)) = 1 := by omega
  funext mp key
  by_cases hm1 : 1 = mp
  · subst mp; rfl
  · by_cases hm0 : 0 = mp
    · subst mp
      rcases hz with hz | hz <;>
        by_cases hs : D 16 = 1 <;> by_cases hr : D 17 = 1 <;>
        simp [everyMaps, writeMaps, sdl_source, sdl_target_data, lookup, evalC, evalE, hz, hs, hr]
    · simp [everyMaps, writeMaps, sdl_source, sdl_target_data, lookup, hm0, hm1]

theorem sdl_step_eq (ρ M ι κ) (hcell : M 0 (cpair (ι 1) (ι 2)) ≤ 1) :
    sNext sdl_source ρ M ι κ = sNext sdl_target_data ρ M ι κ := by
  unfold sNext
  rw [sdl_view_eq ρ M ι κ hcell]
  apply Prod.ext
  · rfl
  · apply sdl_maps_step_eq
    simpa [sView, sdl_target_data, decideQ, withCarried, decideFlags, flagSub,
      applyS, assoc, lookup, withInputs, evalC, evalE] using hcell

theorem sdl_admission (D M) : evalC D M sdl_source.f.m.assume = true →
    evalC D M sdl_target_data.f.m.assume = true := by
  intro h
  simp_all [sdl_source, sdl_target_data, evalC, evalE]

theorem sdl_reach : ∀ {ρ M}, SReach sdl_source ρ M → SReach sdl_target_data ρ M := by
  intro ρ M hr
  induction hr with
  | start ρ M hM hp hf hpf =>
    have maps : StartMaps sdl_target_data.f.m M := by
      simpa [StartMaps, sdl_source, sdl_target_data, and_comm] using hM
    exact SReach.start ρ M maps hp (by simp [sdl_target_data]) (by simp [SMachine.PFacts, sdl_target_data])
  | step ρ M ι κ hr ha ih =>
    have hcell : M 0 (cpair (ι 1) (ι 2)) ≤ 1 :=
      message_bound ρ M (by rw [sdl_target_eq]; exact ih) (ι 1) (ι 2)
    have ht : evalC (sView sdl_target_data ρ M ι κ).1
        (sView sdl_target_data ρ M ι κ).2 sdl_target_data.f.m.assume = true := by
      rw [sdl_view_eq ρ M ι κ hcell] at ha
      exact sdl_admission _ _ ha
    have next := SReach.step ρ M ι κ ih ht
    rw [← sdl_step_eq ρ M ι κ hcell] at next
    exact next

/-- Original emitted symbolic source law, for arbitrary size; no size<=64 premise. -/
theorem bapa_simple_decentralized_lock_source_law (ρ M) (hr : SReach sdl_source ρ M) :
    holdsOver sdl_source_law M sdl_source_keys ρ := by
  have ht : SReach target.s ρ M := by rw [sdl_target_eq]; exact sdl_reach hr
  change ∀ b a, evalC (upd (upd ρ 9 b) 8 a) M sdl_source_law.holds = true
  intro b a
  by_cases ha : M 1 a = 1 <;> by_cases hb : M 1 b = 1
  · have h := mutual_exclusion ρ M ht a b ha hb
    simp [sdl_source_law, evalC, evalE, upd, ha, hb, h]
  all_goals simp [sdl_source_law, evalC, evalE, upd, ha, hb]

#print axioms sdl_view_eq
#print axioms sdl_maps_step_eq
#print axioms sdl_step_eq
#print axioms sdl_admission
#print axioms sdl_reach
#print axioms bapa_simple_decentralized_lock_source_law

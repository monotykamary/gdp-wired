import SktSourceDefs
open Kern
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

/-- Only source-derived map facts needed for structural simulation. -/
def SktSourceInv (ρ : Nat → Nat) (M : Nat → Nat → Nat) : Prop :=
  (∀ k, M 1 k ≤ 1) ∧ (∀ k, M 2 k ≤ 1) ∧
  (∀ k n, ρ 41 ≤ n → M 1 (cpair k n) = 0)

/-- The source-only Owned map is hidden; every other map remains unchanged. -/
def sktProject (M : Nat → Nat → Nat) : Nat → Nat → Nat :=
  fun mp k => if mp = 3 then 0 else M mp k

@[simp] theorem sktProject_table (M k) : sktProject M 0 k = M 0 k := by simp [sktProject]
@[simp] theorem sktProject_owner (M k) : sktProject M 1 k = M 1 k := by simp [sktProject]
@[simp] theorem sktProject_message (M k) : sktProject M 2 k = M 2 k := by simp [sktProject]

 theorem skt_source_view_nodes (ρ M ι κ) : (sView skt_source ρ M ι κ).1 41 = ρ 41 := by
  simp [sView, skt_source, decideQ, withCarried, decideFlags, flagSub,
    applyS, assoc, lookup, withInputs]

 theorem skt_source_next_nodes (ρ M ι κ) : (sNext skt_source ρ M ι κ).1 41 = ρ 41 := by
  change (sView skt_source ρ M ι κ).1 41 = ρ 41
  exact skt_source_view_nodes ρ M ι κ

 theorem skt_source_maps_inv (D M) (h : SktSourceInv D M) (hn : D 1 < D 41) :
    SktSourceInv D (everyMaps skt_source D M) := by
  rcases h with ⟨ho, hm, hz⟩
  refine ⟨?_, ?_, ?_⟩
  · intro k
    by_cases hp : k = cpair (D 2) (D 1) <;>
      by_cases ha : D 33 = 1 <;> by_cases hb : D 36 = 1 <;>
      by_cases hr : D 35 = 1 <;>
      simp [everyMaps, writeMaps, skt_source, lookup, evalC, evalE, hp, ha, hb, hr, ho]
  · intro k
    dsimp [everyMaps, skt_source, lookup, evalE]
    split <;> omega
  · intro k n hbound
    have hp : cpair k n ≠ cpair (D 2) (D 1) := by
      intro heq
      have hh := congrArg (fun x => (cun x).2) heq
      simp only [cun_cpair_snd] at hh
      omega
    simp [everyMaps, writeMaps, skt_source, lookup, evalC, evalE, hp, hz k n hbound]

/-- Boolean cells and off-domain Owner zeros follow from the actual source,
not from a retained family whose step checks are still incomplete. -/
theorem skt_source_invariant : ∀ {ρ M}, SReach skt_source ρ M → SktSourceInv ρ M := by
  intro ρ M hr
  induction hr with
  | start ρ M hM hp hf hpf =>
    have ho : ∀ k, M 1 k = 0 := hM (1,0) (by simp [skt_source])
    have hm : ∀ k, M 2 k = 0 := hM (2,0) (by simp [skt_source])
    exact ⟨by simp [ho], by simp [hm], by intros; simp [ho]⟩
  | step ρ M ι κ hr ha ih =>
    let D := (sView skt_source ρ M ι κ).1
    have hnodes : D 41 = ρ 41 := skt_source_view_nodes ρ M ι κ
    have hi : SktSourceInv D M := by simpa only [SktSourceInv, hnodes] using ih
    have hn : D 1 < D 41 := by
      change evalC D M skt_source.f.m.assume = true at ha
      have hh := (evalC_iff D M skt_source.f.m.assume).mp ha
      exact hh.2.1
    have hh := skt_source_maps_inv D M hi hn
    change SktSourceInv (sNext skt_source ρ M ι κ).1 (everyMaps skt_source D M)
    simpa only [SktSourceInv, skt_source_next_nodes, hnodes] using hh

#print axioms skt_source_view_nodes
#print axioms skt_source_next_nodes
#print axioms skt_source_maps_inv
#print axioms skt_source_invariant

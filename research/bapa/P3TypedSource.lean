import P3TypedDefs
open Kern
open Bapa.CertificateBoundSubstitution
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem p3_basis_matches : p3_basis = captured_client_server_db_ae_0_machine := by rfl
theorem p3_typed_options_complete : P3Typed.machineOption.isSome && P3Typed.entryOptions.all Option.isSome = true := by decide +kernel
theorem p3_init_caches_cleared : (P3Typed.proof.zipIdx.all fun (e,i) =>
    if [0,1,2,26].contains i then e.start.2.1.isEmpty else true) = true := by decide +kernel

theorem p3_step_caches_cleared : (P3Typed.proof.all fun e => e.step.2.1.isEmpty) = true := by decide +kernel

theorem p3_four_parameters : P3Typed.baseTyping.sizes = [31,32,33,34] := by rfl
theorem p3_tree_shapes_preserved :
    P3Typed.proof.map (fun e => (Typed.treeShape e.start.2.2, Typed.treeShape e.step.2.2)) =
    captured_client_server_db_ae_0_proof.map (fun e => (Typed.treeShape e.start.2.2, Typed.treeShape e.step.2.2)) := by decide +kernel
theorem p3_all54 : Bapa.BoundErasureReplay.plainChecks P3Typed.machine P3Typed.proof = List.replicate 54 true := by decide +kernel
theorem p3_family : checkSMachine P3Typed.machine P3Typed.proof = true := by decide +kernel
theorem p3_laws : ∀ ρ M, SReach P3Typed.machine ρ M → ∀ e ∈ P3Typed.proof, e.Holds ρ M := smachine_sound _ _ p3_family

def p3_entry : SEntry := P3Typed.proof[0]'(by decide +kernel)
def p3_mutant : SEntry := Bapa.BoundErasureReplay.boundMutant p3_entry 6
theorem p3_old_bound_refused : checkIn (sStepGoal P3Typed.machine P3Typed.proof p3_mutant) p3_mutant.step = false := by decide +kernel

theorem p3_alpha_valid : QAlpha.validAll p3_source p3_renames = true := by decide +kernel
theorem p3_ghosts_valid : smghostOk p3_ghosts = true := by decide +kernel
theorem p3_view_eq (ρ M ι κ) : sView p3_ghosts.full ρ M ι κ = sView p3_target ρ M ι κ := by rfl
theorem p3_next_eq (ρ M ι κ) : sNext p3_ghosts.full ρ M ι κ = sNext p3_target ρ M ι κ := by rfl

theorem p3_source_assume_eq : p3_ghosts.full.f.m.assume = p3_source_assume := by rfl
theorem p3_target_assume_eq : p3_target.f.m.assume = p3_typed_assume := by rfl
theorem p3_strong_eq : p3_strong_body = p3_strong_literal := by rfl
theorem p3_weak_eq : p3_weak_body = p3_weak_literal := by rfl

theorem p3_admission (ρ M) : evalC ρ M p3_ghosts.full.f.m.assume = true → evalC ρ M p3_target.f.m.assume = true := by
  intro h
  rw [p3_source_assume_eq] at h
  rw [p3_target_assume_eq]
  simpa [p3_source_assume, p3_typed_assume, evalC, and_assoc] using h

theorem p3_inclusion : SourceInclusion p3_ghosts.full p3_target where
  inputs := by rfl
  carried := by rfl
  initial := by rfl
  startMaps := by intro M h; exact h
  pre := by intro ρ M h; exact h
  facts := by intro ρ M h; exact h
  pfacts := by intro ρ M h; exact h
  admission := by
    intro ρ M ι κ h
    rw [p3_view_eq] at h
    exact p3_admission _ _ h
  next := by intro ρ M ι κ _; exact p3_next_eq ρ M ι κ

def p3_weak : SEntry := {p3_entry with law := {p3_entry.law with holds := p3_weak_body}}
theorem p3_law_implication : SourceLawImplication p3_entry p3_weak := by
  apply sourceLawImplication_of_pointwise
  · rfl
  · rfl
  · intro ρ M h
    change evalC ρ M p3_weak_body = true
    change evalC ρ M p3_strong_body = true at h
    rw [p3_strong_eq] at h
    rw [p3_weak_eq]
    simpa [p3_strong_literal, p3_weak_literal, evalC, and_assoc, or_assoc] using h

theorem bapa_client_server_db_ae_source (ρ M) (hr : SReach p3_source ρ M) :
    ExHolds p3_source_body p3_source_key p3_source_exists M p3_source_keys ρ := by
  have ha : SReach p3_source_alpha ρ M :=
    (QAlpha.renameAll_equiv p3_source p3_renames p3_alpha_valid).symm.sreach_imp hr
  obtain ⟨ρg, Mg, hg, hag, hmag⟩ := smghost_reach p3_ghosts p3_ghosts_valid ha
  have h := p3_law_implication ρg Mg (p3_laws ρg Mg (p3_inclusion.sreach hg) p3_entry (by
    exact List.getElem_mem (by decide +kernel)))
  change ∀ vp vn, ∃ f : Nat → Nat, evalC (updAll (upd (upd ρ 7 vp) 6 vn) [(36,f 36)]) M p3_source_body = true
  intro vp vn
  have hplain : evalC (upd (upd ρg 7 vp) 6 vn) Mg (substC p3_sigma p3_source_body) = true := h vp vn
  exact some_of_subst_bound_apart p3_sigma p3_source_body (by decide +kernel) (by decide +kernel)
    (upd_agree (upd_agree hag 7 vp) 6 vn) hmag hplain

#print axioms p3_step_caches_cleared
#print axioms p3_init_caches_cleared
#print axioms p3_typed_options_complete
#print axioms p3_tree_shapes_preserved
#print axioms p3_all54
#print axioms p3_family
#print axioms p3_old_bound_refused
#print axioms p3_inclusion
#print axioms p3_law_implication
#print axioms bapa_client_server_db_ae_source

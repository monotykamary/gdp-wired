import P2SourceDefs
import SourceInclusion
open Kern
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000

def p2_entry : CEntry := Bapa.ToyConsensusForallTransport.proof[2]'(by decide +kernel)
def p2_weak_entry : SEntry := {p2_entry.e with law := p2_source_law, keys2 := p2_source_keys}
def p2_source_alpha : SMachine := QAlpha.renameAll p2_source p2_source_renames
def p2_source_plus : SMachine := {p2_source_alpha with carried := p2_source_alpha.carried ++ p2_fresh}

theorem p2_basis_eq : p2_basis_machine = captured_toy_consensus_forall_0_machine := by rfl
theorem p2_alpha_valid : QAlpha.validAll p2_source p2_source_renames = true := by decide +kernel
theorem p2_view_eq (ρ M ι κ) : sView p2_source_plus ρ M ι κ = sView Bapa.ToyConsensusForallTransport.machine ρ M ι κ := by rfl
theorem p2_next_eq (ρ M ι κ) : sNext p2_source_plus ρ M ι κ = sNext Bapa.ToyConsensusForallTransport.machine ρ M ι κ := by rfl
theorem p2_assume_eq : p2_source_plus.f.m.assume = p2_source_assume := by rfl
theorem p2_target_assume_eq : Bapa.ToyConsensusForallTransport.machine.f.m.assume = p2_target_assume := by rfl

theorem p2_admission (ρ M) : evalC ρ M p2_source_assume = true → evalC ρ M p2_target_assume = true := by
  intro h
  simp_all [p2_source_assume, p2_target_assume, evalC]

theorem p2_inclusion : SourceInclusion p2_source_plus Bapa.ToyConsensusForallTransport.machine where
  inputs := by rfl
  carried := by rfl
  initial := by rfl
  startMaps := by intro M h; exact h
  pre := by intro ρ M h; exact h
  facts := by intro ρ M h; exact h
  pfacts := by intro ρ M h; exact h
  admission := by
    intro ρ M ι κ h
    rw [p2_view_eq, p2_assume_eq] at h
    rw [p2_target_assume_eq]
    exact p2_admission _ _ h
  next := by intro ρ M ι κ _; exact p2_next_eq ρ M ι κ

theorem p2_entry_law_eq : p2_entry.e.law = p2_unbounded_law := by rfl

theorem p2_law_implication : SourceLawImplication p2_entry.e p2_weak_entry := by
  apply sourceLawImplication_of_pointwise
  · rw [p2_entry_law_eq]; rfl
  · rfl
  · intro ρ M h
    change evalC ρ M p2_source_law.holds = true
    rw [p2_entry_law_eq] at h
    simp_all [p2_unbounded_law, p2_source_law, evalC]
    rcases h with (h | h) | h
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr h

theorem bapa_toy_consensus_forall_transported_laws : ∀ ρ M, CReach Bapa.ToyConsensusForallTransport.machine Bapa.ToyConsensusForallTransport.declarations ρ M →
    ∀ e ∈ Bapa.ToyConsensusForallTransport.proof, e.e.Holds ρ (withCnt Bapa.ToyConsensusForallTransport.declarations ρ M) := Bapa.ToyConsensusForallTransport.laws

theorem bapa_toy_consensus_forall_source_law0_holds (ρ M)
    (hr : CReach p2_source p2_source_decls ρ M) :
    holdsOver p2_source_law (withCnt p2_source_decls ρ M) p2_source_keys ρ := by
  have ha : CReach p2_source_alpha p2_source_decls ρ M :=
    (QAlpha.renameAll_equiv p2_source p2_source_renames p2_alpha_valid).symm.creach_imp p2_source_decls hr
  have h := bapa_counted_source_law p2_source_alpha p2_source_decls Bapa.ToyConsensusForallTransport.declarations
    p2_fresh p2_fresh p2_entry.e
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by
      intro d hd
      simp only [p2_source_decls, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl
      simp [Bapa.ToyConsensusForallTransport.declarations, captured_toy_consensus_forall_0_decls, Bapa.CertificateBoundErasure.countDeclaration, Bapa.CertificateBoundErasure.expr, Bapa.CertificateBoundErasure.condition])
    (by
      intro d hd hn
      simp only [Bapa.ToyConsensusForallTransport.declarations, captured_toy_consensus_forall_0_decls, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;>
        simp_all [p2_fresh, p2_source_decls, Bapa.CertificateBoundErasure.countDeclaration, Bapa.CertificateBoundErasure.expr, Bapa.CertificateBoundErasure.condition])
    (stepAvoids_of_check _ _ (by decide +kernel)) (by decide +kernel)
    (by
      intro X N hh
      have ht := p2_inclusion.creach Bapa.ToyConsensusForallTransport.declarations hh
      apply Bapa.ToyConsensusForallTransport.laws X N ht p2_entry
      simp only [p2_entry]
      apply List.getElem_mem) ρ M ha
  exact p2_law_implication ρ _ h

#print axioms p2_inclusion
#print axioms p2_law_implication
#print axioms bapa_toy_consensus_forall_transported_laws
#print axioms bapa_toy_consensus_forall_source_law0_holds

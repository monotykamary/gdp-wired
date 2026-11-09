-- Appended to the exact retained definitions and a one-binder alpha variant.
-- No theorem from the rejected original export is included.
def paxos_row_old : C := (verified_machine.qflags[2]).2.2
def paxos_row_new : C := (paxos_alpha_machine.qflags[2]).2.2

theorem paxos_row_alpha (X : Nat → Nat) (N : Nat → Nat → Nat) :
    (∀ k, holdsC (atKeys X [29] k) N paxos_row_old) ↔
    (∀ k, holdsC (atKeys X [131] k) N paxos_row_new) := by
  constructor
  · intro h k
    have hk := h (fun _ => k 131)
    simpa [paxos_row_old, paxos_row_new, verified_machine, paxos_alpha_machine, holdsC, evalE, atKeys] using hk
  · intro h k
    have hk := h (fun _ => k 29)
    simpa [paxos_row_old, paxos_row_new, verified_machine, paxos_alpha_machine, holdsC, evalE, atKeys] using hk

theorem paxos_decideQ_alpha (X : Nat → Nat) (N : Nat → Nat → Nat) :
    decideQ paxos_alpha_machine X N = decideQ verified_machine X N := by
  classical
  funext v
  by_cases h70 : v = 70
  · subst v; simp [decideQ, verified_machine, paxos_alpha_machine, lookup]
  by_cases h71 : v = 71
  · subst v; simp [decideQ, verified_machine, paxos_alpha_machine, lookup]
  by_cases h72 : v = 72
  · subst v
    change (if ∀ k, holdsC (atKeys X [131] k) N paxos_row_new then 1 else 0) =
      (if ∀ k, holdsC (atKeys X [29] k) N paxos_row_old then 1 else 0)
    rw [paxos_row_alpha]
  by_cases h81 : v = 81
  · subst v; simp [decideQ, verified_machine, paxos_alpha_machine, lookup]
  · simp [decideQ, verified_machine, paxos_alpha_machine, lookup, Ne.symm h70, Ne.symm h71, Ne.symm h72, Ne.symm h81]

theorem paxos_view_alpha (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    sView paxos_alpha_machine ρ M ι κ = sView verified_machine ρ M ι κ := by
  unfold sView
  rw [paxos_decideQ_alpha]
  rfl

theorem paxos_next_alpha (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    sNext paxos_alpha_machine ρ M ι κ = sNext verified_machine ρ M ι κ := by
  unfold sNext
  rw [paxos_view_alpha]
  rfl

theorem paxos_reach_alpha (ds : List CDecl) (ρ : Nat → Nat) (M : Nat → Nat → Nat) :
    CReach paxos_alpha_machine ds ρ M ↔ CReach verified_machine ds ρ M := by
  have hf : paxos_alpha_machine.f = verified_machine.f := rfl
  constructor
  · intro h
    induction h with
    | start ρ M hM hp hf hpf => exact .start ρ M hM hp hf hpf
    | step ρ M ι κ hr hg ha ih =>
      have ht := CReach.step ρ M ι κ ih hg (by simpa only [paxos_view_alpha, hf] using ha)
      simpa only [paxos_next_alpha] using ht
  · intro h
    induction h with
    | start ρ M hM hp hf hpf => exact .start ρ M hM hp hf hpf
    | step ρ M ι κ hr hg ha ih =>
      have ht := CReach.step ρ M ι κ ih hg (by simpa only [paxos_view_alpha, hf] using ha)
      simpa only [paxos_next_alpha] using ht

def paxos_law12 := verified_proof[12]
def paxos_entries := verified_proof.map (·.e)
theorem paxos_original_entry12_rejected : cEntryOk verified_machine verified_decls paxos_entries paxos_law12.e = false := by decide +kernel
theorem paxos_alpha_entry12_accepted : cEntryOk paxos_alpha_machine verified_decls paxos_entries paxos_law12.e = true := by decide +kernel
theorem paxos_alpha_witnesses12 : witsOk paxos_alpha_machine paxos_entries paxos_law12.start = true ∧ witsOk paxos_alpha_machine paxos_entries paxos_law12.step = true := by decide +kernel
theorem paxos_alpha_start12 : checkMC (cStartGoal paxos_alpha_machine verified_decls paxos_law12.e) (cStartDecls paxos_alpha_machine verified_decls) paxos_law12.start = true := by decide +kernel
theorem paxos_alpha_step12 : checkMC (cStepGoal paxos_alpha_machine verified_decls paxos_entries paxos_law12.e) (cStepDecls paxos_alpha_machine verified_decls) paxos_law12.step = true := by decide +kernel
theorem paxos_alpha_whole_rejected : checkCMachine paxos_alpha_machine verified_decls verified_proof = false := by decide +kernel
#print axioms paxos_row_alpha
#print axioms paxos_decideQ_alpha
#print axioms paxos_view_alpha
#print axioms paxos_next_alpha
#print axioms paxos_reach_alpha
#print axioms paxos_original_entry12_rejected
#print axioms paxos_alpha_entry12_accepted
#print axioms paxos_alpha_witnesses12
#print axioms paxos_alpha_start12
#print axioms paxos_alpha_step12
#print axioms paxos_alpha_whole_rejected

theorem paxos_alpha_entries_accepted : verified_proof.all (fun ce => cEntryOk paxos_alpha_machine verified_decls paxos_entries ce.e) = true := by decide +kernel
theorem paxos_alpha_step20_rejected : checkMC (cStepGoal paxos_alpha_machine verified_decls paxos_entries verified_proof[20].e) (cStepDecls paxos_alpha_machine verified_decls) verified_proof[20].step = false := by decide +kernel
#print axioms paxos_alpha_entries_accepted
#print axioms paxos_alpha_step20_rejected

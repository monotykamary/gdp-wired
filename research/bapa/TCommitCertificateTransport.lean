import Proofs

/-! A separate, concrete no-search certificate transport. This does not claim
    to recognize the relational fragment or to implement a cutoff. The only
    change is erasing the literal size cap from the machine and from the
    certificate's named hypotheses. Every proof tree and variable table stays
    definitionally identical to the retained certificate. The kernel, not an
    assumption about unused hypotheses, decides whether this is valid. -/
namespace Bapa.TCommitCertificateTransport
open Kern
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def cap : C := .le (.var 0) (.const 64)

def eraseCap (c : C) : C := if c = cap then trueC else c

def transportCertificate (k : Kern.Cert) : Kern.Cert :=
  (k.1, k.2.1.map eraseCap, k.2.2)

def entry : SEntry := {captured_tcommit_0_e0 with
  start := transportCertificate captured_tcommit_0_e0.start
  step := transportCertificate captured_tcommit_0_e0.step}

def proof : List SEntry := [entry]

def machine : SMachine := {captured_tcommit_0_machine with
  f := {captured_tcommit_0_machine.f with
    m := {captured_tcommit_0_machine.f.m with pre := trueC}}}

theorem tree_unchanged (k : Kern.Cert) :
    (transportCertificate k).2.2 = k.2.2 := rfl

theorem table_unchanged (k : Kern.Cert) :
    (transportCertificate k).1 = k.1 := rfl

theorem no_size_cap : machine.f.m.pre = trueC := rfl

theorem check : checkSMachine machine proof = true := by decide +kernel

theorem laws : ∀ ρ M, SReach machine ρ M → ∀ e ∈ proof, e.Holds ρ M :=
  smachine_sound machine proof check

theorem safety (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : SReach machine ρ μ) :
    ∀ a b : Nat, a < ρ 0 → b < ρ 0 → ¬ (μ 0 a = 3 ∧ μ 0 b = 2) := by
  have hl : entry.Holds ρ μ := laws ρ μ h entry (by simp [proof])
  have hl' := fun a b => (evalC_iff (upd (upd ρ 4 b) 3 a) μ captured_tcommit_0_l0.holds).mp (hl b a)
  intro a b ha hb
  have ht := hl' a b
  simpa [captured_tcommit_0_l0, holdsC, evalE, upd, ha, hb] using ht

/-- The transition and request semantics are definitionally unchanged; only
    the set of admitted initial parameter valuations grows. -/
theorem request_semantics_unchanged (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    sView machine ρ M ι κ = sView captured_tcommit_0_machine ρ M ι κ := rfl

theorem step_semantics_unchanged (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    sNext machine ρ M ι κ = sNext captured_tcommit_0_machine ρ M ι κ := rfl

/-- Keep both negative controls: neither mismatched named premise list passes. -/
theorem stale_cap_annotation_rejected :
    checkSMachine machine captured_tcommit_0_proof = false := by decide +kernel

theorem unmodified_machine_rejects_transported_annotation :
    checkSMachine captured_tcommit_0_machine proof = false := by decide +kernel

#print axioms request_semantics_unchanged
#print axioms step_semantics_unchanged
#print axioms stale_cap_annotation_rejected
#print axioms unmodified_machine_rejects_transported_annotation
#print axioms tree_unchanged
#print axioms table_unchanged
#print axioms no_size_cap
#print axioms check
#print axioms laws
#print axioms safety
end Bapa.TCommitCertificateTransport

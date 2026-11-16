import Checks
import SumChecks
import SdlSourceDefs

namespace Bapa.SimpleDecentralizedLockTransport
open Kern
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Checked
theorem family : checkSMachine target.plain proof = true := by
  rw [Bapa.SdlConcrete.target_eq, Bapa.SdlConcrete.proof_eq]
  exact Bapa.SdlConcrete.Checked.family
theorem cover : checkSums target proof covers = true := by
  rw [Bapa.SdlConcrete.target_eq, Bapa.SdlConcrete.proof_eq, Bapa.SdlConcrete.covers_eq]
  exact Bapa.SdlConcrete.Checked.cover
end Checked

theorem exact_sums : ∀ ρ M, SReach target.plain ρ M →
    ∀ d ∈ target.sums, IsSum (gAt d.g M) (ρ d.v) :=
  sum_holds target Checked.family Checked.cover

theorem own_admission : ∀ ρ M, SReach target.plain ρ M → ∀ ι κ,
    evalC (sView target.plain ρ M ι κ).1 (sView target.plain ρ M ι κ).2 target.plain.f.m.assume =
    evalC (sView target.plain ρ M ι κ).1 (sView target.plain ρ M ι κ).2 target.s.f.m.assume :=
  sum_allowed target Checked.family Checked.cover

theorem sum_ghosts_valid : sghostOk target.ghosts = true := by decide +kernel

def publicEntry : SEntry := proof[2]'(by decide +kernel)
theorem public_shape : publicEntry.law =
    {captured_simple_decentralized_lock_0_l2 with holds := CertificateBoundErasure.condition 64 captured_simple_decentralized_lock_0_l2.holds} ∧
    publicEntry.keys2 = [9] := by constructor <;> rfl

theorem public_base (ρ M) (hr : SReach target.s ρ M) : publicEntry.Holds ρ M :=
  sum_project_laws target sum_ghosts_valid proof Checked.family Checked.cover ρ M hr publicEntry
    (List.getElem_mem (by decide +kernel)) (by decide +kernel)

theorem mutual_exclusion (ρ M) (hr : SReach target.s ρ M) (a b : Nat)
    (ha : M 1 a = 1) (hb : M 1 b = 1) : a = b := by
  have h := public_base ρ M hr
  change holdsOver publicEntry.law M publicEntry.keys2 ρ at h
  rw [public_shape.1,public_shape.2] at h
  have hab := h b a
  simpa [captured_simple_decentralized_lock_0_l2, CertificateBoundErasure.condition,
    CertificateBoundErasure.expr, trueC, evalC, evalE, upd, ha, hb] using hab

def messageEntry : SEntry := proof[0]'(by decide +kernel)
theorem message_shape : messageEntry.law =
    ⟨.le (.get 0 (.tup (.var 6) (.var 1000000))) (.const 1), some 6⟩ ∧
    messageEntry.keys2 = [1000000] := by constructor <;> rfl

theorem message_bound (ρ M) (hr : SReach target.s ρ M) (a b : Nat) :
    M 0 (cpair a b) ≤ 1 := by
  have h := sum_project_laws target sum_ghosts_valid proof Checked.family Checked.cover ρ M hr messageEntry
    (List.getElem_mem (by decide +kernel)) (by decide +kernel)
  change holdsOver messageEntry.law M messageEntry.keys2 ρ at h
  rw [message_shape.1,message_shape.2] at h
  have hab := h b a
  simpa [evalC,evalE,upd] using hab

#print axioms message_bound
#print axioms exact_sums
#print axioms own_admission
#print axioms sum_ghosts_valid
#print axioms public_base
#print axioms mutual_exclusion
end Bapa.SimpleDecentralizedLockTransport

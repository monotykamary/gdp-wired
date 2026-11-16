import PaxosEprAtomicZero
namespace Bapa.PaxosEprAtomicSource
open Kern

private theorem head_true {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> simp_all
private theorem tail_true {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> simp_all

theorem param_view (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (i : Nat) (hi : i < 4) : (sView machine ρ M ι κ).1 i = ρ i := by
  have hs : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hs with rfl | rfl | rfl | rfl <;>
    simp [sView, machine, decideFlags, applyS, flagSub, assoc, lookup, decideQ, withInputs]

theorem param_next (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (i : Nat) (hi : i < 4) : (sNext machine ρ M ι κ).1 i = ρ i := by
  change (sView machine ρ M ι κ).1 i = ρ i
  exact param_view ρ M ι κ i hi

theorem admitted_coordinates (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (ha : evalC (sView machine ρ M ι κ).1 (sView machine ρ M ι κ).2 machine.f.m.assume = true) :
    (sView machine ρ M ι κ).1 5 < ρ 0 ∧
    (sView machine ρ M ι κ).1 6 < ρ 1 ∧ (sView machine ρ M ι κ).1 7 < ρ 2 := by
  have hn : (sView machine ρ M ι κ).1 5 < (sView machine ρ M ι κ).1 0 :=
    of_decide_eq_true (head_true (tail_true ha))
  have hr : (sView machine ρ M ι κ).1 6 < (sView machine ρ M ι κ).1 1 :=
    of_decide_eq_true (head_true (tail_true (tail_true (tail_true ha))))
  have hv : (sView machine ρ M ι κ).1 7 < (sView machine ρ M ι κ).1 2 :=
    of_decide_eq_true (head_true (tail_true (tail_true (tail_true (tail_true (tail_true ha))))))
  rw [param_view ρ M ι κ 0 (by decide)] at hn
  rw [param_view ρ M ι κ 1 (by decide)] at hr
  rw [param_view ρ M ι κ 2 (by decide)] at hv
  exact ⟨hn,hr,hv⟩

def BoundedSupport (ρ : Nat → Nat) (M : Nat → Nat → Nat) : Prop :=
  (∀ n r v, 1 ≤ M 4 (cpair n (cpair r v)) → n < ρ 0 ∧ r < ρ 1 ∧ v < ρ 2) ∧
  (∀ r v, 1 ≤ M 3 (cpair r v) → r < ρ 1 ∧ v < ρ 2)

theorem vote_off_key (D : Nat → Nat) (N : Nat → Nat → Nat) (key : Nat)
    (hne : key ≠ cpair (D 5) (cpair (D 6) (D 7))) :
    everyMaps machine D N 4 key = N 4 key := by
  simp [everyMaps, machine, lookup, writeMaps, evalE, hne]

theorem proposal_off_key (D : Nat → Nat) (N : Nat → Nat → Nat) (key : Nat)
    (hne : key ≠ cpair (D 6) (D 7)) : everyMaps machine D N 3 key = N 3 key := by
  simp [everyMaps, machine, lookup, writeMaps, evalE, hne]

theorem support_start (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hm : StartMaps machine.f.m M) :
    BoundedSupport ρ M := by
  constructor
  · intro n r v h
    have hz : M 4 (cpair n (cpair r v)) = 0 := hm (4,0) (by decide +kernel) _
    rw [hz] at h
    omega
  · intro r v h
    have hz : M 3 (cpair r v) = 0 := hm (3,0) (by decide +kernel) _
    rw [hz] at h
    omega

theorem support_step (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (hs : BoundedSupport ρ M)
    (ha : evalC (sView machine ρ M ι κ).1 (sView machine ρ M ι κ).2 machine.f.m.assume = true) :
    BoundedSupport (sNext machine ρ M ι κ).1 (sNext machine ρ M ι κ).2 := by
  have hb := admitted_coordinates ρ M ι κ ha
  constructor
  · intro n r v h
    rw [param_next ρ M ι κ 0 (by decide), param_next ρ M ι κ 1 (by decide), param_next ρ M ι κ 2 (by decide)]
    by_cases he : cpair n (cpair r v) = cpair ((sView machine ρ M ι κ).1 5)
        (cpair ((sView machine ρ M ι κ).1 6) ((sView machine ρ M ι κ).1 7))
    · have hp := congrArg cun he
      simp only [cun_cpair, Prod.mk.injEq] at hp
      have ht := congrArg cun hp.2
      simp only [cun_cpair, Prod.mk.injEq] at ht
      simpa only [hp.1, ht.1, ht.2] using hb
    · have ho : (sNext machine ρ M ι κ).2 4 (cpair n (cpair r v)) = M 4 (cpair n (cpair r v)) := by
        change everyMaps machine (sView machine ρ M ι κ).1 (sView machine ρ M ι κ).2 4 _ = _
        rw [vote_off_key _ _ _ he]
        rfl
      rw [ho] at h
      exact hs.1 n r v h
  · intro r v h
    rw [param_next ρ M ι κ 1 (by decide), param_next ρ M ι κ 2 (by decide)]
    by_cases he : cpair r v = cpair ((sView machine ρ M ι κ).1 6) ((sView machine ρ M ι κ).1 7)
    · have hp := congrArg cun he
      simp only [cun_cpair, Prod.mk.injEq] at hp
      simpa only [hp.1, hp.2] using hb.2
    · have ho : (sNext machine ρ M ι κ).2 3 (cpair r v) = M 3 (cpair r v) := by
        change everyMaps machine (sView machine ρ M ι κ).1 (sView machine ρ M ι κ).2 3 _ = _
        rw [proposal_off_key _ _ _ he]
        rfl
      rw [ho] at h
      exact hs.2 r v h

theorem reachable_support {ρ M} (hr : SReach machine ρ M) : BoundedSupport ρ M := by
  induction hr with
  | start ρ M hm _ _ _ => exact support_start ρ M hm
  | step ρ M ι κ _ ha ih => exact support_step ρ M ι κ ih ha

theorem counted_reachable_support {ds : List CDecl} {ρ M} (hr : CReach machine ds ρ M) :
    BoundedSupport ρ M := reachable_support (creach_sreach hr)

/-- Support closes the gap between bounded and unbounded noProposal. -/
theorem proposal_guard_unbounded {ρ M} (hs : BoundedSupport ρ M) (r : Nat)
    (bounded : ∀ v, v < ρ 2 → M 3 (cpair r v) = 0) : ∀ v, M 3 (cpair r v) = 0 := by
  intro v
  by_cases hp : 1 ≤ M 3 (cpair r v)
  · exact bounded v (hs.2 r v hp).2
  · omega

/-- The source's bounded universal row condition covers every positive target
vote. No round/value cap is imposed on the target quantifier. -/
theorem vote_guard_unbounded {ρ M} (hs : BoundedSupport ρ M) (Q : Nat → Prop) (pr mr none : Nat)
    (bounded : ∀ n r v, Q n → r < ρ 1 → v < ρ 2 → 1 ≤ M 4 (cpair n (cpair r v)) →
      r < pr → mr ≠ none ∧ r ≤ mr) :
    ∀ n r v, Q n → M 4 (cpair n (cpair r v)) = 1 → r < pr → mr ≠ none ∧ r ≤ mr := by
  intro n r v hq hv hr
  have positive : 1 ≤ M 4 (cpair n (cpair r v)) := by omega
  have hb := hs.1 n r v positive
  exact bounded n r v hq hb.2.1 hb.2.2 positive hr

#print axioms proposal_guard_unbounded
#print axioms vote_guard_unbounded
#print axioms admitted_coordinates
#print axioms reachable_support
#print axioms counted_reachable_support
end Bapa.PaxosEprAtomicSource

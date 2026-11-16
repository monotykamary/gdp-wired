import PaxosEprAtomicSupport
namespace Bapa.PaxosEprAtomicSource
open Kern

private theorem of_code_one {p : Prop} [Decidable p]
    (h : (if p then (1 : Nat) else 0) = 1) : p := by
  by_cases hp : p
  · exact hp
  · simp only [if_neg hp] at h
    contradiction

theorem noProposal_from_flag (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (h : (sView machine ρ M ι κ).1 11 = 1) :
    ∀ v, v < ρ 2 → M 3 (cpair (ι 6) v) = 0 := by
  have hall : ∀ k : Nat → Nat, ¬ k 26 < ρ 2 ∨ ¬ 1 ≤ M 3 (cpair (ι 6) (k 26)) := by
    classical
    apply of_code_one
    simpa [sView, machine, decideFlags, applyS, flagSub, assoc, lookup, decideQ,
      withInputs, holdsC, evalE, atKeys, withCarried] using h
  intro v hv
  have hb := hall (fun _ => v)
  rcases hb with hn | hn
  · exact False.elim (hn hv)
  · omega

theorem joined_from_flag (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (h : (sView machine ρ M ι κ).1 12 = 1) :
    ∀ n, 1 ≤ κ 6 n → 1 ≤ M 1 (cpair (ι 6) n) := by
  have hall : ∀ k : Nat → Nat, ¬ 1 ≤ κ 6 (k 27) ∨ 1 ≤ M 1 (cpair (ι 6) (k 27)) := by
    classical
    apply of_code_one
    simpa [sView, machine, decideFlags, applyS, flagSub, assoc, lookup, decideQ,
      withInputs, holdsC, evalE, atKeys, withCarried] using h
  intro n hn
  exact (hall (fun _ => n)).resolve_left (fun hc => hc hn)

theorem voteRows_from_flag (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (h : (sView machine ρ M ι κ).1 13 = 1) :
    ∀ n r v, 1 ≤ κ 6 n → r < ρ 1 → v < ρ 2 → 1 ≤ M 4 (cpair n (cpair r v)) →
      r < ι 6 → ι 8 ≠ ρ 3 ∧ r ≤ ι 8 := by
  have hall : ∀ k : Nat → Nat,
      ¬ (1 ≤ κ 6 (k 28) ∧ k 29 < ρ 1 ∧ k 30 < ρ 2 ∧
        1 ≤ M 4 (cpair (k 28) (cpair (k 29) (k 30))) ∧ k 29 < ι 6) ∨
      (ι 8 ≠ ρ 3 ∧ k 29 ≤ ι 8) := by
    classical
    apply of_code_one
    simpa [sView, machine, decideFlags, applyS, flagSub, assoc, lookup, decideQ,
      withInputs, holdsC, evalE, atKeys, withCarried] using h
  intro n r v hn hr hv hVote hLt
  have hh := hall (fun i => if i = 28 then n else if i = 29 then r else v)
  exact hh.resolve_left (fun hc => hc ⟨hn,hr,hv,hVote,hLt⟩)

theorem quorumValid_from_flag (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (h : (sView machine ρ M ι κ).1 19 = 1) :
    ∀ n, κ 6 n ≤ 1 ∧ (1 ≤ κ 6 n → n < ρ 0) := by
  have hall : ∀ k : Nat → Nat, κ 6 (k 31) ≤ 1 ∧ (¬ 1 ≤ κ 6 (k 31) ∨ k 31 < ρ 0) := by
    classical
    apply of_code_one
    simpa [sView, machine, decideFlags, applyS, flagSub, assoc, lookup, decideQ,
      withInputs, holdsC, evalE, atKeys, withCarried] using h
  intro n
  have hh := hall (fun _ => n)
  exact ⟨hh.1, fun hn => hh.2.resolve_left (fun hc => hc hn)⟩

theorem reachable_noProposal_unbounded {ds : List CDecl} {ρ M}
    (hr : CReach machine ds ρ M) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (h : (sView machine ρ M ι κ).1 11 = 1) : ∀ v, M 3 (cpair (ι 6) v) = 0 :=
  proposal_guard_unbounded (counted_reachable_support hr) (ι 6) (noProposal_from_flag ρ M ι κ h)

theorem reachable_voteRows_unbounded {ds : List CDecl} {ρ M}
    (hr : CReach machine ds ρ M) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (h : (sView machine ρ M ι κ).1 13 = 1) :
    ∀ n r v, 1 ≤ κ 6 n → M 4 (cpair n (cpair r v)) = 1 →
      r < ι 6 → ι 8 ≠ ρ 3 ∧ r ≤ ι 8 :=
  vote_guard_unbounded (counted_reachable_support hr) (fun n => 1 ≤ κ 6 n)
    (ι 6) (ι 8) (ρ 3) (voteRows_from_flag ρ M ι κ h)

#print axioms noProposal_from_flag
#print axioms joined_from_flag
#print axioms voteRows_from_flag
#print axioms quorumValid_from_flag
#print axioms reachable_noProposal_unbounded
#print axioms reachable_voteRows_unbounded
end Bapa.PaxosEprAtomicSource

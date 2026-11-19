import Count

/- No new count-checker rule. An ordinary Lean finite-sum theorem composes
   the checked local transition obligations of the research certificate. -/
namespace FiniteFold
open Kern

theorem spike (n t : Nat) (v : Nat) (ht : t < n) :
    sumBelow (fun k => if k = t then v else 0) n = v := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n = t
    · subst t
      have hz : sumBelow (fun k => if k = n then v else 0) n = 0 := by
        calc
          _ = sumBelow (fun _ => 0) n := by
            apply sumBelow_congr
            intro k hk
            simp [Nat.ne_of_lt hk]
          _ = 0 := sumBelow_zero_fn n
      simp [sumBelow, hz]
    · have hn : t < n := by omega
      simp [sumBelow, ih hn, h]

theorem point_delta (f g : Nat → Nat) (n t : Nat) (ht : t < n)
    (frame : ∀ k, k < n → k ≠ t → g k = f k) :
    sumBelow g n + f t = sumBelow f n + g t := by
  rw [← spike n t (f t) ht, ← spike n t (g t) ht]
  rw [← sumBelow_add, ← sumBelow_add]
  apply sumBelow_congr n
  intro k hk
  by_cases he : k = t
  · subst k; simp [Nat.add_comm]
  · simp [he, frame k hk he]

theorem coupled_change (f g : Nat → Nat) (n t before after : Nat)
    (ht : t < n) (frame : ∀ k, k < n → k ≠ t → g k = f k)
    (old : before = sumBelow f n) (delta : after + f t = before + g t) :
    after = sumBelow g n := by
  have h := point_delta f g n t ht frame
  omega

end FiniteFold

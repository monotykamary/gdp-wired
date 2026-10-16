import Cert
def lossStep (b m : Nat) (s c : Nat) : Nat := if s < b then s + min c m else s
theorem loss_step (b m s c : Nat) (h : s ≤ b + m) : lossStep b m s c ≤ b + m := by
  unfold lossStep; split <;> omega
theorem bounded_loss (b m : Nat) (cs : List Nat) : cs.foldl (lossStep b m) 0 ≤ b + m :=
  Cert.run_preserves (lossStep b m) (fun s => s ≤ b + m) 0 (by omega) (fun s c h => loss_step b m s c h) cs

structure A where
  Acct : Nat → Nat
  Day : Nat → Nat
structure R where
  acct : Nat
  day : Nat
  ok : Nat
def upd (f : Nat → Nat) (k v : Nat) : Nat → Nat := fun y => if y = k then v else f y
def admitStep (d : Nat) (st : A) (r : R) : A :=
  let g := r.ok = 1 ∧ st.Acct r.acct < 1 ∧ st.Day r.day < d
  { Acct := upd st.Acct r.acct (if g then st.Acct r.acct + 1 else st.Acct r.acct),
    Day := upd st.Day r.day (if g then st.Day r.day + 1 else st.Day r.day) }
theorem day_step (d : Nat) (st : A) (r : R) (h : ∀ k, st.Day k ≤ d) : ∀ k, (admitStep d st r).Day k ≤ d := by
  intro k
  by_cases e : k = r.day
  · subst e
    have hk := h r.day
    simp only [admitStep, upd, ite_true]
    split <;> omega
  · have hk := h k
    simp only [admitStep, upd, e, ite_false]
    omega

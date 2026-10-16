import Cert
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! Generated from gdp-wired's machines (core/models.ts) and proven here by omega, independently of the solver. -/

def upd (f : Nat → Nat) (k v : Nat) : Nat → Nat := fun y => if y = k then v else f y

namespace Loss
structure St where
  s : Nat
structure In where
  c : Nat
def init (b : Nat) (m : Nat) : St := { s := 0 }
def step (b : Nat) (m : Nat) (st : St) (i : In) : St :=
  { s := (if st.s < b then (st.s + (min i.c m)) else st.s) }

def Inv (b : Nat) (m : Nat) (st : St) : Prop := (st.s ≤ (b + m))
theorem step_inv (b : Nat) (m : Nat) (st : St) (i : In) (h : Inv b m st) : Inv b m (step b m st i) := by
  simp only [Inv, step] at h ⊢
  (repeat' split) <;> omega
theorem inv_always (b : Nat) (m : Nat) (is : List In) : Inv b m (is.foldl (step b m) (init b m)) :=
  Cert.run_preserves (step b m) (Inv b m) (init b m) (by simp only [Inv, init]; omega) (step_inv b m) is

theorem bounded_loss (b : Nat) (m : Nat) (is : List In) : (is.foldl (step b m) (init b m)).s ≤ (b + m) := by
  have h := inv_always b m is
  simp only [Inv] at h
  omega

end Loss

namespace Admit
structure St where
  Acct : Nat → Nat
  Day : Nat → Nat
  Hour : Nat → Nat
  Dom : Nat → Nat
structure In where
  acct : Nat
  day : Nat
  hour : Nat
  dom : Nat
  ok : Nat
def init (d : Nat) (hr : Nat) (dm : Nat) : St := { Acct := fun _ => 0, Day := fun _ => 0, Hour := fun _ => 0, Dom := fun _ => 0 }
def step (d : Nat) (hr : Nat) (dm : Nat) (st : St) (i : In) : St :=
  { Acct := upd st.Acct i.acct (if (i.ok = 1 ∧ (st.Acct i.acct) < 1 ∧ (st.Day i.day) < d ∧ (st.Hour i.hour) < hr ∧ (st.Dom i.dom) < dm) then ((st.Acct i.acct) + 1) else (st.Acct i.acct)),
    Day := upd st.Day i.day (if (i.ok = 1 ∧ (st.Acct i.acct) < 1 ∧ (st.Day i.day) < d ∧ (st.Hour i.hour) < hr ∧ (st.Dom i.dom) < dm) then ((st.Day i.day) + 1) else (st.Day i.day)),
    Hour := upd st.Hour i.hour (if (i.ok = 1 ∧ (st.Acct i.acct) < 1 ∧ (st.Day i.day) < d ∧ (st.Hour i.hour) < hr ∧ (st.Dom i.dom) < dm) then ((st.Hour i.hour) + 1) else (st.Hour i.hour)),
    Dom := upd st.Dom i.dom (if (i.ok = 1 ∧ (st.Acct i.acct) < 1 ∧ (st.Day i.day) < d ∧ (st.Hour i.hour) < hr ∧ (st.Dom i.dom) < dm) then ((st.Dom i.dom) + 1) else (st.Dom i.dom)) }

theorem step_once_per_account (d : Nat) (hr : Nat) (dm : Nat) (st : St) (i : In) (h : ∀ k, (st.Acct k) ≤ 1) : ∀ k, ((step d hr dm st i).Acct k) ≤ 1 := by
  intro k
  by_cases e : k = i.acct
  · rw [e]
    have hk := h i.acct
    simp only [step, upd, ite_true]
    (repeat' split) <;> omega
  · have hk := h k
    simp only [step, upd, e, ite_false]
    omega
theorem once_per_account (d : Nat) (hr : Nat) (dm : Nat) (is : List In) : ∀ k, ((is.foldl (step d hr dm) (init d hr dm)).Acct k) ≤ 1 :=
  Cert.run_preserves (step d hr dm) (fun st => ∀ k, (st.Acct k) ≤ 1) (init d hr dm) (by intro k; simp only [init]; omega) (step_once_per_account d hr dm) is

theorem step_day_cap (d : Nat) (hr : Nat) (dm : Nat) (st : St) (i : In) (h : ∀ k, (st.Day k) ≤ d) : ∀ k, ((step d hr dm st i).Day k) ≤ d := by
  intro k
  by_cases e : k = i.day
  · rw [e]
    have hk := h i.day
    simp only [step, upd, ite_true]
    (repeat' split) <;> omega
  · have hk := h k
    simp only [step, upd, e, ite_false]
    omega
theorem day_cap (d : Nat) (hr : Nat) (dm : Nat) (is : List In) : ∀ k, ((is.foldl (step d hr dm) (init d hr dm)).Day k) ≤ d :=
  Cert.run_preserves (step d hr dm) (fun st => ∀ k, (st.Day k) ≤ d) (init d hr dm) (by intro k; simp only [init]; omega) (step_day_cap d hr dm) is

theorem step_hour_cap (d : Nat) (hr : Nat) (dm : Nat) (st : St) (i : In) (h : ∀ k, (st.Hour k) ≤ hr) : ∀ k, ((step d hr dm st i).Hour k) ≤ hr := by
  intro k
  by_cases e : k = i.hour
  · rw [e]
    have hk := h i.hour
    simp only [step, upd, ite_true]
    (repeat' split) <;> omega
  · have hk := h k
    simp only [step, upd, e, ite_false]
    omega
theorem hour_cap (d : Nat) (hr : Nat) (dm : Nat) (is : List In) : ∀ k, ((is.foldl (step d hr dm) (init d hr dm)).Hour k) ≤ hr :=
  Cert.run_preserves (step d hr dm) (fun st => ∀ k, (st.Hour k) ≤ hr) (init d hr dm) (by intro k; simp only [init]; omega) (step_hour_cap d hr dm) is

theorem step_dom_cap (d : Nat) (hr : Nat) (dm : Nat) (st : St) (i : In) (h : ∀ k, (st.Dom k) ≤ dm) : ∀ k, ((step d hr dm st i).Dom k) ≤ dm := by
  intro k
  by_cases e : k = i.dom
  · rw [e]
    have hk := h i.dom
    simp only [step, upd, ite_true]
    (repeat' split) <;> omega
  · have hk := h k
    simp only [step, upd, e, ite_false]
    omega
theorem dom_cap (d : Nat) (hr : Nat) (dm : Nat) (is : List In) : ∀ k, ((is.foldl (step d hr dm) (init d hr dm)).Dom k) ≤ dm :=
  Cert.run_preserves (step d hr dm) (fun st => ∀ k, (st.Dom k) ≤ dm) (init d hr dm) (by intro k; simp only [init]; omega) (step_dom_cap d hr dm) is

end Admit

namespace Inflight
structure St where
  s : Nat
  p : Nat
structure In where
  t : Nat
  done : Nat
def init (b : Nat) : St := { s := 0, p := 0 }
def step (b : Nat) (st : St) (i : In) : St :=
  { s := (if (i.done = 1 ∧ 0 < st.p) then (st.s + (min i.t 50)) else st.s),
    p := (if i.done = 1 then (if 0 < st.p then (st.p - 1) else st.p) else (if (st.s < b ∧ st.p < 3) then (st.p + 1) else st.p)) }

def Inv (b : Nat) (st : St) : Prop := (st.s ≤ (b + 150)) ∧ ((st.s + (50 * st.p)) ≤ (b + 150))
theorem step_inv (b : Nat) (st : St) (i : In) (h : Inv b st) : Inv b (step b st i) := by
  simp only [Inv, step] at h ⊢
  refine ⟨?_, ?_⟩ <;> (repeat' split) <;> omega
theorem inv_always (b : Nat) (is : List In) : Inv b (is.foldl (step b) (init b)) :=
  Cert.run_preserves (step b) (Inv b) (init b) (by simp only [Inv, init]; omega) (step_inv b) is

theorem in_flight_loss (b : Nat) (is : List In) : (is.foldl (step b) (init b)).s ≤ (b + 150) := by
  have h := inv_always b is
  simp only [Inv] at h
  omega

theorem flight_invariant (b : Nat) (is : List In) : ((is.foldl (step b) (init b)).s + (50 * (is.foldl (step b) (init b)).p)) ≤ (b + 150) := by
  have h := inv_always b is
  simp only [Inv] at h
  omega

end Inflight

#print axioms Loss.bounded_loss
#print axioms Admit.once_per_account
#print axioms Admit.day_cap
#print axioms Admit.hour_cap
#print axioms Admit.dom_cap
#print axioms Inflight.in_flight_loss

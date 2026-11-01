import Data

/-!
Nested recursion end to end (lean-kernel/Data.lean's `wf_fix_inv_unique`): two definitions core/data.ts takes now, each
a call in another's argument, defined here through the theorem from the obligations the kernel proves for them
(core/data.test.ts reads the same obligations' texts). Each obligation is a law over the path's variables and a value r
per call of the function in the law (the call read as r, under `lexLt (μ a) (μ x) → I a r`); here each is proven by
omega, then `hF` from them, then the function, its equation, its uniqueness and a law about it.
`lean -R . Nested.lean` with lean-kernel's library on LEAN_PATH (lean-nested.sh).
-/

open Kern

namespace NestedEx

/-! ### nz 0 = 0, nz (n + 1) = nz (nz n): measure n, invariant nz n ≤ n -/

def nzF (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => g (g n)

/-- I: the value at most the argument. -/
def nzI (x r : Nat) : Prop := r ≤ x

-- call 1 (inner), at n + 1: nz n lowers n + 1
theorem nz_dec1 (n : Nat) : lexLt [n] [n + 1] := by simp [lexLt]
-- call 2 (outer), nz r with r the inner call: (lexLt [n] [n + 1] → r ≤ n) → lexLt [r] [n + 1]
theorem nz_dec2 (n r : Nat) (h : lexLt [n] [n + 1] → nzI n r) : lexLt [r] [n + 1] := by
  have := h (nz_dec1 n); simp only [nzI] at this; simp [lexLt]; omega
-- the body keeps I: at 0, 0 ≤ 0; at n + 1, the outer call's value r2 under its hypothesis and the inner's
theorem nz_inv (n r1 r2 : Nat) (h1 : lexLt [n] [n + 1] → nzI n r1) (h2 : lexLt [r1] [n + 1] → nzI r1 r2) : nzI (n + 1) r2 := by
  have a := h1 (nz_dec1 n); have b := h2 (nz_dec2 n r1 h1); simp only [nzI] at *; omega

theorem nz_hF (g h : Nat → Nat) (x : Nat) (hy : ∀ y, lexLt [y] [x] → g y = h y ∧ nzI y (g y)) :
    nzF g x = nzF h x ∧ nzI x (nzF g x) := by
  cases x with
  | zero => exact ⟨rfl, by simp [nzF, nzI]⟩
  | succ n =>
    have ⟨e1, i1⟩ := hy n (nz_dec1 n)
    have ⟨e2, _⟩ := hy (g n) (nz_dec2 n (g n) (fun _ => i1))
    refine ⟨?_, ?_⟩
    · show g (g n) = h (h n); rw [← e1, e2]
    · exact nz_inv n (g n) (g (g n)) (fun _ => i1) (fun d => (hy (g n) d).2)

theorem nz_exists : ∃ f : Nat → Nat, (∀ x, f x = nzF f x ∧ nzI x (f x)) ∧ ∀ f' : Nat → Nat, (∀ x, f' x = nzF f' x) → f' = f :=
  wf_fix_inv_unique (fun n => [n]) nzI nzF (fun g h x => nz_hF g h x)
noncomputable def nz : Nat → Nat := Classical.choose nz_exists
theorem nz_eq (n : Nat) : nz n = nzF nz n := ((Classical.choose_spec nz_exists).1 n).1
theorem nz_unique (f' : Nat → Nat) (h : ∀ n, f' n = nzF f' n) : f' = nz := (Classical.choose_spec nz_exists).2 f' h

/-- The law: nz n = 0. -/
theorem nz_zero : ∀ n, nz n = 0
  | 0 => by rw [nz_eq]; rfl
  | n + 1 => by rw [nz_eq]; show nz (nz n) = 0; rw [nz_zero n, nz_eq]; rfl

/-! ### A list, nest [] = [], nest (x :: xs) = x :: nest (nest xs): measure size, invariant size kept -/

inductive Lst where
  | nil
  | cons (h : Nat) (t : Lst)

def Lst.size : Lst → Nat
  | .nil => 1
  | .cons _ t => 1 + t.size

def nestF (g : Lst → Lst) : Lst → Lst
  | .nil => .nil
  | .cons x xs => .cons x (g (g xs))

def nestI (x r : Lst) : Prop := r.size = x.size

theorem nest_dec1 (x : Nat) (xs : Lst) : lexLt [xs.size] [(Lst.cons x xs).size] := by simp [lexLt, Lst.size]
theorem nest_dec2 (x : Nat) (xs r : Lst) (h : lexLt [xs.size] [(Lst.cons x xs).size] → nestI xs r) :
    lexLt [r.size] [(Lst.cons x xs).size] := by
  have := h (nest_dec1 x xs); simp only [nestI] at this; simp [lexLt, Lst.size]; omega
theorem nest_inv (x : Nat) (xs r1 r2 : Lst) (h1 : lexLt [xs.size] [(Lst.cons x xs).size] → nestI xs r1)
    (h2 : lexLt [r1.size] [(Lst.cons x xs).size] → nestI r1 r2) : nestI (Lst.cons x xs) (Lst.cons x r2) := by
  have a := h1 (nest_dec1 x xs); have b := h2 (nest_dec2 x xs r1 h1); simp only [nestI, Lst.size] at *; omega

theorem nest_hF (g h : Lst → Lst) (l : Lst) (hy : ∀ y, lexLt [y.size] [l.size] → g y = h y ∧ nestI y (g y)) :
    nestF g l = nestF h l ∧ nestI l (nestF g l) := by
  cases l with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs =>
    have ⟨e1, i1⟩ := hy xs (nest_dec1 x xs)
    have ⟨e2, _⟩ := hy (g xs) (nest_dec2 x xs (g xs) (fun _ => i1))
    refine ⟨?_, ?_⟩
    · show Lst.cons x (g (g xs)) = Lst.cons x (h (h xs)); rw [← e1, e2]
    · exact nest_inv x xs (g xs) (g (g xs)) (fun _ => i1) (fun d => (hy (g xs) d).2)

instance : Inhabited Lst := ⟨.nil⟩
theorem nest_exists : ∃ f : Lst → Lst, (∀ x, f x = nestF f x ∧ nestI x (f x)) ∧ ∀ f' : Lst → Lst, (∀ x, f' x = nestF f' x) → f' = f :=
  wf_fix_inv_unique (fun l => [l.size]) nestI nestF (fun g h l => nest_hF g h l)
noncomputable def nest : Lst → Lst := Classical.choose nest_exists
theorem nest_eq (l : Lst) : nest l = nestF nest l := ((Classical.choose_spec nest_exists).1 l).1
theorem nest_unique (f' : Lst → Lst) (h : ∀ l, f' l = nestF f' l) : f' = nest := (Classical.choose_spec nest_exists).2 f' h

/-- The law: nest l = l. -/
theorem nest_id : ∀ l, nest l = l
  | .nil => by rw [nest_eq]; rfl
  | .cons x xs => by rw [nest_eq]; show Lst.cons x (nest (nest xs)) = _; rw [nest_id xs, nest_id xs]

end NestedEx

#print axioms Kern.wf_fix_inv_unique_ring
#print axioms Kern.wf_fix_inv_unique
#print axioms NestedEx.nz_zero
#print axioms NestedEx.nz_unique
#print axioms NestedEx.nest_id
#print axioms NestedEx.nest_unique

import Cyclic

/-!
Data: recursive datatypes as values, for cyclic proofs. Lean 4.34.0, core only, on top of `Cyclic.lean`.

core/data.ts proves laws about datatypes (lists, trees, any declared with constructors whose fields are naturals or
values of the datatype) by cyclic proofs over an encoding: every natural is a value of each datatype, a value is read
through maps (its constructor's tag, its fields, its size), a function of several arguments is a map read at their
pairing `pk a b = (a + b)² + b` (left-nested). Nothing here is trusted beyond `Cyclic.lean`: an export defines the
datatype as a Lean `inductive` and the functions by pattern matching, gives each map of the encoding its meaning (the
model, through a bijection between the naturals and the datatype's values), proves every fact of the cyclic proof true
of that model, and concludes the law about the Lean definitions from `cyclic_sound`. What this file gives the exports:

- `pk`, the pairing, injective (`pk_inj`), and a left inverse `unpk` (`unpk_pk`, chosen classically, so no division or
  square root is computed);
- `cun`, the naturals onto the pairs, in order of their sum (`cun 0 = (0, 0)`, then each pair after the last), with
  `cpair` its inverse (`cun_cpair`, `cpair_cun`): a bijection, the one a datatype's codes are built from, each part at
  most the whole (`cun_fst_le`, `cun_snd_le`) so a value's fields have smaller codes;
- `tup q k i`, the i-th of k naturals packed in q by `tupk` (`tup_tupk`), at most q (`tup_le`).
-/

namespace Kern

/-! ### The pairing the encoding reads several arguments at -/

/-- `(a + b)² + b`: core/dsl.ts's argsKey of two arguments. -/
def pk (a b : Nat) : Nat := (a + b) * (a + b) + b

theorem sq_succ (s : Nat) : (s + 1) * (s + 1) = s * s + 2 * s + 1 := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega

theorem pk_lt {a b c d : Nat} (h : a + b < c + d) : pk a b < pk c d := by
  unfold pk
  have h1 : (a + b + 1) * (a + b + 1) ≤ (c + d) * (c + d) := Nat.mul_self_le_mul_self h
  have h2 := sq_succ (a + b)
  omega

theorem pk_inj {a b c d : Nat} (h : pk a b = pk c d) : a = c ∧ b = d := by
  have hs : a + b = c + d := by
    rcases Nat.lt_trichotomy (a + b) (c + d) with hl | he | hg
    · exact absurd h (Nat.ne_of_lt (pk_lt hl))
    · exact he
    · exact absurd h (Nat.ne_of_gt (pk_lt hg))
  unfold pk at h
  rw [hs] at h
  omega

/-- A left inverse of `pk`: the pair a natural is the pairing of, where it is one. -/
noncomputable def unpk (n : Nat) : Nat × Nat :=
  if h : ∃ p : Nat × Nat, pk p.1 p.2 = n then Classical.choose h else (0, 0)

theorem unpk_pk (a b : Nat) : unpk (pk a b) = (a, b) := by
  have h : ∃ p : Nat × Nat, pk p.1 p.2 = pk a b := ⟨(a, b), rfl⟩
  unfold unpk
  rw [dif_pos h]
  have ⟨h1, h2⟩ := pk_inj (Classical.choose_spec h)
  exact Prod.ext h1 h2

@[simp] theorem unpk_fst (a b : Nat) : (unpk ((a + b) * (a + b) + b)).1 = a := by
  have := unpk_pk a b; unfold pk at this; rw [this]
@[simp] theorem unpk_snd (a b : Nat) : (unpk ((a + b) * (a + b) + b)).2 = b := by
  have := unpk_pk a b; unfold pk at this; rw [this]

/-! ### A bijection between the naturals and the pairs -/

/-- The naturals onto the pairs, in order of their sum: 0 is (0, 0), and each next natural the pair after. -/
def cun : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 => match cun n with
    | (0, b) => (b + 1, 0)
    | (a + 1, b) => (a, b + 1)

/-- 0 + 1 + … + s. -/
def tri : Nat → Nat
  | 0 => 0
  | s + 1 => tri s + s + 1

/-- `cun`'s inverse. -/
def cpair (a b : Nat) : Nat := tri (a + b) + b

theorem le_tri : ∀ s, s ≤ tri s
  | 0 => Nat.le_refl 0
  | s + 1 => by have := le_tri s; simp only [tri]; omega

theorem cpair_cun : ∀ n, cpair (cun n).1 (cun n).2 = n
  | 0 => rfl
  | n + 1 => by
    have ih := cpair_cun n
    simp only [cun]
    split
    · rename_i b h
      rw [h] at ih
      simp only [cpair, Nat.zero_add] at ih ⊢
      simp only [Nat.add_zero, tri]
      omega
    · rename_i a b h
      rw [h] at ih
      simp only [cpair] at ih ⊢
      have e : a + (b + 1) = (a + 1 + b) := by omega
      rw [e]
      omega

theorem cun_tri : ∀ s b, b ≤ s → cun (tri s + b) = (s - b, b)
  | 0, 0, _ => rfl
  | 0, _ + 1, h => absurd h (by omega)
  | s + 1, 0, _ => by
    have ih := cun_tri s s (Nat.le_refl s)
    have e : tri (s + 1) + 0 = (tri s + s) + 1 := by simp only [tri]; omega
    rw [e]
    simp only [cun, ih, Nat.sub_self, Nat.sub_zero]
  | s + 1, b + 1, h => by
    have ih := cun_tri (s + 1) b (by omega)
    have e : tri (s + 1) + (b + 1) = (tri (s + 1) + b) + 1 := by omega
    rw [e]
    simp only [cun, ih]
    have e2 : s + 1 - b = (s - b) + 1 := by omega
    rw [e2]
    simp only
    have e3 : s + 1 - (b + 1) = s - b := by omega
    rw [e3]

theorem cun_cpair (a b : Nat) : cun (cpair a b) = (a, b) := by
  unfold cpair
  rw [cun_tri (a + b) b (by omega)]
  simp

@[simp] theorem cun_cpair_fst (a b : Nat) : (cun (cpair a b)).1 = a := by rw [cun_cpair]
@[simp] theorem cun_cpair_snd (a b : Nat) : (cun (cpair a b)).2 = b := by rw [cun_cpair]
@[simp] theorem cpair_cun_eq (n : Nat) : cpair (cun n).1 (cun n).2 = n := cpair_cun n

theorem cpair_ge (a b : Nat) : a + b ≤ cpair a b := by
  unfold cpair; have := le_tri (a + b); omega

theorem cun_fst_le (n : Nat) : (cun n).1 ≤ n := by
  have h := cpair_ge (cun n).1 (cun n).2; rw [cpair_cun] at h; omega
theorem cun_snd_le (n : Nat) : (cun n).2 ≤ n := by
  have h := cpair_ge (cun n).1 (cun n).2; rw [cpair_cun] at h; omega

/-! ### Tuples of naturals -/

/-- The i-th of k naturals packed in q (`tupk`): the first is `(cun q).1`, the rest packed in `(cun q).2`, the last q
itself. -/
def tup (q : Nat) : Nat → Nat → Nat
  | 0, _ => q
  | 1, _ => q
  | _ + 2, 0 => (cun q).1
  | k + 2, i + 1 => tup (cun q).2 (k + 1) i

/-- Naturals packed by `cpair`, right-nested; one is itself. -/
def tupk : List Nat → Nat
  | [] => 0
  | [x] => x
  | x :: xs => cpair x (tupk xs)

theorem tup_le : ∀ (k i q : Nat), tup q k i ≤ q
  | 0, _, _ => Nat.le_refl _
  | 1, _, _ => Nat.le_refl _
  | _ + 2, 0, q => cun_fst_le q
  | k + 2, i + 1, q => Nat.le_trans (tup_le (k + 1) i (cun q).2) (cun_snd_le q)

@[simp] theorem tup_two_zero (k a q : Nat) : tup (cpair a q) (k + 2) 0 = a := by simp [tup]
@[simp] theorem tup_two_succ (k i a q : Nat) : tup (cpair a q) (k + 2) (i + 1) = tup q (k + 1) i := by simp [tup]
@[simp] theorem tup_one (q i : Nat) : tup q 1 i = q := rfl

end Kern

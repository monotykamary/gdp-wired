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
- `tup q k i`, the i-th of k naturals packed in q by `tupk` (`tup_tupk`), at most q (`tup_le`);
- `wf_fix_unique`: a definition by well-founded recursion has exactly one solution. core/data.ts takes a function whose
  recursion isn't structural once the kernel has proven that each of its calls lowers a measure (a lexicographic tuple
  of naturals, the order of the cyclic ranks, `lexLt`) under the path to the call; its body, read as a functional F of
  the function, then reads it only below the argument's measure, and such an F has one fixpoint. So the function's
  equation, a fact of its proofs, has a model (what they conclude isn't vacuous), and only one: the function as written.
  An export defines such a function with `termination_by` the same measure, `Lx` (a tuple, ordered by `lexLt`) where
  it has several components, and Lean checks the decrease again;
- `wf_fix_unique_ring`: the same for a ring of functions calling each other (mutual recursion), each with its own
  measure (all of one length): one functional over the ring's tuple of functions, reading each only below the measure
  of the argument it is called at. An export defines the ring in one `mutual` block, each function with `termination_by`
  its measure.
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

open Classical in
/-- A left inverse of `pk`: the pair a natural is the pairing of, where it is one. -/
noncomputable def unpk (n : Nat) : Nat × Nat :=
  if h : ∃ p : Nat × Nat, pk p.1 p.2 = n then Classical.choose h else (0, 0)

theorem unpk_pk (a b : Nat) : unpk (pk a b) = (a, b) := by
  have h : ∃ p : Nat × Nat, pk p.1 p.2 = pk a b := ⟨(a, b), rfl⟩
  unfold unpk
  split
  · rename_i h'
    have ⟨h1, h2⟩ := pk_inj (Classical.choose_spec h')
    exact Prod.ext h1 h2
  · exact absurd h ‹_›

@[simp] theorem unpk_fst (a b : Nat) : (unpk ((a + b) * (a + b) + b)).1 = a := by
  have := unpk_pk a b; unfold pk at this; rw [this]
@[simp] theorem unpk_snd (a b : Nat) : (unpk ((a + b) * (a + b) + b)).2 = b := by
  have := unpk_pk a b; unfold pk at this; rw [this]

-- The pairing with a 0 argument, as simp leaves it: (a + 0)² + 0 is a·a, (0 + b)² + b is b·b + b, and (0 + 0)² + 0 is 0.
@[simp] theorem unpk_sq_fst (a : Nat) : (unpk (a * a)).1 = a := by
  have := unpk_pk a 0; simp only [pk, Nat.add_zero] at this; rw [this]
@[simp] theorem unpk_sq_snd (a : Nat) : (unpk (a * a)).2 = 0 := by
  have := unpk_pk a 0; simp only [pk, Nat.add_zero] at this; rw [this]
@[simp] theorem unpk_sqb_fst (b : Nat) : (unpk (b * b + b)).1 = 0 := by
  have := unpk_pk 0 b; simp only [pk, Nat.zero_add] at this; rw [this]
@[simp] theorem unpk_sqb_snd (b : Nat) : (unpk (b * b + b)).2 = b := by
  have := unpk_pk 0 b; simp only [pk, Nat.zero_add] at this; rw [this]
@[simp] theorem unpk_zero : unpk 0 = (0, 0) := unpk_pk 0 0

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

theorem cpair_succ_left (b : Nat) : cpair (b + 1) 0 = cpair 0 b + 1 := by
  simp only [cpair, Nat.add_zero, Nat.zero_add, tri]

theorem cpair_succ_right (a b : Nat) : cpair a (b + 1) = cpair (a + 1) b + 1 := by
  simp only [cpair]
  have e : a + (b + 1) = a + 1 + b := by omega
  rw [e]; omega

theorem cpair_cun : ∀ n, cpair (cun n).1 (cun n).2 = n
  | 0 => rfl
  | n + 1 => by
    have ih := cpair_cun n
    rcases h : cun n with ⟨a, b⟩
    rw [h] at ih
    cases a with
    | zero => simp only [cun, h]; rw [cpair_succ_left]; simp only at ih; omega
    | succ a => simp only [cun, h]; rw [cpair_succ_right]; simp only at ih; omega

theorem cun_tri : ∀ s b, b ≤ s → cun (tri s + b) = (s - b, b)
  | 0, 0, _ => rfl
  | 0, _ + 1, h => absurd h (by omega)
  | s + 1, 0, _ => by
    have ih := cun_tri s s (Nat.le_refl s)
    have e : tri (s + 1) + 0 = (tri s + s) + 1 := by simp only [tri]; try omega
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
@[simp] theorem tupk_one (x : Nat) : tupk [x] = x := rfl
@[simp] theorem tupk_cons (x y : Nat) (ys : List Nat) : tupk (x :: y :: ys) = cpair x (tupk (y :: ys)) := rfl

/-! ### Definitions by well-founded recursion -/

/-- A functional that reads its function only at arguments of lower measure (lexicographic, as the cyclic ranks are
ordered) has exactly one fixpoint: a function satisfying `f x = F f x` at every argument, and every other one equal to
it. `F g x = F h x` wherever g and h agree below x's measure: a body whose calls (under the path the argument takes)
are each at a lower measure. -/
theorem wf_fix_unique {α β : Type} [Inhabited β] (μ : α → List Nat) (F : (α → β) → α → β)
    (hF : ∀ (g h : α → β) (x : α), (∀ y, lexLt (μ y) (μ x) → g y = h y) → F g x = F h x) :
    ∃ f : α → β, (∀ x, f x = F f x) ∧ ∀ f' : α → β, (∀ x, f' x = F f' x) → f' = f := by
  classical
  have wf : WellFounded (InvImage lexLt μ) := InvImage.wf μ lexLt_wf
  let G : (x : α) → ((y : α) → InvImage lexLt μ y x → β) → β :=
    fun x rec => F (fun y => if h : lexLt (μ y) (μ x) then rec y h else default) x
  have hfix : ∀ x, wf.fix G x = F (wf.fix G) x := by
    intro x
    rw [wf.fix_eq G x]
    apply hF
    intro y hy
    simp [hy]
  refine ⟨wf.fix G, hfix, fun f' hf' => funext fun x => ?_⟩
  exact wf.induction (C := fun x => f' x = wf.fix G x) x (fun x ih => by
    rw [hf' x, hfix x]
    exact hF f' (wf.fix G) x (fun y hy => ih y hy))

/-- A ring of functions calling each other (one per index i, each `α i → β i`), read as one functional F over the ring's
tuple, that reads each function of the ring only at arguments of lower measure than its own argument's (the measures
of the ring's functions, one per function, all of one length, compared by `lexLt`), has exactly one fixpoint: a tuple
satisfying `f i x = F f i x` for every function and argument, and every other tuple equal to it. core/data.ts takes a
ring that isn't structural recursion once the kernel has proven that each call within the ring, under its path, lowers
the callee's measure at the call's arguments below the caller's at its parameters: that is `hF`, each function's body
reading the ring's functions only at those calls. `wf_fix_unique` is the ring of one. -/
theorem wf_fix_unique_ring {ι : Type} {α β : ι → Type} [∀ i, Inhabited (β i)] (μ : (i : ι) → α i → List Nat)
    (F : ((i : ι) → α i → β i) → (i : ι) → α i → β i)
    (hF : ∀ (g h : (i : ι) → α i → β i) (i : ι) (x : α i),
      (∀ (j : ι) (y : α j), lexLt (μ j y) (μ i x) → g j y = h j y) → F g i x = F h i x) :
    ∃ f : (i : ι) → α i → β i, (∀ i x, f i x = F f i x) ∧
      ∀ f' : (i : ι) → α i → β i, (∀ i x, f' i x = F f' i x) → f' = f := by
  classical
  -- the ring's arguments as one type (a function's index and its argument), ordered by the measure there
  let m : (Σ i, α i) → List Nat := fun p => μ p.1 p.2
  have wf : WellFounded (InvImage lexLt m) := InvImage.wf m lexLt_wf
  let G : (p : Σ i, α i) → ((q : Σ i, α i) → InvImage lexLt m q p → β q.1) → β p.1 :=
    fun p rec => F (fun j y => if h : lexLt (μ j y) (μ p.1 p.2) then rec ⟨j, y⟩ h else default) p.1 p.2
  let f : (i : ι) → α i → β i := fun i x => wf.fix G ⟨i, x⟩
  have hfix : ∀ i x, f i x = F f i x := by
    intro i x
    show wf.fix G ⟨i, x⟩ = F f i x
    rw [wf.fix_eq G ⟨i, x⟩]
    apply hF
    intro j y hy
    simp [hy, f]
  refine ⟨f, hfix, fun f' hf' => ?_⟩
  have key : ∀ p : Σ i, α i, f' p.1 p.2 = f p.1 p.2 := fun p =>
    wf.induction (C := fun p => f' p.1 p.2 = f p.1 p.2) p (fun p ih => by
      rw [hf' p.1 p.2, hfix p.1 p.2]
      exact hF f' f p.1 p.2 (fun j y hy => ih ⟨j, y⟩ hy))
  funext i x
  exact key ⟨i, x⟩

/-- A measure of several components for `termination_by`: the tuple, ordered by `lexLt` (an export's measures all have
one length). -/
structure Lx where
  l : List Nat

instance : WellFoundedRelation Lx := ⟨fun a b => lexLt a.l b.l, InvImage.wf Lx.l lexLt_wf⟩

/-! ### Facts at their keys -/

/-- A condition's value as a natural is at most 1 (a function to `Bool` as the encoding reads it). -/
@[simp] theorem ite_one_zero_le (p : Prop) [Decidable p] : (if p then 1 else 0) ≤ 1 := by
  split <;> omega

/-- A fact read at its own keys reads the values given there. -/
theorem override_at (keys : List Nat) (i : Nat) (h : keys.contains i = true) (vals env : Nat → Nat) :
    override keys vals env i = vals i := by
  unfold override; rw [if_pos h]

end Kern

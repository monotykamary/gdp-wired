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
  its measure;
- `wf_fix_inv_unique_ring` (`wf_fix_inv_unique` its ring of one): nested recursion, a call of the ring in another's
  argument, so a body reads the ring at its own values. An invariant of each function (core/data.ts: how its value's
  size relates to an argument's) is proven with the decrease: each call lowers the measure and each body keeps the
  invariant, wherever the calls the body reads below the measure keep it. The fixpoint is unique and keeps it.
  research/termination/Nested.lean defines two such functions through it (Lean's `termination_by` can't read a call's
  value: core/data.ts's Lean export doesn't write these yet).
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

/-! ### A bijection between the naturals and the pairs

`cun`, `tri`, `cpair` and their inverse laws (`cun_cpair`, `cpair_cun`) are Kernel.lean's (a tuple key is a term there);
what a datatype's codes need beyond them is here. -/

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

theorem tup_le : ∀ (k i q : Nat), tup q k i ≤ q
  | 0, _, _ => Nat.le_refl _
  | 1, _, _ => Nat.le_refl _
  | _ + 2, 0, q => cun_fst_le q
  | k + 2, i + 1, q => Nat.le_trans (tup_le (k + 1) i (cun q).2) (cun_snd_le q)

@[simp] theorem tup_two_zero (k a q : Nat) : tup (cpair a q) (k + 2) 0 = a := by simp [tup]
@[simp] theorem tup_two_succ (k i a q : Nat) : tup (cpair a q) (k + 2) (i + 1) = tup q (k + 1) i := by simp [tup]
@[simp] theorem tup_one (q i : Nat) : tup q 1 i = q := rfl

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

/-- Nested recursion: a ring whose calls may sit in the arguments (or conditions) of others, so a body reads the ring at
values of the ring itself. A functional F such that, wherever g and h agree below x's measure and g keeps the invariant
I there (`I j y (g j y)`), F g and F h agree at x and F g keeps I at x, has exactly one fixpoint, and it keeps I
everywhere: the decrease and the invariant proven together, by well-founded induction on the measure. core/data.ts
takes such a ring once the kernel has proven, for each call within it (under its path, each call of the ring in its
argument or condition read as a value r with `lexLt (μ j a) (μ i x) → I j a r`), that it lowers the callee's measure
below the caller's, and that each body, its calls read the same way, keeps its function's invariant: that is `hF`.
`wf_fix_unique_ring` is the case I = True. -/
theorem wf_fix_inv_unique_ring {ι : Type} {α β : ι → Type} [∀ i, Inhabited (β i)] (μ : (i : ι) → α i → List Nat)
    (I : (i : ι) → α i → β i → Prop) (F : ((i : ι) → α i → β i) → (i : ι) → α i → β i)
    (hF : ∀ (g h : (i : ι) → α i → β i) (i : ι) (x : α i),
      (∀ (j : ι) (y : α j), lexLt (μ j y) (μ i x) → g j y = h j y ∧ I j y (g j y)) →
      F g i x = F h i x ∧ I i x (F g i x)) :
    ∃ f : (i : ι) → α i → β i, (∀ i x, f i x = F f i x ∧ I i x (f i x)) ∧
      ∀ f' : (i : ι) → α i → β i, (∀ i x, f' i x = F f' i x) → f' = f := by
  classical
  let m : (Σ i, α i) → List Nat := fun p => μ p.1 p.2
  have wf : WellFounded (InvImage lexLt m) := InvImage.wf m lexLt_wf
  let G : (p : Σ i, α i) → ((q : Σ i, α i) → InvImage lexLt m q p → β q.1) → β p.1 :=
    fun p rec => F (fun j y => if h : lexLt (μ j y) (μ p.1 p.2) then rec ⟨j, y⟩ h else default) p.1 p.2
  let f : (i : ι) → α i → β i := fun i x => wf.fix G ⟨i, x⟩
  -- the equation and the invariant at once, by induction on the measure
  have hfix : ∀ p : Σ i, α i, f p.1 p.2 = F f p.1 p.2 ∧ I p.1 p.2 (f p.1 p.2) := fun p =>
    wf.induction (C := fun p => f p.1 p.2 = F f p.1 p.2 ∧ I p.1 p.2 (f p.1 p.2)) p (fun p ih => by
      have e : f p.1 p.2 = F (fun j y => if lexLt (μ j y) (μ p.1 p.2) then f j y else default) p.1 p.2 := by
        show wf.fix G p = _
        rw [wf.fix_eq G p]
        rfl
      have k := hF (fun j y => if lexLt (μ j y) (μ p.1 p.2) then f j y else default) f p.1 p.2
        (fun j y hy => by rw [if_pos hy]; exact ⟨rfl, (ih ⟨j, y⟩ hy).2⟩)
      rw [e]
      exact ⟨k.1, k.2⟩)
  refine ⟨f, fun i x => hfix ⟨i, x⟩, fun f' hf' => ?_⟩
  have key : ∀ p : Σ i, α i, f' p.1 p.2 = f p.1 p.2 := fun p =>
    wf.induction (C := fun p => f' p.1 p.2 = f p.1 p.2) p (fun p ih => by
      rw [hf' p.1 p.2, (hfix p).1]
      exact (hF f f' p.1 p.2 (fun j y hy => ⟨(ih ⟨j, y⟩ hy).symm, (hfix ⟨j, y⟩).2⟩)).1.symm)
  funext i x
  exact key ⟨i, x⟩

/-- `wf_fix_inv_unique_ring`'s ring of one: a nested recursive function (McCarthy's `m(m(x + 11))`, a sort that sorts
the result of sorting) with its invariant. -/
theorem wf_fix_inv_unique {α β : Type} [Inhabited β] (μ : α → List Nat) (I : α → β → Prop) (F : (α → β) → α → β)
    (hF : ∀ (g h : α → β) (x : α), (∀ y, lexLt (μ y) (μ x) → g y = h y ∧ I y (g y)) → F g x = F h x ∧ I x (F g x)) :
    ∃ f : α → β, (∀ x, f x = F f x ∧ I x (f x)) ∧ ∀ f' : α → β, (∀ x, f' x = F f' x) → f' = f := by
  obtain ⟨f, hf, hu⟩ := wf_fix_inv_unique_ring (ι := Unit) (α := fun _ => α) (β := fun _ => β) (fun _ => μ) (fun _ => I)
    (fun g _ x => F (g ()) x) (fun g h _ x hy => hF (g ()) (h ()) x (fun y hy' => hy () y hy'))
  refine ⟨f (), fun x => hf () x, fun f' hf' => ?_⟩
  have := hu (fun _ => f') (fun _ x => hf' x)
  exact congrFun this ()

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

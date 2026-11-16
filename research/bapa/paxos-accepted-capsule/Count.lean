import Kernel

/-!
Count: quorum facts as a certificate kind, proven sound. Lean 4.34.0, core only; on top of `Kernel.lean` alone.

**The lemma.** Finite sums over the keys below a bound (`sumBelow f n` = f 0 + … + f (n − 1)) are monotone and linear,
so a pointwise inequality sums: if g sums below f over the keys below n, some key below n has g below f there
(`exists_lt_of_sumBelow_lt`). Its corollaries are the quorum facts, for sets of keys below n (`card`):
- `pigeonhole`: A, B ⊆ S and |A| + |B| > |S| give a key in A ∩ B;
- `majorities_meet`: two majorities of S (2|A| > |S|, 2|B| > |S|) meet;
- `quorums_meet_outside`: A, B ⊆ S and |A| + |B| > |S| + |F| give a key in A ∩ B outside F (thresholds: two sets of
  f + 1 out of 2f + 1, or two sets of n − t when n > 3t, meet in a process outside the t faulty ones).

**The certificate kind** (kernel.ts's `checkCounted`, its twin). A counted goal is a goal (hypotheses over naturals and
maps, as `Kernel.lean`'s) and counts: each a variable `v` that names Σ_{k < below} body(k), the body read with its key
variable `key` at k (a 0/1 body is a set's size). A certificate is a list of instances and a tree. An instance names a
fresh witness variable `wit`, a bound `below` every count it reads shares, integer coefficients on counts (`terms`) and
on the constant 1 (`unit`). With P the positive parts and N the negative parts (posP z = max z 0, negP z = max (−z) 0):

    countHyp = ( P·counts + P(unit)·below  ≤  N·counts + N(unit)·below )
            ∨ ( wit < below  ∧  N·bodies(wit) + N(unit)  <  P·bodies(wit) + P(unit) )

which is the lemma read at one key: either the combination's sum is not positive, or `wit` is a key below the bound
where its pointwise value is. Lean builds the instances' hypotheses itself (`countHyps`), checks each witness is fresh
(`countedOk`) and checks the tree against the goal's hypotheses followed by them (`checkGoal`). `counted_sound`: an
accepted counted goal's hypotheses hold at no naturals and maps where every count is its sum.

Why this shape is the smallest that covers the class: the whole of a Venn-region (BAPA) certificate is a linear
combination of set sizes whose pointwise value is never positive, so one instance (its Farkas coefficients on the
counts) plus a refutation at the witness key replaces the region variables: the case split on which sets hold the
witness is the tree's, over the cells it reads, as the kernel already splits. Majorities (+1, +1 on two counts, −1 on
the set's), f + 1 of 2f + 1 (the same) and more than 2/3 with faulty processes (+1, +1, −1 on S, −1 on F) are each one
instance; a count of a compound body (A ∩ B, say) gives the numeric forms (|A ∩ B| ≥ |A| + |B| − |S|).
-/

namespace Kern

/-! Finite sums below a bound -/

def sumBelow (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumBelow f n + f n

theorem sumBelow_mono {f g : Nat → Nat} (n : Nat) (h : ∀ k, k < n → f k ≤ g k) : sumBelow f n ≤ sumBelow g n := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih =>
    simp only [sumBelow]
    have h1 := ih (fun k hk => h k (by omega))
    have h2 := h n (by omega)
    omega

theorem sumBelow_add (f g : Nat → Nat) (n : Nat) : sumBelow (fun k => f k + g k) n = sumBelow f n + sumBelow g n := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih => simp only [sumBelow, ih]; omega

theorem sumBelow_mul (c : Nat) (f : Nat → Nat) (n : Nat) : sumBelow (fun k => c * f k) n = c * sumBelow f n := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih => simp only [sumBelow, ih, Nat.mul_add]

theorem sumBelow_const (d n : Nat) : sumBelow (fun _ => d) n = d * n := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih => simp only [sumBelow, ih, Nat.mul_add, Nat.mul_one]

theorem sumBelow_congr {f g : Nat → Nat} (n : Nat) (h : ∀ k, k < n → f k = g k) : sumBelow f n = sumBelow g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumBelow, ih (fun k hk => h k (by omega)), h n (by omega)]

theorem sumBelow_zero_fn (n : Nat) : sumBelow (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumBelow, ih]

/-- A pointwise inequality, summed: if g sums below f over the keys below n, some key below n has g below f. -/
theorem exists_lt_of_sumBelow_lt {f g : Nat → Nat} {n : Nat} (h : sumBelow g n < sumBelow f n) : ∃ k, k < n ∧ g k < f k := by
  apply Classical.byContradiction
  intro hno
  have hle : ∀ k, k < n → f k ≤ g k := fun k hk => Nat.le_of_not_lt (fun hlt => hno ⟨k, hk, hlt⟩)
  have := sumBelow_mono n hle
  omega

/-! Sets of keys below a bound, and the quorum facts -/

-- The number of keys below n where p holds.
def card (p : Nat → Bool) (n : Nat) : Nat := sumBelow (fun k => if p k then 1 else 0) n

/-- The pigeonhole: two subsets of S whose sizes add up to more than S's meet. -/
theorem pigeonhole {a b s : Nat → Bool} {n : Nat} (ha : ∀ k, k < n → a k = true → s k = true)
    (hb : ∀ k, k < n → b k = true → s k = true) (h : card s n < card a n + card b n) :
    ∃ k, k < n ∧ a k = true ∧ b k = true := by
  unfold card at h
  rw [← sumBelow_add] at h
  obtain ⟨k, hk, hlt⟩ := exists_lt_of_sumBelow_lt h
  have h1 := ha k hk
  have h2 := hb k hk
  refine ⟨k, hk, ?_⟩
  cases hak : a k <;> cases hbk : b k <;> cases hsk : s k <;> simp_all

/-- Two majorities of S meet. -/
theorem majorities_meet {a b s : Nat → Bool} {n : Nat} (ha : ∀ k, k < n → a k = true → s k = true)
    (hb : ∀ k, k < n → b k = true → s k = true) (h1 : card s n < 2 * card a n) (h2 : card s n < 2 * card b n) :
    ∃ k, k < n ∧ a k = true ∧ b k = true :=
  pigeonhole ha hb (by omega)

/-- Thresholds: two subsets of S whose sizes add up to more than |S| + |F| meet outside F (f + 1 of 2f + 1 with F
empty; n − t of n with n > 3t and at most t faulty). -/
theorem quorums_meet_outside {a b s f : Nat → Bool} {n : Nat} (ha : ∀ k, k < n → a k = true → s k = true)
    (hb : ∀ k, k < n → b k = true → s k = true) (h : card s n + card f n < card a n + card b n) :
    ∃ k, k < n ∧ a k = true ∧ b k = true ∧ f k = false := by
  unfold card at h
  rw [← sumBelow_add, ← sumBelow_add] at h
  obtain ⟨k, hk, hlt⟩ := exists_lt_of_sumBelow_lt h
  have h1 := ha k hk
  have h2 := hb k hk
  refine ⟨k, hk, ?_⟩
  cases hak : a k <;> cases hbk : b k <;> cases hsk : s k <;> cases hfk : f k <;> simp_all

/-! The certificate kind: counts in a goal -/

-- A count: the variable v names the sum of `body` over the keys below `below`, `body` read with `key` at each key.
structure Count where
  v : Nat
  key : Nat
  below : E
  body : E

-- What a count means at an environment.
def Count.Holds (c : Count) (ρ : Nat → Nat) (M : Nat → Nat → Nat) : Prop :=
  ρ c.v = sumBelow (fun k => evalE (upd ρ c.key k) M c.body) (evalE ρ M c.below)

-- An instance of the lemma: a fresh witness, the bound its counts share, a coefficient per count (named by its
-- variable) and one on the constant 1.
structure CInst where
  wit : Nat
  below : E
  terms : List (Int × Nat)
  unit : Int

-- A counted goal: its hypotheses, and the counts they read.
structure CGoal where
  hyps : List C
  counts : List Count

def findCount (cs : List Count) (v : Nat) : Option Count := lookup (fun c => c.v == v) cs

-- Each term's count (the first with its variable), when every term names one whose bound is the instance's.
def resolve (cs : List Count) (B : E) : List (Int × Nat) → Option (List (Int × Count))
  | [] => some []
  | t :: ts => match findCount cs t.2 with
    | none => none
    | some c => if beqE c.below B then (resolve cs B ts).map (fun rs => (t.1, c) :: rs) else none

-- A sum of terms, right-nested from 0.
def sumE : List E → E
  | [] => .const 0
  | e :: es => .add e (sumE es)

def posP (z : Int) : Nat := z.toNat
def negP (z : Int) : Nat := (-z).toNat

-- One side of an instance: each count read by `rd` times its coefficient's part, then the unit's part times `one`.
def side (part : Int → Nat) (rd : Count → E) (one : E) (u : Int) (rs : List (Int × Count)) : E :=
  .add (sumE (rs.map fun r => .mul (part r.1) (rd r.2))) (.mul (part u) one)

-- A count read as its variable, and its body read at the witness.
def atCount (c : Count) : E := .var c.v
def atWit (w : Nat) (c : Count) : E := substE [(c.key, .var w)] c.body

-- The instance's hypothesis: the combination's sum is not positive, or the witness is a key below the bound where the
-- combination's value is.
def countHyp (cs : List Count) (i : CInst) : Option C :=
  (resolve cs i.below i.terms).map fun rs =>
    .or (.le (side posP atCount i.below i.unit rs) (side negP atCount i.below i.unit rs))
      (.and (.lt (.var i.wit) i.below)
        (.lt (side negP (atWit i.wit) (.const 1) i.unit rs) (side posP (atWit i.wit) (.const 1) i.unit rs)))

def countHyps (cs : List Count) : List CInst → Option (List C)
  | [] => some []
  | i :: is => match countHyp cs i with
    | none => none
    | some h => (countHyps cs is).map (h :: ·)

def cDistinct : List Nat → Bool
  | [] => true
  | a :: as => !as.contains a && cDistinct as

-- A witness is fresh: no hypothesis reads it, no count names it or reads it (in its bound or its body), and no
-- instance's bound reads it.
def witFresh (hyps : List C) (cs : List Count) (is : List CInst) (w : Nat) : Bool :=
  hyps.all (fun h => !occC w h) && cs.all (fun c => c.v != w && !occE w c.below && !occE w c.body) && is.all (fun j => !occE w j.below)

def countedOk (hyps : List C) (cs : List Count) (is : List CInst) : Bool :=
  cDistinct (is.map (·.wit)) && is.all (fun i => witFresh hyps cs is i.wit)

/-! Conditional lemma cuts. A lemma shares the containing goal's table and may select only its hypotheses.
Its proof is an old-language tree, checked without any lemma assumptions. This rules out circular citations. -/

section LemmaCuts
set_option autoImplicit false

structure CutLemma where
  when : List Cert.Row
  cut : Cert.Row
  tree : Tree
  slice : Option (List Nat) := none

def lemmaSlice (hyps : List C) : List Nat → Option (List C)
  | [] => some []
  | i :: is => match hyps[i]?, lemmaSlice hyps is with
    | some h, some hs => some (h :: hs)
    | _, _ => none

def lemmaHyps (hyps : List C) (l : CutLemma) : Option (List C) :=
  match l.slice with
  | none => some hyps
  | some is => lemmaSlice hyps is

def checkLemma (tab : List VDef) (hyps : List C) (l : CutLemma) : Bool :=
  match lemmaHyps hyps l with
  | some hs => checkT tab hs ((l.cut, false) :: l.when.map (fun w => (w, true))) l.tree
  | none => false

-- Eligibility reads only the original split path, never the cuts being made available.
def lemmaActive (path : Path) (l : CutLemma) : Bool :=
  l.when.all (fun w => dec path w == some true)

def lemmaPath (lemmas : List CutLemma) (path : Path) : Path :=
  (lemmas.filter (lemmaActive path)).map (fun l => (l.cut, true)) ++ path

def checkTLemmas (tab : List VDef) (hyps : List C) (lemmas : List CutLemma) : Path → Tree → Bool
  | path, .split l y n => checkTLemmas tab hyps lemmas ((l, true) :: path) y && checkTLemmas tab hyps lemmas ((l, false) :: path) n
  | path, t => checkT tab hyps (lemmaPath lemmas path) t

def checkGoalLemmas (g : Goal) (t : Tree) (lemmas : List CutLemma) : Bool :=
  wfTab 0 g.tab && lemmas.all (checkLemma g.tab g.hyps) && checkTLemmas g.tab g.hyps lemmas [] t

@[simp] theorem lemmaPath_nil (path : Path) : lemmaPath [] path = path := rfl

@[simp] theorem checkTLemmas_nil (tab : List VDef) (hyps : List C) (t : Tree) (path : Path) :
    checkTLemmas tab hyps [] path t = checkT tab hyps path t := by
  induction t generalizing path with
  | split l y n ihy ihn => simp only [checkTLemmas, checkT, ihy, ihn]
  | leaf rows steps eqs prods => rfl
  | leafAt rows steps eqs prods => rfl
  | leafSq rows sqs steps eqs prods => rfl

@[simp] theorem checkGoalLemmas_nil (g : Goal) (t : Tree) : checkGoalLemmas g t [] = checkGoal g t := by
  simp [checkGoalLemmas, checkGoal]

theorem lemmaSlice_sub {hyps : List C} : ∀ {is : List Nat} {hs : List C},
    lemmaSlice hyps is = some hs → ∀ h ∈ hs, h ∈ hyps
  | [], hs, he => by simp only [lemmaSlice, Option.some.injEq] at he; subst he; simp
  | i :: is, hs, he => by
    cases hi : hyps[i]? with
    | none => simp [lemmaSlice, hi] at he
    | some c =>
      cases ht : lemmaSlice hyps is with
      | none => simp [lemmaSlice, hi, ht] at he
      | some cs =>
        simp only [lemmaSlice, hi, ht, Option.some.injEq] at he
        subst he
        intro h hh
        rcases List.mem_cons.mp hh with rfl | hh
        · exact List.mem_of_getElem? hi
        · exact lemmaSlice_sub ht h hh

theorem lemmaHyps_sub {hyps hs : List C} {l : CutLemma} (he : lemmaHyps hyps l = some hs) :
    ∀ h ∈ hs, h ∈ hyps := by
  cases sl : l.slice with
  | none => simp only [lemmaHyps, sl, Option.some.injEq] at he; subst he; exact fun _ hh => hh
  | some is => exact lemmaSlice_sub (by simpa only [lemmaHyps, sl] using he)

def CutHolds (l : CutLemma) (x : List Int) : Prop :=
  (∀ w ∈ l.when, Cert.eval w x ≤ 0) → Cert.eval l.cut x ≤ 0

/-- A checked lemma proves its cut under exactly its declared linear conditions. -/
theorem lemma_sound {tab : List VDef} {hyps : List C} {env : Nat → Nat} {maps : Nat → Nat → Nat} {x : List Int}
    (hM : Model tab env maps x) (hH : ∀ c ∈ hyps, evalC env maps c = true)
    {l : CutLemma} (hck : checkLemma tab hyps l = true) : CutHolds l x := by
  intro hw
  apply Int.not_lt.mp
  intro hc
  cases hs : lemmaHyps hyps l with
  | none => simp [checkLemma, hs] at hck
  | some cs =>
    simp only [checkLemma, hs] at hck
    have hp : PathHolds ((l.cut, false) :: l.when.map (fun w => (w, true))) x := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · have hn : ¬ Cert.eval l.cut x ≤ 0 := by omega
        simpa using hn
      · obtain ⟨w, hwm, rfl⟩ := List.mem_map.mp ha
        simpa using hw w hwm
    exact checkT_sound hM (fun c hc => hH c (lemmaHyps_sub hs c hc)) l.tree _ hp hck

theorem lemmaPath_holds {lemmas : List CutLemma} {path : Path} {x : List Int}
    (hP : PathHolds path x) (hL : ∀ l ∈ lemmas, CutHolds l x) : PathHolds (lemmaPath lemmas path) x := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    obtain ⟨hlm, hactive⟩ := List.mem_filter.mp hl
    have hc : Cert.eval l.cut x ≤ 0 := hL l hlm (fun w hw => by
      have hd : dec path w = some true := by
        simpa only [lemmaActive, List.all_eq_true, beq_iff_eq] using (List.all_eq_true.mp hactive w hw)
      have := dec_sound hP hd
      simpa using this)
    simpa using hc
  · exact hP a ha

theorem checkTLemmas_sound {tab : List VDef} {hyps : List C} {env : Nat → Nat} {maps : Nat → Nat → Nat} {x : List Int}
    (hM : Model tab env maps x) (hH : ∀ c ∈ hyps, evalC env maps c = true)
    {lemmas : List CutLemma} (hL : ∀ l ∈ lemmas, CutHolds l x) :
    ∀ (t : Tree) (path : Path), PathHolds path x → checkTLemmas tab hyps lemmas path t = true → False
  | .split l y n, path, hP, h => by
    simp only [checkTLemmas, Bool.and_eq_true] at h
    by_cases hl : Cert.eval l x ≤ 0
    · refine checkTLemmas_sound hM hH hL y _ ?_ h.1
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simpa using hl
      · exact hP a ha
    · refine checkTLemmas_sound hM hH hL n _ ?_ h.2
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simpa using hl
      · exact hP a ha
  | .leaf rows steps eqs prods, path, hP, h =>
    checkT_sound hM hH _ _ (lemmaPath_holds hP hL) h
  | .leafAt rows steps eqs prods, path, hP, h =>
    checkT_sound hM hH _ _ (lemmaPath_holds hP hL) h
  | .leafSq rows sqs steps eqs prods, path, hP, h =>
    checkT_sound hM hH _ _ (lemmaPath_holds hP hL) h

/-- The extended goal checker has the original unsatisfiability conclusion. -/
theorem goalLemmas_sound (g : Goal) (t : Tree) (lemmas : List CutLemma)
    (h : checkGoalLemmas g t lemmas = true) (env : Nat → Nat) (maps : Nat → Nat → Nat) :
    ¬ ∀ c ∈ g.hyps, evalC env maps c = true := by
  intro hH
  simp only [checkGoalLemmas, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hw, hl⟩, ht⟩ := h
  have hv := build_valid env maps g.tab [] [] ⟨rfl, by simp, by simp⟩ (by simpa using hw)
  simp only [List.nil_append] at hv
  have hM := model_of_valid hv
  exact checkTLemmas_sound hM hH (fun l hm => lemma_sound hM hH (hl l hm)) t [] (by simp [PathHolds]) ht

end LemmaCuts

/-! Conditional count frames (MLDR-DESIGN.md Section 15.7). A frame cut names two counts of the goal by their
variables, a post count and its pre count, and linear conditions `when` over the goal's table. It is accepted when,
with every `if` whose condition reads no count key and is decided under `when` resolved (`simpE`), the two counts have
the same key, bound and body. No tree is checked: the two sums are equal because their bounds and summands are
(`sumBelow_congr`). Where a leaf's original split path decides every condition, the two rows `post − pre ≤ 0` and
`pre − post ≤ 0` are available to it, as a lemma cut's row is. Nothing else changes: with no frames the checkers
below are the lemma-cut checkers (`checkGoalFrames_nil`). -/

section FrameCuts
set_option autoImplicit false

structure FrameCut where
  when : List Cert.Row
  post : Nat
  pre : Nat

/-! Section 17 (MLDR-DESIGN.md): the simplifier decides conditions that read the key from their key-free parts, prunes
decided conjuncts and disjuncts, and folds `(if C then 1 else 0) = 1` to `C`, so a step's write tree substituted into a
count's body collapses to the pre body where the step does not write the map. -/

-- A term that only rises with any variable: variables, constants, sums, scalings, products, minima, maxima.
def monoE : E → Bool
  | .var _ => true
  | .const _ => true
  | .add a b => monoE a && monoE b
  | .mul _ a => monoE a
  | .min a b => monoE a && monoE b
  | .max a b => monoE a && monoE b
  | .prod a b => monoE a && monoE b
  | _ => false

-- The variable `k` replaced by 0.
def zeroK (k : Nat) : E → E
  | .var i => if i = k then .const 0 else .var i
  | .const n => .const n
  | .add a b => .add (zeroK k a) (zeroK k b)
  | .sub a b => .sub (zeroK k a) (zeroK k b)
  | .mul m a => .mul m (zeroK k a)
  | .min a b => .min (zeroK k a) (zeroK k b)
  | .max a b => .max (zeroK k a) (zeroK k b)
  | .prod a b => .prod (zeroK k a) (zeroK k b)
  | .ite c t f => .ite c (zeroK k t) (zeroK k f)
  | .get m key => .get m (zeroK k key)
  | .tup a b => .tup (zeroK k a) (zeroK k b)
  | .proj j a => .proj j (zeroK k a)

theorem occE_zeroK (k : Nat) : (e : E) → monoE e = true → occE k (zeroK k e) = false
  | .var i, _ => by simp only [zeroK]; split <;> simp [occE, *]
  | .const _, _ => by simp [zeroK, occE]
  | .add a b, h => by
    simp only [monoE, Bool.and_eq_true] at h
    simp [zeroK, occE, occE_zeroK k a h.1, occE_zeroK k b h.2]
  | .mul _ a, h => by simp only [monoE] at h; simp [zeroK, occE, occE_zeroK k a h]
  | .min a b, h => by
    simp only [monoE, Bool.and_eq_true] at h
    simp [zeroK, occE, occE_zeroK k a h.1, occE_zeroK k b h.2]
  | .max a b, h => by
    simp only [monoE, Bool.and_eq_true] at h
    simp [zeroK, occE, occE_zeroK k a h.1, occE_zeroK k b h.2]
  | .prod a b, h => by
    simp only [monoE, Bool.and_eq_true] at h
    simp [zeroK, occE, occE_zeroK k a h.1, occE_zeroK k b h.2]
  | .sub _ _, h => by simp [monoE] at h
  | .ite _ _ _, h => by simp [monoE] at h
  | .get _ _, h => by simp [monoE] at h
  | .tup _ _, h => by simp [monoE] at h
  | .proj _ _, h => by simp [monoE] at h

theorem zeroK_eval (ρ : Nat → Nat) (M : Nat → Nat → Nat) (k : Nat) :
    (e : E) → monoE e = true → evalE ρ M (zeroK k e) = evalE (upd ρ k 0) M e
  | .var i, _ => by simp only [zeroK]; split <;> simp_all [evalE, upd]
  | .const _, _ => rfl
  | .add a b, h => by
    simp only [monoE, Bool.and_eq_true] at h
    simp only [zeroK, evalE, zeroK_eval ρ M k a h.1, zeroK_eval ρ M k b h.2]
  | .mul m a, h => by simp only [monoE] at h; simp only [zeroK, evalE, zeroK_eval ρ M k a h]
  | .min a b, h => by
    simp only [monoE, Bool.and_eq_true] at h
    simp only [zeroK, evalE, zeroK_eval ρ M k a h.1, zeroK_eval ρ M k b h.2]
  | .max a b, h => by
    simp only [monoE, Bool.and_eq_true] at h
    simp only [zeroK, evalE, zeroK_eval ρ M k a h.1, zeroK_eval ρ M k b h.2]
  | .prod a b, h => by
    simp only [monoE, Bool.and_eq_true] at h
    simp only [zeroK, evalE, zeroK_eval ρ M k a h.1, zeroK_eval ρ M k b h.2]
  | .sub _ _, h => by simp [monoE] at h
  | .ite _ _ _, h => by simp [monoE] at h
  | .get _ _, h => by simp [monoE] at h
  | .tup _ _, h => by simp [monoE] at h
  | .proj _ _, h => by simp [monoE] at h

theorem monoE_ge (ρ : Nat → Nat) (M : Nat → Nat → Nat) (k : Nat) :
    (e : E) → monoE e = true → evalE (upd ρ k 0) M e ≤ evalE ρ M e
  | .var i, _ => by simp only [evalE, upd]; split <;> simp
  | .const _, _ => Nat.le_refl _
  | .add a b, h => by
    simp only [monoE, Bool.and_eq_true] at h
    simp only [evalE]; exact Nat.add_le_add (monoE_ge ρ M k a h.1) (monoE_ge ρ M k b h.2)
  | .mul m a, h => by
    simp only [monoE] at h
    simp only [evalE]; exact Nat.mul_le_mul (Nat.le_refl m) (monoE_ge ρ M k a h)
  | .min a b, h => by
    simp only [monoE, Bool.and_eq_true] at h
    simp only [evalE]
    have ha := monoE_ge ρ M k a h.1; have hb := monoE_ge ρ M k b h.2; omega
  | .max a b, h => by
    simp only [monoE, Bool.and_eq_true] at h
    simp only [evalE]
    have ha := monoE_ge ρ M k a h.1; have hb := monoE_ge ρ M k b h.2; omega
  | .prod a b, h => by
    simp only [monoE, Bool.and_eq_true] at h
    simp only [evalE]; exact Nat.mul_le_mul (monoE_ge ρ M k a h.1) (monoE_ge ρ M k b h.2)
  | .sub _ _, h => by simp [monoE] at h
  | .ite _ _ _, h => by simp [monoE] at h
  | .get _ _, h => by simp [monoE] at h
  | .tup _ _, h => by simp [monoE] at h
  | .proj _ _, h => by simp [monoE] at h

-- An atom reading the key, decided for every value of the key from its key-free instance at 0: with the key only on
-- the left and the left rising with it, false at 0 is false everywhere; with the key only on the right, true at 0 is
-- true everywhere. Anything else is undecided.
def atomK (tab : List VDef) (path : Path) (k : Nat) : C → Option Bool
  | .le a b =>
    if occE k a && !occE k b && monoE a then
      (match truth tab path (.le (zeroK k a) b) with | some false => some false | _ => none)
    else if !occE k a && occE k b && monoE b then
      (match truth tab path (.le a (zeroK k b)) with | some true => some true | _ => none)
    else none
  | .lt a b =>
    if occE k a && !occE k b && monoE a then
      (match truth tab path (.lt (zeroK k a) b) with | some false => some false | _ => none)
    else if !occE k a && occE k b && monoE b then
      (match truth tab path (.lt a (zeroK k b)) with | some true => some true | _ => none)
    else none
  | _ => none

-- A condition decided for every value of the key: atoms reading no key by `truth`, atoms reading it by `atomK`,
-- `and`, `or` and `not` three-valued.
def truthK (tab : List VDef) (path : Path) (k : Nat) : C → Option Bool
  | .le a b => if occC k (.le a b) then atomK tab path k (.le a b) else truth tab path (.le a b)
  | .lt a b => if occC k (.lt a b) then atomK tab path k (.lt a b) else truth tab path (.lt a b)
  | .eq a b => if occC k (.eq a b) then
      (match atomK tab path k (.le a b), atomK tab path k (.le b a) with
       | some false, _ => some false
       | _, some false => some false
       | _, _ => none)
    else truth tab path (.eq a b)
  | .and a b => match truthK tab path k a, truthK tab path k b with
    | some false, _ => some false
    | _, some false => some false
    | some true, some true => some true
    | _, _ => none
  | .or a b => match truthK tab path k a, truthK tab path k b with
    | some true, _ => some true
    | _, some true => some true
    | some false, some false => some false
    | _, _ => none
  | .not a => match truthK tab path k a with
    | some b => some (!b)
    | none => none

theorem atomK_sound {tab : List VDef} {env : Nat → Nat} {maps : Nat → Nat → Nat} {x : List Int} {path : Path}
    (hM : Model tab env maps x) (hP : PathHolds path x) (k : Nat) (env' : Nat → Nat) (hk : ∀ i, i ≠ k → env' i = env i) :
    (c : C) → (b : Bool) → atomK tab path k c = some b → evalC env' maps c = b
  | .le a b', r, h => by
    simp only [atomK] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      obtain ⟨⟨hoa, hob⟩, hma⟩ := hc
      split at h
      · rename_i hT
        simp only [Option.some.injEq] at h; subst h
        have ht := truth_sound hM hP _ false hT
        have hcg : evalC env maps (.le (zeroK k a) b') = evalC env' maps (.le (zeroK k a) b') := by
          apply congrC
          intro i hi
          by_cases hik : i = k
          · subst hik; simp [occC, occE_zeroK i a hma, hob] at hi
          · exact (hk i hik).symm
        rw [hcg] at ht
        simp only [evalC, decide_eq_false_iff_not, Nat.not_le] at ht ⊢
        have h0 := zeroK_eval env' maps k a hma
        have hge := monoE_ge env' maps k a hma
        omega
      · simp at h
    · split at h
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        obtain ⟨⟨hoa, hob⟩, hmb⟩ := hc
        split at h
        · rename_i hT
          simp only [Option.some.injEq] at h; subst h
          have ht := truth_sound hM hP _ true hT
          have hcg : evalC env maps (.le a (zeroK k b')) = evalC env' maps (.le a (zeroK k b')) := by
            apply congrC
            intro i hi
            by_cases hik : i = k
            · subst hik; simp [occC, occE_zeroK i b' hmb, hoa] at hi
            · exact (hk i hik).symm
          rw [hcg] at ht
          simp only [evalC, decide_eq_true_eq] at ht ⊢
          have h0 := zeroK_eval env' maps k b' hmb
          have hge := monoE_ge env' maps k b' hmb
          omega
        · simp at h
      · simp at h
  | .lt a b', r, h => by
    simp only [atomK] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      obtain ⟨⟨hoa, hob⟩, hma⟩ := hc
      split at h
      · rename_i hT
        simp only [Option.some.injEq] at h; subst h
        have ht := truth_sound hM hP _ false hT
        have hcg : evalC env maps (.lt (zeroK k a) b') = evalC env' maps (.lt (zeroK k a) b') := by
          apply congrC
          intro i hi
          by_cases hik : i = k
          · subst hik; simp [occC, occE_zeroK i a hma, hob] at hi
          · exact (hk i hik).symm
        rw [hcg] at ht
        simp only [evalC, decide_eq_false_iff_not, Nat.not_lt] at ht ⊢
        have h0 := zeroK_eval env' maps k a hma
        have hge := monoE_ge env' maps k a hma
        omega
      · simp at h
    · split at h
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        obtain ⟨⟨hoa, hob⟩, hmb⟩ := hc
        split at h
        · rename_i hT
          simp only [Option.some.injEq] at h; subst h
          have ht := truth_sound hM hP _ true hT
          have hcg : evalC env maps (.lt a (zeroK k b')) = evalC env' maps (.lt a (zeroK k b')) := by
            apply congrC
            intro i hi
            by_cases hik : i = k
            · subst hik; simp [occC, occE_zeroK i b' hmb, hoa] at hi
            · exact (hk i hik).symm
          rw [hcg] at ht
          simp only [evalC, decide_eq_true_eq] at ht ⊢
          have h0 := zeroK_eval env' maps k b' hmb
          have hge := monoE_ge env' maps k b' hmb
          omega
        · simp at h
      · simp at h
  | .eq _ _, _, h => by simp [atomK] at h
  | .and _ _, _, h => by simp [atomK] at h
  | .or _ _, _, h => by simp [atomK] at h
  | .not _, _, h => by simp [atomK] at h

theorem truthK_sound {tab : List VDef} {env : Nat → Nat} {maps : Nat → Nat → Nat} {x : List Int} {path : Path}
    (hM : Model tab env maps x) (hP : PathHolds path x) (k : Nat) (env' : Nat → Nat) (hk : ∀ i, i ≠ k → env' i = env i) :
    (c : C) → (b : Bool) → truthK tab path k c = some b → evalC env' maps c = b
  | .le a b', r, h => by
    simp only [truthK] at h
    split at h
    · exact atomK_sound hM hP k env' hk _ r h
    · rename_i hocc
      rw [← truth_sound hM hP _ r h]
      exact congrC env' env maps _ (fun i hi => hk i (fun he => by subst he; exact hocc hi))
  | .lt a b', r, h => by
    simp only [truthK] at h
    split at h
    · exact atomK_sound hM hP k env' hk _ r h
    · rename_i hocc
      rw [← truth_sound hM hP _ r h]
      exact congrC env' env maps _ (fun i hi => hk i (fun he => by subst he; exact hocc hi))
  | .eq a b', r, h => by
    simp only [truthK] at h
    split at h
    · split at h
      · rename_i hA
        simp only [Option.some.injEq] at h; subst h
        have := atomK_sound hM hP k env' hk _ false hA
        simp only [evalC, decide_eq_false_iff_not, Nat.not_le] at this
        simp only [evalC, decide_eq_false_iff_not]; omega
      · rename_i hB _
        simp only [Option.some.injEq] at h; subst h
        have := atomK_sound hM hP k env' hk _ false hB
        simp only [evalC, decide_eq_false_iff_not, Nat.not_le] at this
        simp only [evalC, decide_eq_false_iff_not]; omega
      · simp at h
    · rename_i hocc
      rw [← truth_sound hM hP _ r h]
      exact congrC env' env maps _ (fun i hi => hk i (fun he => by subst he; exact hocc hi))
  | .and a b', r, h => by
    simp only [truthK] at h
    simp only [evalC]
    split at h
    · rename_i h1; simp only [Option.some.injEq] at h; subst h; simp [truthK_sound hM hP k env' hk a false h1]
    · rename_i h2 _; simp only [Option.some.injEq] at h; subst h; simp [truthK_sound hM hP k env' hk b' false h2]
    · rename_i h1 h2; simp only [Option.some.injEq] at h; subst h; simp [truthK_sound hM hP k env' hk a true h1, truthK_sound hM hP k env' hk b' true h2]
    · simp at h
  | .or a b', r, h => by
    simp only [truthK] at h
    simp only [evalC]
    split at h
    · rename_i h1; simp only [Option.some.injEq] at h; subst h; simp [truthK_sound hM hP k env' hk a true h1]
    · rename_i h2 _; simp only [Option.some.injEq] at h; subst h; simp [truthK_sound hM hP k env' hk b' true h2]
    · rename_i h1 h2; simp only [Option.some.injEq] at h; subst h; simp [truthK_sound hM hP k env' hk a false h1, truthK_sound hM hP k env' hk b' false h2]
    · simp at h
  | .not a, r, h => by
    simp only [truthK] at h
    split at h
    · rename_i r' h1; simp only [Option.some.injEq] at h; subst h; simp [evalC, truthK_sound hM hP k env' hk a r' h1]
    · simp at h

-- The decided conditions, as terms: 0 ≤ 0 and 0 < 0.
def cTrue : C := .le (.const 0) (.const 0)
def cFalse : C := .lt (.const 0) (.const 0)
def decideC (tab : List VDef) (path : Path) (k : Nat) (c : C) : C :=
  match truthK tab path k c with
  | some true => cTrue
  | some false => cFalse
  | none => c
def andC : C → C → C
  | .lt (.const 0) (.const 0), _ => cFalse
  | _, .lt (.const 0) (.const 0) => cFalse
  | .le (.const 0) (.const 0), y => y
  | x, .le (.const 0) (.const 0) => x
  | x, y => .and x y
def orC : C → C → C
  | .le (.const 0) (.const 0), _ => cTrue
  | _, .le (.const 0) (.const 0) => cTrue
  | .lt (.const 0) (.const 0), y => y
  | x, .lt (.const 0) (.const 0) => x
  | x, y => .or x y
def notC : C → C
  | .le (.const 0) (.const 0) => cFalse
  | .lt (.const 0) (.const 0) => cTrue
  | .not y => y
  | y => .not y
-- `(if C then 1 else 0) = 1` is C, `= 0` is ¬C; any other equation is decided as it stands.
def foldEq (tab : List VDef) (path : Path) (k : Nat) : E → E → C
  | .ite c (.const 1) (.const 0), .const 1 => c
  | .ite c (.const 1) (.const 0), .const 0 => notC c
  | .const 1, .ite c (.const 1) (.const 0) => c
  | .const 0, .ite c (.const 1) (.const 0) => notC c
  | a, b => decideC tab path k (.eq a b)

theorem decideC_eval {tab : List VDef} {env : Nat → Nat} {maps : Nat → Nat → Nat} {x : List Int} {path : Path}
    (hM : Model tab env maps x) (hP : PathHolds path x) (k : Nat) (env' : Nat → Nat) (hk : ∀ i, i ≠ k → env' i = env i)
    (c : C) : evalC env' maps (decideC tab path k c) = evalC env' maps c := by
  unfold decideC
  split
  · rename_i hT; rw [truthK_sound hM hP k env' hk c true hT]; simp [cTrue, evalC]
  · rename_i hT; rw [truthK_sound hM hP k env' hk c false hT]; simp [cFalse, evalC]
  · rfl
theorem andC_eval (ρ : Nat → Nat) (M : Nat → Nat → Nat) (a b : C) : evalC ρ M (andC a b) = (evalC ρ M a && evalC ρ M b) := by
  unfold andC; split <;> simp_all [evalC, cTrue, cFalse]
theorem orC_eval (ρ : Nat → Nat) (M : Nat → Nat → Nat) (a b : C) : evalC ρ M (orC a b) = (evalC ρ M a || evalC ρ M b) := by
  unfold orC; split <;> simp_all [evalC, cTrue, cFalse]
theorem notC_eval (ρ : Nat → Nat) (M : Nat → Nat → Nat) (a : C) : evalC ρ M (notC a) = !evalC ρ M a := by
  unfold notC; split <;> simp_all [evalC, cTrue, cFalse]
theorem foldEq_eval {tab : List VDef} {env : Nat → Nat} {maps : Nat → Nat → Nat} {x : List Int} {path : Path}
    (hM : Model tab env maps x) (hP : PathHolds path x) (k : Nat) (env' : Nat → Nat) (hk : ∀ i, i ≠ k → env' i = env i)
    (a b : E) : evalC env' maps (foldEq tab path k a b) = evalC env' maps (.eq a b) := by
  unfold foldEq
  split
  · simp only [evalC, evalE]; split <;> simp_all
  · rw [notC_eval]; simp only [evalC, evalE]; split <;> simp_all
  · simp only [evalC, evalE]; split <;> simp_all
  · rw [notC_eval]; simp only [evalC, evalE]; split <;> simp_all
  · exact decideC_eval hM hP k env' hk _

mutual
-- Each `if` whose condition is decided for every value of the key `k` under the path, resolved; the terms inside
-- conditions simplified and decided parts pruned; nothing else changes.
def simpE (tab : List VDef) (path : Path) (k : Nat) : E → E
  | .var i => .var i
  | .const n => .const n
  | .add a b => .add (simpE tab path k a) (simpE tab path k b)
  | .sub a b => .sub (simpE tab path k a) (simpE tab path k b)
  | .mul m a => .mul m (simpE tab path k a)
  | .min a b => .min (simpE tab path k a) (simpE tab path k b)
  | .max a b => .max (simpE tab path k a) (simpE tab path k b)
  | .prod a b => .prod (simpE tab path k a) (simpE tab path k b)
  | .ite c t f =>
    match simpC tab path k c with
    | .le (.const 0) (.const 0) => simpE tab path k t
    | .lt (.const 0) (.const 0) => simpE tab path k f
    | c' => .ite c' (simpE tab path k t) (simpE tab path k f)
  | .get m key => .get m (simpE tab path k key)
  | .tup a b => .tup (simpE tab path k a) (simpE tab path k b)
  | .proj j a => .proj j (simpE tab path k a)
def simpC (tab : List VDef) (path : Path) (k : Nat) : C → C
  | .le a b => decideC tab path k (.le (simpE tab path k a) (simpE tab path k b))
  | .lt a b => decideC tab path k (.lt (simpE tab path k a) (simpE tab path k b))
  | .eq a b => foldEq tab path k (simpE tab path k a) (simpE tab path k b)
  | .and a b => andC (simpC tab path k a) (simpC tab path k b)
  | .or a b => orC (simpC tab path k a) (simpC tab path k b)
  | .not a => notC (simpC tab path k a)
end

def whenPath (f : FrameCut) : Path := f.when.map (fun w => (w, true))

-- The two counts share their key, and under `when` their bounds and bodies are the same terms.
def frameOk (tab : List VDef) (cs : List Count) (f : FrameCut) : Bool :=
  match findCount cs f.post, findCount cs f.pre with
  | some c₁, some c₀ => c₁.key == c₀.key
      && beqE (simpE tab (whenPath f) c₁.key c₁.below) (simpE tab (whenPath f) c₁.key c₀.below)
      && beqE (simpE tab (whenPath f) c₁.key c₁.body) (simpE tab (whenPath f) c₁.key c₀.body)
  | _, _ => false

-- The rows a frame gives a leaf: post − pre ≤ 0 and pre − post ≤ 0, over the table's columns of the two variables.
def frameRows (tab : List VDef) (f : FrameCut) : List Cert.Row :=
  match findIdx (isVar f.post) tab, findIdx (isVar f.pre) tab with
  | some j₁, some j₀ => [lsub (lunit j₁) (lunit j₀), lsub (lunit j₀) (lunit j₁)]
  | _, _ => []

-- Eligibility reads only the original split path.
def frameActive (path : Path) (f : FrameCut) : Bool := f.when.all (fun w => dec path w == some true)

/-! Section 17.4 (MLDR-DESIGN.md): the per-key cut. A claim `post ≤ pre` between two counts of the same key and bound,
proved for every value of the key by the kernel's own goal checker on an auxiliary goal — hypotheses: the cut's conditions
(reading no key), the key below the bound, and the pre body below the post body at the key — and lifted to the sums by
`sumBelow_mono`. Nothing new is trusted: the auxiliary goal is checked by `checkGoal`. -/

structure MonoCut where
  when : List C
  post : Nat
  pre : Nat
  tab : List VDef
  tree : Tree

def monoHyps (m : MonoCut) (c₁ c₀ : Count) : List C := m.when ++ [.lt (.var c₁.key) c₁.below, .lt c₀.body c₁.body]

def monoOk (cs : List Count) (m : MonoCut) : Bool :=
  match findCount cs m.post, findCount cs m.pre with
  | some c₁, some c₀ => c₁.key == c₀.key && beqE c₁.below c₀.below && !occE c₁.key c₁.below
      && m.when.all (fun c => !occC c₁.key c) && checkGoal ⟨m.tab, monoHyps m c₁ c₀⟩ m.tree
  | _, _ => false

-- The row a cut gives a leaf: post − pre ≤ 0, over the table's columns of the two variables.
def monoRows (tab : List VDef) (m : MonoCut) : List Cert.Row :=
  match findIdx (isVar m.post) tab, findIdx (isVar m.pre) tab with
  | some j₁, some j₀ => [lsub (lunit j₁) (lunit j₀)]
  | _, _ => []

-- Eligibility: every condition decided true on the original split path.
def monoActive (tab : List VDef) (path : Path) (m : MonoCut) : Bool := m.when.all (fun c => truth tab path c == some true)

def MonoHolds (tab : List VDef) (env : Nat → Nat) (maps : Nat → Nat → Nat) (m : MonoCut) (x : List Int) : Prop :=
  (∀ c ∈ m.when, evalC env maps c = true) → ∀ r ∈ monoRows tab m, Cert.eval r x ≤ 0

/-- An accepted cut's row holds under its conditions, wherever both counts are their sums. -/
theorem mono_sound {tab : List VDef} {env : Nat → Nat} {maps : Nat → Nat → Nat} {x : List Int}
    (hM : Model tab env maps x) {cs : List Count} (hc : ∀ c ∈ cs, c.Holds env maps)
    {m : MonoCut} (hok : monoOk cs m = true) : MonoHolds tab env maps m x := by
  intro hw r hr
  simp only [monoOk] at hok
  split at hok
  · rename_i c₁ c₀ h₁ h₀
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.all_eq_true] at hok
    obtain ⟨⟨⟨⟨hkey, hbelow⟩, hob⟩, hwhen⟩, hchk⟩ := hok
    have hb := beqE_eq hbelow
    have hm₁ := lookup_some h₁
    have hm₀ := lookup_some h₀
    have hv₁ : c₁.v = m.post := by simpa using hm₁.2
    have hv₀ : c₀.v = m.pre := by simpa using hm₀.2
    have H₁ : env c₁.v = sumBelow (fun kk => evalE (upd env c₁.key kk) maps c₁.body) (evalE env maps c₁.below) := hc c₁ hm₁.1
    have H₀ : env c₀.v = sumBelow (fun kk => evalE (upd env c₀.key kk) maps c₀.body) (evalE env maps c₀.below) := hc c₀ hm₀.1
    have hpt : ∀ kk, kk < evalE env maps c₁.below →
        evalE (upd env c₁.key kk) maps c₁.body ≤ evalE (upd env c₁.key kk) maps c₀.body := by
      intro kk hkk
      apply Classical.byContradiction
      intro hnot
      have hlt := Nat.lt_of_not_le hnot
      apply sound ⟨m.tab, monoHyps m c₁ c₀⟩ m.tree hchk (upd env c₁.key kk) maps
      intro c hcm
      simp only [monoHyps, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hcm
      rcases hcm with hcm | rfl | rfl
      · have hk : ∀ i, occC i c = true → upd env c₁.key kk i = env i := fun i hi => by
          have hne : i ≠ c₁.key := fun he => by subst he; simp [hwhen c hcm] at hi
          simp [upd, hne]
        rw [congrC (upd env c₁.key kk) env maps c hk]
        exact hw c hcm
      · have hk : ∀ i, occE i c₁.below = true → upd env c₁.key kk i = env i := fun i hi => by
          have hne : i ≠ c₁.key := fun he => by subst he; simp [hob] at hi
          simp [upd, hne]
        simp only [evalC, evalE, decide_eq_true_eq]
        rw [congrE (upd env c₁.key kk) env maps c₁.below hk]
        simpa [upd] using hkk
      · simp only [evalC, decide_eq_true_eq]; exact hlt
    have hle : env c₁.v ≤ env c₀.v := by
      rw [H₁, H₀, ← hb, ← hkey]
      exact sumBelow_mono _ hpt
    simp only [monoRows] at hr
    split at hr
    · rename_i j₁ j₀ hj₁ hj₀
      have e₁ := var_col hM hj₁
      have e₀ := var_col hM hj₀
      simp only [List.mem_singleton] at hr
      subst hr
      rw [eval_lsub, eval_lunit, eval_lunit, e₁, e₀]
      rw [hv₁, hv₀] at hle
      omega
    · simp at hr
  · simp at hok

/-! Section 17.5 (MLDR-DESIGN.md): the linear per-key cut. A claim Σ pos m·x_v ≤ Σ neg m·x_v over counts of one key and
bound, proved for every value of the key by `checkGoal` on the auxiliary goal — the cut's conditions (reading no key), the key
below the bound, and Σ neg m·body_v(k) < Σ pos m·body_v(k) — and lifted to the sums by the linearity of `sumBelow`. The per-key
cut (MonoCut) is its one-term-a-side case. -/

structure LinCut where
  when : List C
  pos : List (Nat × Nat)   -- (coefficient, count variable)
  neg : List (Nat × Nat)
  tab : List VDef
  tree : Tree

-- The named counts with their coefficients, in order, or none.
def linCounts (cs : List Count) : List (Nat × Nat) → Option (List (Nat × Count))
  | [] => some []
  | (m, v) :: rest => match findCount cs v, linCounts cs rest with
    | some c, some tl => some ((m, c) :: tl)
    | _, _ => none

-- Σ m·body, as a term; the counts share their key, so every body reads it as written.
def linTerm : List (Nat × Count) → E
  | [] => .const 0
  | (m, c) :: rest => .add (.mul m c.body) (linTerm rest)

-- Σ m·x_v as a row over the table's columns of the variables, or none.
def linRow (tab : List VDef) : List (Nat × Nat) → Option Cert.Row
  | [] => some (lconst 0)
  | (m, v) :: rest => match findIdx (isVar v) tab, linRow tab rest with
    | some j, some r => some (ladd (lscale (m : Int) (lunit j)) r)
    | _, _ => none

def sameShape (c₀ : Count) (xs : List (Nat × Count)) : Bool := xs.all (fun p => p.2.key == c₀.key && beqE p.2.below c₀.below)

def linHyps (l : LinCut) (c₀ : Count) (ps ns : List (Nat × Count)) : List C :=
  l.when ++ [.lt (.var c₀.key) c₀.below, .lt (linTerm ns) (linTerm ps)]

def linOk (cs : List Count) (l : LinCut) : Bool :=
  match linCounts cs l.pos, linCounts cs l.neg with
  | some ps, some ns => match ps ++ ns with
    | [] => false
    | (_, c₀) :: _ => sameShape c₀ ps && sameShape c₀ ns && !occE c₀.key c₀.below && l.when.all (fun c => !occC c₀.key c)
        && checkGoal ⟨l.tab, linHyps l c₀ ps ns⟩ l.tree
  | _, _ => false

def linRows (tab : List VDef) (l : LinCut) : List Cert.Row :=
  match linRow tab l.pos, linRow tab l.neg with
  | some rp, some rn => [lsub rp rn]
  | _, _ => []

def linActive (tab : List VDef) (path : Path) (l : LinCut) : Bool := l.when.all (fun c => truth tab path c == some true)

def LinHolds (tab : List VDef) (env : Nat → Nat) (maps : Nat → Nat → Nat) (l : LinCut) (x : List Int) : Prop :=
  (∀ c ∈ l.when, evalC env maps c = true) → ∀ r ∈ linRows tab l, Cert.eval r x ≤ 0

-- Σ m·(sum of the body below the bound), in Nat, and Σ m·(the variable), in Int.
def linSumN (env : Nat → Nat) (maps : Nat → Nat → Nat) (key n : Nat) : List (Nat × Count) → Nat
  | [] => 0
  | (m, c) :: rest => m * sumBelow (fun kk => evalE (upd env key kk) maps c.body) n + linSumN env maps key n rest
def linSumZ (env : Nat → Nat) : List (Nat × Nat) → Int
  | [] => 0
  | (m, v) :: rest => (m : Int) * ((env v : Nat) : Int) + linSumZ env rest

theorem linTerm_eval (ρ : Nat → Nat) (M : Nat → Nat → Nat) : ∀ xs : List (Nat × Count),
    evalE ρ M (linTerm xs) = (xs.map (fun p => p.1 * evalE ρ M p.2.body)).sum
  | [] => by simp [linTerm, evalE]
  | (m, c) :: rest => by simp [linTerm, evalE, linTerm_eval ρ M rest]

theorem sumBelow_linTerm (env : Nat → Nat) (maps : Nat → Nat → Nat) (key n : Nat) : ∀ xs : List (Nat × Count),
    sumBelow (fun kk => evalE (upd env key kk) maps (linTerm xs)) n = linSumN env maps key n xs
  | [] => by simp [linTerm, evalE, linSumN, sumBelow_zero_fn]
  | (m, c) :: rest => by
    have h : (fun kk => evalE (upd env key kk) maps (linTerm ((m, c) :: rest)))
        = fun kk => m * evalE (upd env key kk) maps c.body + evalE (upd env key kk) maps (linTerm rest) := by
      funext kk; simp [linTerm, evalE]
    rw [h, sumBelow_add, sumBelow_mul, sumBelow_linTerm env maps key n rest]; rfl

-- The row's value is Σ m·x[j] = Σ m·env v.
theorem linRow_eval {tab : List VDef} {env : Nat → Nat} {maps : Nat → Nat → Nat} {x : List Int} (hM : Model tab env maps x) :
    ∀ (xs : List (Nat × Nat)) (r : Cert.Row), linRow tab xs = some r → Cert.eval r x = linSumZ env xs
  | [], r, h => by simp only [linRow, Option.some.injEq] at h; subst h; simp [linSumZ, eval_lconst]
  | (m, v) :: rest, r, h => by
    simp only [linRow] at h
    split at h
    · rename_i j r' hj hr
      simp only [Option.some.injEq] at h; subst h
      rw [eval_ladd, eval_lscale, eval_lunit, var_col hM hj, linRow_eval hM rest r' hr]; rfl
    · simp at h

-- With every named count its sum (of the shared key and bound), Σ m·env v is Σ m·(its body summed below the bound).
theorem linSum_holds {env : Nat → Nat} {maps : Nat → Nat → Nat} {cs : List Count} (hc : ∀ c ∈ cs, c.Holds env maps) (c₀ : Count) :
    ∀ (vs : List (Nat × Nat)) (ps : List (Nat × Count)), linCounts cs vs = some ps → sameShape c₀ ps = true →
      linSumZ env vs = ((linSumN env maps c₀.key (evalE env maps c₀.below) ps : Nat) : Int)
  | [], ps, h, _ => by simp only [linCounts, Option.some.injEq] at h; subst h; simp [linSumZ, linSumN]
  | (m, v) :: rest, ps, h, hs => by
    simp only [linCounts] at h
    split at h
    · rename_i c tl hfind htl
      simp only [Option.some.injEq] at h; subst h
      simp only [sameShape, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hs
      obtain ⟨⟨hkey, hbelow⟩, hrest⟩ := hs
      have hb := beqE_eq hbelow
      have hm := lookup_some hfind
      have hv : c.v = v := by simpa using hm.2
      have H : env c.v = sumBelow (fun kk => evalE (upd env c.key kk) maps c.body) (evalE env maps c.below) := hc c hm.1
      simp only [linSumZ, linSumN]
      rw [← hv, H, hkey, hb, linSum_holds hc c₀ rest tl htl (by simpa [sameShape] using hrest)]
      simp [Int.natCast_add, Int.natCast_mul]
    · simp at h

/-- An accepted linear cut's row holds under its conditions, wherever the named counts are their sums. -/
theorem lin_sound {tab : List VDef} {env : Nat → Nat} {maps : Nat → Nat → Nat} {x : List Int}
    (hM : Model tab env maps x) {cs : List Count} (hc : ∀ c ∈ cs, c.Holds env maps)
    {l : LinCut} (hok : linOk cs l = true) : LinHolds tab env maps l x := by
  intro hw r hr
  simp only [linOk] at hok
  split at hok
  · rename_i ps ns hps hns
    split at hok
    · simp at hok
    · rename_i c₀ tl hcons
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hok
      obtain ⟨⟨⟨⟨hsp, hsn⟩, hob⟩, hwhen⟩, hchk⟩ := hok
      -- pointwise: Σ pos ≤ Σ neg at every key below the bound
      have hpt : ∀ kk, kk < evalE env maps c₀.below →
          evalE (upd env c₀.key kk) maps (linTerm ps) ≤ evalE (upd env c₀.key kk) maps (linTerm ns) := by
        intro kk hkk
        apply Classical.byContradiction
        intro hnot
        have hlt := Nat.lt_of_not_le hnot
        apply sound ⟨l.tab, linHyps l c₀ ps ns⟩ l.tree hchk (upd env c₀.key kk) maps
        intro c hcm
        simp only [linHyps, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hcm
        rcases hcm with hcm | rfl | rfl
        · have hk : ∀ i, occC i c = true → upd env c₀.key kk i = env i := fun i hi => by
            have hne : i ≠ c₀.key := fun he => by subst he; simp [hwhen c hcm] at hi
            simp [upd, hne]
          rw [congrC (upd env c₀.key kk) env maps c hk]
          exact hw c hcm
        · have hk : ∀ i, occE i c₀.below = true → upd env c₀.key kk i = env i := fun i hi => by
            have hne : i ≠ c₀.key := fun he => by subst he; simp [hob] at hi
            simp [upd, hne]
          simp only [evalC, evalE, decide_eq_true_eq]
          rw [congrE (upd env c₀.key kk) env maps c₀.below hk]
          simpa [upd] using hkk
        · simp only [evalC, decide_eq_true_eq]; exact hlt
      have hsum := sumBelow_mono (evalE env maps c₀.below) hpt
      rw [sumBelow_linTerm, sumBelow_linTerm] at hsum
      -- the row
      simp only [linRows] at hr
      split at hr
      · rename_i rp rn hrp hrn
        simp only [List.mem_singleton] at hr
        subst hr
        rw [eval_lsub, linRow_eval hM l.pos rp hrp, linRow_eval hM l.neg rn hrn,
          linSum_holds hc c₀ l.pos ps hps hsp, linSum_holds hc c₀ l.neg ns hns hsn]
        have hz : ((linSumN env maps c₀.key (evalE env maps c₀.below) ps : Nat) : Int) ≤ ((linSumN env maps c₀.key (evalE env maps c₀.below) ns : Nat) : Int) := Int.ofNat_le.mpr hsum
        omega
      · simp at hr
  · simp at hok

-- The active frames' rows in front of the lemma path.
def framePath (tab : List VDef) (frames : List FrameCut) (monos : List MonoCut) (lemmas : List CutLemma) (path : Path) (lins : List LinCut := []) : Path :=
  (lins.filter (linActive tab path)).flatMap (fun l => (linRows tab l).map (fun r => (r, true)))
    ++ ((monos.filter (monoActive tab path)).flatMap (fun m => (monoRows tab m).map (fun r => (r, true)))
    ++ ((frames.filter (frameActive path)).flatMap (fun f => (frameRows tab f).map (fun r => (r, true))) ++ lemmaPath lemmas path))

def checkTFrames (tab : List VDef) (hyps : List C) (lemmas : List CutLemma) (frames : List FrameCut) (monos : List MonoCut) (lins : List LinCut) : Path → Tree → Bool
  | path, .split l y n => checkTFrames tab hyps lemmas frames monos lins ((l, true) :: path) y && checkTFrames tab hyps lemmas frames monos lins ((l, false) :: path) n
  | path, t => checkT tab hyps (framePath tab frames monos lemmas path lins) t

def checkGoalFrames (g : Goal) (cs : List Count) (t : Tree) (lemmas : List CutLemma) (frames : List FrameCut) (monos : List MonoCut := []) (lins : List LinCut := []) : Bool :=
  wfTab 0 g.tab && lemmas.all (checkLemma g.tab g.hyps) && frames.all (frameOk g.tab cs) && monos.all (monoOk cs) && lins.all (linOk cs) && checkTFrames g.tab g.hyps lemmas frames monos lins [] t

@[simp] theorem framePath_nil (tab : List VDef) (lemmas : List CutLemma) (path : Path) : framePath tab [] [] lemmas path [] = lemmaPath lemmas path := rfl

@[simp] theorem checkTFrames_nil (tab : List VDef) (hyps : List C) (lemmas : List CutLemma) (t : Tree) (path : Path) :
    checkTFrames tab hyps lemmas [] [] [] path t = checkTLemmas tab hyps lemmas path t := by
  induction t generalizing path with
  | split l y n ihy ihn => simp only [checkTFrames, checkTLemmas, ihy, ihn]
  | leaf rows steps eqs prods => rfl
  | leafAt rows steps eqs prods => rfl
  | leafSq rows sqs steps eqs prods => rfl

@[simp] theorem checkGoalFrames_nil (g : Goal) (cs : List Count) (t : Tree) (lemmas : List CutLemma) :
    checkGoalFrames g cs t lemmas [] = checkGoalLemmas g t lemmas := by
  simp [checkGoalFrames, checkGoalLemmas]

mutual
/-- Resolving decided conditions keeps a term's value, at any environment that differs from the model's only at the
key. -/
theorem simpE_eval {tab : List VDef} {env : Nat → Nat} {maps : Nat → Nat → Nat} {x : List Int} {path : Path}
    (hM : Model tab env maps x) (hP : PathHolds path x) (k : Nat) (env' : Nat → Nat) (hk : ∀ i, i ≠ k → env' i = env i) :
    (e : E) → evalE env' maps (simpE tab path k e) = evalE env' maps e
  | .var i => rfl
  | .const n => rfl
  | .add a b => by simp only [simpE, evalE, simpE_eval hM hP k env' hk a, simpE_eval hM hP k env' hk b]
  | .sub a b => by simp only [simpE, evalE, simpE_eval hM hP k env' hk a, simpE_eval hM hP k env' hk b]
  | .mul m a => by simp only [simpE, evalE, simpE_eval hM hP k env' hk a]
  | .min a b => by simp only [simpE, evalE, simpE_eval hM hP k env' hk a, simpE_eval hM hP k env' hk b]
  | .max a b => by simp only [simpE, evalE, simpE_eval hM hP k env' hk a, simpE_eval hM hP k env' hk b]
  | .prod a b => by simp only [simpE, evalE, simpE_eval hM hP k env' hk a, simpE_eval hM hP k env' hk b]
  | .get m key => by simp only [simpE, evalE, simpE_eval hM hP k env' hk key]
  | .tup a b => by simp only [simpE, evalE, simpE_eval hM hP k env' hk a, simpE_eval hM hP k env' hk b]
  | .proj j a => by simp only [simpE, evalE, simpE_eval hM hP k env' hk a]
  | .ite c t f => by
    have ht := simpE_eval hM hP k env' hk t
    have hf := simpE_eval hM hP k env' hk f
    have hc := simpC_eval hM hP k env' hk c
    simp only [simpE]
    split
    · rename_i heq
      rw [heq] at hc
      have hc' : evalC env' maps c = true := by simpa [evalC] using hc.symm
      simp only [evalE, hc', ite_true, ht]
    · rename_i heq
      rw [heq] at hc
      have hc' : evalC env' maps c = false := by simpa [evalC] using hc.symm
      simp only [evalE, hc', Bool.false_eq_true, ite_false, hf]
    · simp only [evalE, hc, ht, hf]
theorem simpC_eval {tab : List VDef} {env : Nat → Nat} {maps : Nat → Nat → Nat} {x : List Int} {path : Path}
    (hM : Model tab env maps x) (hP : PathHolds path x) (k : Nat) (env' : Nat → Nat) (hk : ∀ i, i ≠ k → env' i = env i) :
    (c : C) → evalC env' maps (simpC tab path k c) = evalC env' maps c
  | .le a b => by
    have ha := simpE_eval hM hP k env' hk a
    have hb := simpE_eval hM hP k env' hk b
    simp only [simpC]; rw [decideC_eval hM hP k env' hk]; simp only [evalC, ha, hb]
  | .lt a b => by
    have ha := simpE_eval hM hP k env' hk a
    have hb := simpE_eval hM hP k env' hk b
    simp only [simpC]; rw [decideC_eval hM hP k env' hk]; simp only [evalC, ha, hb]
  | .eq a b => by
    have ha := simpE_eval hM hP k env' hk a
    have hb := simpE_eval hM hP k env' hk b
    simp only [simpC]; rw [foldEq_eval hM hP k env' hk]; simp only [evalC, ha, hb]
  | .and a b => by simp only [simpC, andC_eval, evalC, simpC_eval hM hP k env' hk a, simpC_eval hM hP k env' hk b]
  | .or a b => by simp only [simpC, orC_eval, evalC, simpC_eval hM hP k env' hk a, simpC_eval hM hP k env' hk b]
  | .not a => by simp only [simpC, notC_eval, evalC, simpC_eval hM hP k env' hk a]
end

def FrameHolds (tab : List VDef) (f : FrameCut) (x : List Int) : Prop :=
  (∀ w ∈ f.when, Cert.eval w x ≤ 0) → ∀ r ∈ frameRows tab f, Cert.eval r x ≤ 0

/-- An accepted frame's rows hold under its conditions, wherever both counts are their sums. -/
theorem frame_sound {tab : List VDef} {env : Nat → Nat} {maps : Nat → Nat → Nat} {x : List Int}
    (hM : Model tab env maps x) {cs : List Count} (hc : ∀ c ∈ cs, c.Holds env maps)
    {f : FrameCut} (hok : frameOk tab cs f = true) : FrameHolds tab f x := by
  intro hw
  have hP : PathHolds (whenPath f) x := by
    intro a ha
    obtain ⟨w, hwm, rfl⟩ := List.mem_map.mp ha
    simpa using hw w hwm
  simp only [frameOk] at hok
  split at hok
  · rename_i c₁ c₀ h₁ h₀
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨hkey, hbelow⟩, hbody⟩ := hok
    have hb := beqE_eq hbelow
    have hd := beqE_eq hbody
    have hm₁ := lookup_some h₁
    have hm₀ := lookup_some h₀
    have hv₁ : c₁.v = f.post := by simpa using hm₁.2
    have hv₀ : c₀.v = f.pre := by simpa using hm₀.2
    have H₁ : env c₁.v = sumBelow (fun kk => evalE (upd env c₁.key kk) maps c₁.body) (evalE env maps c₁.below) := hc c₁ hm₁.1
    have H₀ : env c₀.v = sumBelow (fun kk => evalE (upd env c₀.key kk) maps c₀.body) (evalE env maps c₀.below) := hc c₀ hm₀.1
    have heq : env f.post = env f.pre := by
      rw [← hv₁, ← hv₀, H₁, H₀]
      have eb : evalE env maps c₁.below = evalE env maps c₀.below := by
        rw [← simpE_eval hM hP c₁.key env (fun _ _ => rfl) c₁.below, hb, simpE_eval hM hP c₁.key env (fun _ _ => rfl) c₀.below]
      rw [eb]
      apply sumBelow_congr
      intro kk _
      have hk' : ∀ i, i ≠ c₁.key → upd env c₁.key kk i = env i := fun i hi => by simp [upd, hi]
      rw [← simpE_eval hM hP c₁.key (upd env c₁.key kk) hk' c₁.body, hd, simpE_eval hM hP c₁.key (upd env c₁.key kk) hk' c₀.body, hkey]
    intro r hr
    simp only [frameRows] at hr
    split at hr
    · rename_i j₁ j₀ hj₁ hj₀
      have e₁ := var_col hM hj₁
      have e₀ := var_col hM hj₀
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [eval_lsub, eval_lunit, eval_lunit, e₁, e₀, heq]; omega
      · rw [eval_lsub, eval_lunit, eval_lunit, e₁, e₀, heq]; omega
    · simp at hr
  · simp at hok

theorem framePath_holds {tab : List VDef} {env : Nat → Nat} {maps : Nat → Nat → Nat} {frames : List FrameCut} {monos : List MonoCut}
    {lins : List LinCut} {lemmas : List CutLemma} {path : Path} {x : List Int}
    (hM : Model tab env maps x) (hP : PathHolds path x) (hL : ∀ l ∈ lemmas, CutHolds l x) (hF : ∀ f ∈ frames, FrameHolds tab f x)
    (hMo : ∀ m ∈ monos, MonoHolds tab env maps m x) (hLi : ∀ l ∈ lins, LinHolds tab env maps l x) :
    PathHolds (framePath tab frames monos lemmas path lins) x := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨l, hl, ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨hlm, hactive⟩ := List.mem_filter.mp hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
    have hwhen : ∀ c ∈ l.when, evalC env maps c = true := fun c hc => by
      have ht : truth tab path c = some true := by
        simpa only [linActive, List.all_eq_true, beq_iff_eq] using (List.all_eq_true.mp hactive c hc)
      exact truth_sound hM hP c true ht
    simpa using hLi l hlm hwhen r hr
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨m, hm, ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨hmm, hactive⟩ := List.mem_filter.mp hm
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
    have hwhen : ∀ c ∈ m.when, evalC env maps c = true := fun c hc => by
      have ht : truth tab path c = some true := by
        simpa only [monoActive, List.all_eq_true, beq_iff_eq] using (List.all_eq_true.mp hactive c hc)
      exact truth_sound hM hP c true ht
    simpa using hMo m hmm hwhen r hr
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨f, hf, ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨hfm, hactive⟩ := List.mem_filter.mp hf
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
    have hwhen : ∀ w ∈ f.when, Cert.eval w x ≤ 0 := fun w hw => by
      have hd : dec path w = some true := by
        simpa only [frameActive, List.all_eq_true, beq_iff_eq] using (List.all_eq_true.mp hactive w hw)
      have := dec_sound hP hd
      simpa using this
    simpa using hF f hfm hwhen r hr
  · exact lemmaPath_holds hP hL a ha

theorem checkTFrames_sound {tab : List VDef} {hyps : List C} {env : Nat → Nat} {maps : Nat → Nat → Nat} {x : List Int}
    (hM : Model tab env maps x) (hH : ∀ c ∈ hyps, evalC env maps c = true)
    {lemmas : List CutLemma} (hL : ∀ l ∈ lemmas, CutHolds l x) {frames : List FrameCut} (hF : ∀ f ∈ frames, FrameHolds tab f x)
    {monos : List MonoCut} (hMo : ∀ m ∈ monos, MonoHolds tab env maps m x) {lins : List LinCut} (hLi : ∀ l ∈ lins, LinHolds tab env maps l x) :
    ∀ (t : Tree) (path : Path), PathHolds path x → checkTFrames tab hyps lemmas frames monos lins path t = true → False
  | .split l y n, path, hP, h => by
    simp only [checkTFrames, Bool.and_eq_true] at h
    by_cases hl : Cert.eval l x ≤ 0
    · refine checkTFrames_sound hM hH hL hF hMo hLi y _ ?_ h.1
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simpa using hl
      · exact hP a ha
    · refine checkTFrames_sound hM hH hL hF hMo hLi n _ ?_ h.2
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simpa using hl
      · exact hP a ha
  | .leaf rows steps eqs prods, path, hP, h =>
    checkT_sound hM hH _ _ (framePath_holds hM hP hL hF hMo hLi) h
  | .leafAt rows steps eqs prods, path, hP, h =>
    checkT_sound hM hH _ _ (framePath_holds hM hP hL hF hMo hLi) h
  | .leafSq rows sqs steps eqs prods, path, hP, h =>
    checkT_sound hM hH _ _ (framePath_holds hM hP hL hF hMo hLi) h

/-- The goal checker with frames has the original unsatisfiability conclusion, wherever the named counts are their
sums. -/
theorem goalFrames_sound (g : Goal) (cs : List Count) (t : Tree) (lemmas : List CutLemma) (frames : List FrameCut) (monos : List MonoCut) (lins : List LinCut)
    (h : checkGoalFrames g cs t lemmas frames monos lins = true) (env : Nat → Nat) (maps : Nat → Nat → Nat)
    (hc : ∀ c ∈ cs, c.Holds env maps) : ¬ ∀ c ∈ g.hyps, evalC env maps c = true := by
  intro hH
  simp only [checkGoalFrames, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hw, hl⟩, hf⟩, hmo⟩, hli⟩, ht⟩ := h
  have hv := build_valid env maps g.tab [] [] ⟨rfl, by simp, by simp⟩ (by simpa using hw)
  simp only [List.nil_append] at hv
  have hM := model_of_valid hv
  exact checkTFrames_sound hM hH (fun l hm => lemma_sound hM hH (hl l hm)) (fun f hm => frame_sound hM hc (hf f hm)) (fun m hm => mono_sound hM hc (hmo m hm)) (fun l hm => lin_sound hM hc (hli l hm)) t [] (by simp [PathHolds]) ht

end FrameCuts

-- The check: fresh witnesses, every instance built, then the same goal extended by checked conditional cuts.
def checkCounted (g : CGoal) (is : List CInst) (tab : List VDef) (t : Tree) (lemmas : List CutLemma := []) : Bool :=
  countedOk g.hyps g.counts is && match countHyps g.counts is with
    | some hs => checkGoalLemmas ⟨tab, g.hyps ++ hs⟩ t lemmas
    | none => false

/-- With no lemma entries the old counted check is unchanged. -/
theorem checkCounted_nil (g : CGoal) (is : List CInst) (tab : List VDef) (t : Tree) :
    checkCounted g is tab t [] = (countedOk g.hyps g.counts is && match countHyps g.counts is with
      | some hs => checkGoal ⟨tab, g.hyps ++ hs⟩ t
      | none => false) := by
  simp only [checkCounted, checkGoalLemmas_nil]

/-! Soundness -/

theorem cDistinct_cons {a : Nat} {as : List Nat} (h : cDistinct (a :: as) = true) : a ∉ as ∧ cDistinct as = true := by
  simp only [cDistinct, Bool.and_eq_true] at h
  refine ⟨fun hm => ?_, h.2⟩
  have h1 := h.1
  simp at h1
  exact h1 hm

theorem applyS_one (k : Nat) (t : E) (ρ : Nat → Nat) (M : Nat → Nat → Nat) : applyS [(k, t)] ρ M = upd ρ k (evalE ρ M t) := by
  funext i
  simp only [applyS, assoc, lookup, upd]
  by_cases h : i = k
  · subst h; simp
  · have hb : (k == i) = false := by simp; omega
    simp [hb, h]

theorem resolve_mem {cs : List Count} {B : E} : ∀ {ts : List (Int × Nat)} {rs : List (Int × Count)},
    resolve cs B ts = some rs → ∀ r ∈ rs, r.2 ∈ cs ∧ r.2.below = B
  | [], rs, h => by simp only [resolve, Option.some.injEq] at h; subst h; simp
  | t :: ts, rs, h => by
    cases hc : findCount cs t.2 with
    | none => simp [resolve, hc] at h
    | some c =>
      by_cases hb : beqE c.below B = true
      · cases hr : resolve cs B ts with
        | none => simp [resolve, hc, hb, hr] at h
        | some rs' =>
          simp [resolve, hc, hb, hr] at h
          subst h
          intro r hr'
          rcases List.mem_cons.mp hr' with rfl | hr'
          · exact ⟨(lookup_some hc).1, beqE_eq hb⟩
          · exact resolve_mem hr r hr'
      · simp [resolve, hc, hb] at h

theorem countHyps_mem {cs : List Count} : ∀ {is : List CInst} {hs : List C}, countHyps cs is = some hs → ∀ h ∈ hs, ∃ i ∈ is, countHyp cs i = some h
  | [], hs, hh => by simp only [countHyps, Option.some.injEq] at hh; subst hh; simp
  | i :: is, hs, hh => by
    cases e1 : countHyp cs i with
    | none => simp [countHyps, e1] at hh
    | some h1 =>
      cases e2 : countHyps cs is with
      | none => simp [countHyps, e1, e2] at hh
      | some hs' =>
        simp [countHyps, e1, e2] at hh
        subst hh
        intro h hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact ⟨i, List.mem_cons_self, e1⟩
        · obtain ⟨j, hj, hj'⟩ := countHyps_mem e2 h hm
          exact ⟨j, List.mem_cons_of_mem _ hj, hj'⟩

-- The two sides, evaluated: the counts' combination, and the bodies' at a key.
def sumSide (part : Int → Nat) (ρ : Nat → Nat) : List (Int × Count) → Nat
  | [] => 0
  | r :: rs => part r.1 * ρ r.2.v + sumSide part ρ rs
def ptSide (part : Int → Nat) (ρ : Nat → Nat) (M : Nat → Nat → Nat) : List (Int × Count) → Nat → Nat
  | [], _ => 0
  | r :: rs, k => part r.1 * evalE (upd ρ r.2.key k) M r.2.body + ptSide part ρ M rs k

theorem eval_sumE_count (part : Int → Nat) (ρ : Nat → Nat) (M : Nat → Nat → Nat) : ∀ rs : List (Int × Count),
    evalE ρ M (sumE (rs.map fun r => .mul (part r.1) (atCount r.2))) = sumSide part ρ rs
  | [] => by simp [sumE, evalE, sumSide]
  | r :: rs => by
    simp only [List.map_cons, sumE, evalE, eval_sumE_count part ρ M rs]
    simp [atCount, evalE, sumSide]

theorem eval_sumE_wit (part : Int → Nat) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (w : Nat) : ∀ rs : List (Int × Count),
    evalE ρ M (sumE (rs.map fun r => .mul (part r.1) (atWit w r.2))) = ptSide part ρ M rs (ρ w)
  | [] => by simp [sumE, evalE, ptSide]
  | r :: rs => by
    simp only [List.map_cons, sumE, evalE, eval_sumE_wit part ρ M w rs]
    simp only [ptSide, atWit, subst_evalE, applyS_one, evalE]

-- With every count its sum below one bound, the counts' combination sums the bodies' over the keys below it.
theorem sumSide_eq (part : Int → Nat) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (n : Nat) : ∀ rs : List (Int × Count),
    (∀ r ∈ rs, ρ r.2.v = sumBelow (fun k => evalE (upd ρ r.2.key k) M r.2.body) n) →
      sumSide part ρ rs = sumBelow (ptSide part ρ M rs) n
  | [], _ => by
    have : ptSide part ρ M [] = fun _ => 0 := funext fun k => by simp [ptSide]
    simp [sumSide, this, sumBelow_const]
  | r :: rs, h => by
    simp only [sumSide]
    have hp : ptSide part ρ M (r :: rs) = fun k => part r.1 * evalE (upd ρ r.2.key k) M r.2.body + ptSide part ρ M rs k := rfl
    rw [hp, sumBelow_add, sumBelow_mul, ← h r List.mem_cons_self, sumSide_eq part ρ M n rs (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))]

-- The witness values a state gives the instances' witnesses.
def setWits (ρ : Nat → Nat) (ws : List (Nat × Nat)) : Nat → Nat := fun j =>
  match lookup (fun p => p.1 == j) ws with
  | some p => p.2
  | none => ρ j

theorem setWits_other {ρ : Nat → Nat} {ws : List (Nat × Nat)} {j : Nat} (h : j ∉ ws.map (·.1)) : setWits ρ ws j = ρ j := by
  have hl : lookup (fun p => p.1 == j) ws = none :=
    lookup_none (fun p hp => by simp only [beq_eq_false_iff_ne]; intro he; exact h (by rw [← he]; exact List.mem_map_of_mem hp))
  simp [setWits, hl]

theorem setWits_at {ρ : Nat → Nat} : ∀ {ws : List (Nat × Nat)}, cDistinct (ws.map (·.1)) = true → ∀ {p : Nat × Nat}, p ∈ ws → setWits ρ ws p.1 = p.2
  | [], _, _, hp => by simp at hp
  | a :: as, hd, p, hp => by
    simp only [List.map_cons] at hd
    obtain ⟨hna, hd'⟩ := cDistinct_cons hd
    rcases List.mem_cons.mp hp with rfl | hp'
    · simp [setWits, lookup]
    · have hne : (a.1 == p.1) = false := by
        simp only [beq_eq_false_iff_ne]; intro he; exact hna (by rw [he]; exact List.mem_map_of_mem hp')
      have ih := setWits_at (ρ := ρ) hd' hp'
      simp only [setWits, lookup, hne, Bool.false_eq_true, ite_false] at ih ⊢
      exact ih

theorem witFresh_parts {hyps : List C} {cs : List Count} {is : List CInst} {w : Nat} (h : witFresh hyps cs is w = true) :
    (∀ h' ∈ hyps, occC w h' = false) ∧ (∀ c ∈ cs, c.v ≠ w ∧ occE w c.below = false ∧ occE w c.body = false) ∧ (∀ j ∈ is, occE w j.below = false) := by
  simp only [witFresh, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1, fun c hc => ⟨(h.1.2 c hc).1.1, (h.1.2 c hc).1.2, (h.1.2 c hc).2⟩, h.2⟩

/-- The kind is sound: an accepted counted goal's hypotheses hold at no naturals and maps where every count is its
sum. -/
theorem counted_sound (g : CGoal) (is : List CInst) (tab : List VDef) (t : Tree) {lemmas : List CutLemma}
    (hck : checkCounted g is tab t lemmas = true)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hc : ∀ c ∈ g.counts, c.Holds ρ M) : ¬ ∀ h ∈ g.hyps, evalC ρ M h = true := by
  intro hH
  simp only [checkCounted, Bool.and_eq_true] at hck
  obtain ⟨hok, hgoal⟩ := hck
  simp only [countedOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨hdist, hfresh⟩ := hok
  cases hhs : countHyps g.counts is with
  | none => simp [hhs] at hgoal
  | some hs =>
  simp only [hhs] at hgoal
  -- Each instance's witness value, chosen at ρ: a key below the bound where the combination is positive, when its sum is.
  have hx : ∀ i : CInst, ∃ x : Nat, ∀ rs, resolve g.counts i.below i.terms = some rs →
      sumBelow (fun k => ptSide posP ρ M rs k + posP i.unit) (evalE ρ M i.below) ≤ sumBelow (fun k => ptSide negP ρ M rs k + negP i.unit) (evalE ρ M i.below)
      ∨ (x < evalE ρ M i.below ∧ ptSide negP ρ M rs x + negP i.unit < ptSide posP ρ M rs x + posP i.unit) := by
    intro i
    cases hr : resolve g.counts i.below i.terms with
    | none => exact ⟨0, fun rs h => by simp at h⟩
    | some rs =>
      by_cases hlt : sumBelow (fun k => ptSide negP ρ M rs k + negP i.unit) (evalE ρ M i.below) < sumBelow (fun k => ptSide posP ρ M rs k + posP i.unit) (evalE ρ M i.below)
      · obtain ⟨k, hk, hk'⟩ := exists_lt_of_sumBelow_lt hlt
        exact ⟨k, fun rs' h => by simp only [Option.some.injEq] at h; subst h; exact Or.inr ⟨hk, hk'⟩⟩
      · exact ⟨0, fun rs' h => by simp only [Option.some.injEq] at h; subst h; exact Or.inl (Nat.le_of_not_lt hlt)⟩
  obtain ⟨xs, hxs⟩ : ∃ xs : CInst → Nat, ∀ i rs, resolve g.counts i.below i.terms = some rs →
      sumBelow (fun k => ptSide posP ρ M rs k + posP i.unit) (evalE ρ M i.below) ≤ sumBelow (fun k => ptSide negP ρ M rs k + negP i.unit) (evalE ρ M i.below)
      ∨ (xs i < evalE ρ M i.below ∧ ptSide negP ρ M rs (xs i) + negP i.unit < ptSide posP ρ M rs (xs i) + posP i.unit) :=
    ⟨fun i => Classical.choose (hx i), fun i => Classical.choose_spec (hx i)⟩
  -- ρs: ρ with each witness set to its value.
  obtain ⟨ρs, hother, hat⟩ : ∃ ρs : Nat → Nat, (∀ j, (∀ i ∈ is, i.wit ≠ j) → ρs j = ρ j) ∧ (∀ i ∈ is, ρs i.wit = xs i) := by
    have hws : (is.map fun i => (i.wit, xs i)).map (·.1) = is.map (·.wit) := by induction is <;> simp_all
    refine ⟨setWits ρ (is.map fun i => (i.wit, xs i)), fun j hj => setWits_other ?_, fun i hi => ?_⟩
    · rw [hws]; intro hm; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm; exact hj i hi rfl
    · exact setWits_at (ρ := ρ) (ws := is.map fun i => (i.wit, xs i)) (by rw [hws]; exact hdist) (p := (i.wit, xs i)) (List.mem_map.mpr ⟨i, hi, rfl⟩)
  -- What the witnesses' freshness gives: counts and bounds read alike at ρs and ρ.
  have hvar : ∀ c ∈ g.counts, ρs c.v = ρ c.v := fun c hc =>
    hother c.v (fun i hi he => ((witFresh_parts (hfresh i hi)).2.1 c hc).1 he.symm)
  have hbound : ∀ e : E, (∀ i ∈ is, occE i.wit e = false) → evalE ρs M e = evalE ρ M e := fun e he =>
    congrE ρs ρ M e (fun j hj => hother j (fun i hi hij => by have := he i hi; rw [hij] at this; simp [this] at hj))
  have hbody : ∀ c ∈ g.counts, ∀ k, evalE (upd ρs c.key k) M c.body = evalE (upd ρ c.key k) M c.body := fun c hc k =>
    congrE _ _ M c.body (fun j hj => by
      simp only [upd]; split
      · rfl
      · exact hother j (fun i hi hij => by
          have := ((witFresh_parts (hfresh i hi)).2.1 c hc).2.2; rw [hij] at this; simp [this] at hj))
  have hpt : ∀ (part : Int → Nat) (rs : List (Int × Count)), (∀ r ∈ rs, r.2 ∈ g.counts) → ∀ k, ptSide part ρs M rs k = ptSide part ρ M rs k := by
    intro part rs hrs k
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      simp only [ptSide, hbody r.2 (hrs r List.mem_cons_self) k, ih (fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr'))]
  -- Every instance's hypothesis holds at ρs.
  have hinst : ∀ i ∈ is, ∀ h, countHyp g.counts i = some h → evalC ρs M h = true := by
    intro i hi h hh
    simp only [countHyp, Option.map_eq_some_iff] at hh
    obtain ⟨rs, hr, rfl⟩ := hh
    have hrm := resolve_mem hr
    have hB : evalE ρs M i.below = evalE ρ M i.below := hbound i.below (fun j hj => (witFresh_parts (hfresh j hj)).2.2 i hi)
    have hcnt : ∀ r ∈ rs, ρs r.2.v = sumBelow (fun k => evalE (upd ρs r.2.key k) M r.2.body) (evalE ρ M i.below) := by
      intro r hr'
      obtain ⟨hcm, hcb⟩ := hrm r hr'
      have h1 : ρ r.2.v = sumBelow (fun k => evalE (upd ρ r.2.key k) M r.2.body) (evalE ρ M r.2.below) := hc r.2 hcm
      rw [hvar r.2 hcm, h1, hcb]
      exact sumBelow_congr _ (fun k _ => (hbody r.2 hcm k).symm)
    have hS : ∀ part, evalE ρs M (side part atCount i.below i.unit rs)
        = sumBelow (fun k => ptSide part ρ M rs k + part i.unit) (evalE ρ M i.below) := by
      intro part
      have e1 : evalE ρs M (side part atCount i.below i.unit rs) = sumSide part ρs rs + part i.unit * evalE ρ M i.below := by
        simp only [side, evalE, eval_sumE_count, hB]
      have e2 : sumBelow (fun k => ptSide part ρ M rs k + part i.unit) (evalE ρ M i.below)
          = sumBelow (ptSide part ρ M rs) (evalE ρ M i.below) + part i.unit * evalE ρ M i.below := by
        rw [sumBelow_add (ptSide part ρ M rs) (fun _ => part i.unit), sumBelow_const]
      have e3 : sumSide part ρs rs = sumBelow (ptSide part ρ M rs) (evalE ρ M i.below) := by
        rw [sumSide_eq part ρs M _ rs hcnt]
        exact sumBelow_congr _ (fun k _ => hpt part rs (fun r hr' => (hrm r hr').1) k)
      rw [e1, e2, e3]
    have hW : ∀ part, evalE ρs M (side part (atWit i.wit) (.const 1) i.unit rs) = ptSide part ρ M rs (xs i) + part i.unit := by
      intro part
      simp only [side, evalE, eval_sumE_wit, hat i hi, hpt part rs (fun r hr' => (hrm r hr').1), Nat.mul_one]
    have hv := hxs i rs hr
    simp only [evalC, hS, hW, evalE, hat i hi, hB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact hv
  -- The goal's hypotheses hold at ρs too: no witness is read there.
  have hhyp : ∀ h ∈ g.hyps, evalC ρs M h = true := fun h hm => by
    rw [congrC ρs ρ M h (fun j hj => hother j (fun i hi hij => by
      have := (witFresh_parts (hfresh i hi)).1 h hm; rw [hij] at this; simp [this] at hj))]
    exact hH h hm
  exact goalLemmas_sound ⟨tab, g.hyps ++ hs⟩ t lemmas hgoal ρs M (fun h hm => by
    rcases List.mem_append.mp hm with hm | hm
    · exact hhyp h hm
    · obtain ⟨i, hi, hh⟩ := countHyps_mem hhs h hm
      exact hinst i hi h hh)


-- The counted check with frames: fresh witnesses, every instance built, the goal extended by checked lemma cuts and
-- frames over its own counts.
def checkCountedF (g : CGoal) (is : List CInst) (tab : List VDef) (t : Tree) (frames : List FrameCut) (lemmas : List CutLemma := []) (monos : List MonoCut := []) (lins : List LinCut := []) : Bool :=
  countedOk g.hyps g.counts is && match countHyps g.counts is with
    | some hs => checkGoalFrames ⟨tab, g.hyps ++ hs⟩ g.counts t lemmas frames monos lins
    | none => false

/-- With no frames the counted check with lemma cuts is unchanged. -/
theorem checkCountedF_nil (g : CGoal) (is : List CInst) (tab : List VDef) (t : Tree) (lemmas : List CutLemma) :
    checkCountedF g is tab t [] lemmas = checkCounted g is tab t lemmas := by
  cases h : countHyps g.counts is <;> simp [checkCountedF, checkCounted, h]

/-- The kind with frames is sound: an accepted counted goal's hypotheses hold at no naturals and maps where every
count is its sum. -/
theorem countedF_sound (g : CGoal) (is : List CInst) (tab : List VDef) (t : Tree) (frames : List FrameCut) {lemmas : List CutLemma} {monos : List MonoCut} {lins : List LinCut}
    (hck : checkCountedF g is tab t frames lemmas monos lins = true)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hc : ∀ c ∈ g.counts, c.Holds ρ M) : ¬ ∀ h ∈ g.hyps, evalC ρ M h = true := by
  intro hH
  simp only [checkCountedF, Bool.and_eq_true] at hck
  obtain ⟨hok, hgoal⟩ := hck
  simp only [countedOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨hdist, hfresh⟩ := hok
  cases hhs : countHyps g.counts is with
  | none => simp [hhs] at hgoal
  | some hs =>
  simp only [hhs] at hgoal
  -- Each instance's witness value, chosen at ρ: a key below the bound where the combination is positive, when its sum is.
  have hx : ∀ i : CInst, ∃ x : Nat, ∀ rs, resolve g.counts i.below i.terms = some rs →
      sumBelow (fun k => ptSide posP ρ M rs k + posP i.unit) (evalE ρ M i.below) ≤ sumBelow (fun k => ptSide negP ρ M rs k + negP i.unit) (evalE ρ M i.below)
      ∨ (x < evalE ρ M i.below ∧ ptSide negP ρ M rs x + negP i.unit < ptSide posP ρ M rs x + posP i.unit) := by
    intro i
    cases hr : resolve g.counts i.below i.terms with
    | none => exact ⟨0, fun rs h => by simp at h⟩
    | some rs =>
      by_cases hlt : sumBelow (fun k => ptSide negP ρ M rs k + negP i.unit) (evalE ρ M i.below) < sumBelow (fun k => ptSide posP ρ M rs k + posP i.unit) (evalE ρ M i.below)
      · obtain ⟨k, hk, hk'⟩ := exists_lt_of_sumBelow_lt hlt
        exact ⟨k, fun rs' h => by simp only [Option.some.injEq] at h; subst h; exact Or.inr ⟨hk, hk'⟩⟩
      · exact ⟨0, fun rs' h => by simp only [Option.some.injEq] at h; subst h; exact Or.inl (Nat.le_of_not_lt hlt)⟩
  obtain ⟨xs, hxs⟩ : ∃ xs : CInst → Nat, ∀ i rs, resolve g.counts i.below i.terms = some rs →
      sumBelow (fun k => ptSide posP ρ M rs k + posP i.unit) (evalE ρ M i.below) ≤ sumBelow (fun k => ptSide negP ρ M rs k + negP i.unit) (evalE ρ M i.below)
      ∨ (xs i < evalE ρ M i.below ∧ ptSide negP ρ M rs (xs i) + negP i.unit < ptSide posP ρ M rs (xs i) + posP i.unit) :=
    ⟨fun i => Classical.choose (hx i), fun i => Classical.choose_spec (hx i)⟩
  -- ρs: ρ with each witness set to its value.
  obtain ⟨ρs, hother, hat⟩ : ∃ ρs : Nat → Nat, (∀ j, (∀ i ∈ is, i.wit ≠ j) → ρs j = ρ j) ∧ (∀ i ∈ is, ρs i.wit = xs i) := by
    have hws : (is.map fun i => (i.wit, xs i)).map (·.1) = is.map (·.wit) := by induction is <;> simp_all
    refine ⟨setWits ρ (is.map fun i => (i.wit, xs i)), fun j hj => setWits_other ?_, fun i hi => ?_⟩
    · rw [hws]; intro hm; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm; exact hj i hi rfl
    · exact setWits_at (ρ := ρ) (ws := is.map fun i => (i.wit, xs i)) (by rw [hws]; exact hdist) (p := (i.wit, xs i)) (List.mem_map.mpr ⟨i, hi, rfl⟩)
  -- What the witnesses' freshness gives: counts and bounds read alike at ρs and ρ.
  have hvar : ∀ c ∈ g.counts, ρs c.v = ρ c.v := fun c hc =>
    hother c.v (fun i hi he => ((witFresh_parts (hfresh i hi)).2.1 c hc).1 he.symm)
  have hbound : ∀ e : E, (∀ i ∈ is, occE i.wit e = false) → evalE ρs M e = evalE ρ M e := fun e he =>
    congrE ρs ρ M e (fun j hj => hother j (fun i hi hij => by have := he i hi; rw [hij] at this; simp [this] at hj))
  have hbody : ∀ c ∈ g.counts, ∀ k, evalE (upd ρs c.key k) M c.body = evalE (upd ρ c.key k) M c.body := fun c hc k =>
    congrE _ _ M c.body (fun j hj => by
      simp only [upd]; split
      · rfl
      · exact hother j (fun i hi hij => by
          have := ((witFresh_parts (hfresh i hi)).2.1 c hc).2.2; rw [hij] at this; simp [this] at hj))
  have hpt : ∀ (part : Int → Nat) (rs : List (Int × Count)), (∀ r ∈ rs, r.2 ∈ g.counts) → ∀ k, ptSide part ρs M rs k = ptSide part ρ M rs k := by
    intro part rs hrs k
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      simp only [ptSide, hbody r.2 (hrs r List.mem_cons_self) k, ih (fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr'))]
  -- Every instance's hypothesis holds at ρs.
  have hinst : ∀ i ∈ is, ∀ h, countHyp g.counts i = some h → evalC ρs M h = true := by
    intro i hi h hh
    simp only [countHyp, Option.map_eq_some_iff] at hh
    obtain ⟨rs, hr, rfl⟩ := hh
    have hrm := resolve_mem hr
    have hB : evalE ρs M i.below = evalE ρ M i.below := hbound i.below (fun j hj => (witFresh_parts (hfresh j hj)).2.2 i hi)
    have hcnt : ∀ r ∈ rs, ρs r.2.v = sumBelow (fun k => evalE (upd ρs r.2.key k) M r.2.body) (evalE ρ M i.below) := by
      intro r hr'
      obtain ⟨hcm, hcb⟩ := hrm r hr'
      have h1 : ρ r.2.v = sumBelow (fun k => evalE (upd ρ r.2.key k) M r.2.body) (evalE ρ M r.2.below) := hc r.2 hcm
      rw [hvar r.2 hcm, h1, hcb]
      exact sumBelow_congr _ (fun k _ => (hbody r.2 hcm k).symm)
    have hS : ∀ part, evalE ρs M (side part atCount i.below i.unit rs)
        = sumBelow (fun k => ptSide part ρ M rs k + part i.unit) (evalE ρ M i.below) := by
      intro part
      have e1 : evalE ρs M (side part atCount i.below i.unit rs) = sumSide part ρs rs + part i.unit * evalE ρ M i.below := by
        simp only [side, evalE, eval_sumE_count, hB]
      have e2 : sumBelow (fun k => ptSide part ρ M rs k + part i.unit) (evalE ρ M i.below)
          = sumBelow (ptSide part ρ M rs) (evalE ρ M i.below) + part i.unit * evalE ρ M i.below := by
        rw [sumBelow_add (ptSide part ρ M rs) (fun _ => part i.unit), sumBelow_const]
      have e3 : sumSide part ρs rs = sumBelow (ptSide part ρ M rs) (evalE ρ M i.below) := by
        rw [sumSide_eq part ρs M _ rs hcnt]
        exact sumBelow_congr _ (fun k _ => hpt part rs (fun r hr' => (hrm r hr').1) k)
      rw [e1, e2, e3]
    have hW : ∀ part, evalE ρs M (side part (atWit i.wit) (.const 1) i.unit rs) = ptSide part ρ M rs (xs i) + part i.unit := by
      intro part
      simp only [side, evalE, eval_sumE_wit, hat i hi, hpt part rs (fun r hr' => (hrm r hr').1), Nat.mul_one]
    have hv := hxs i rs hr
    simp only [evalC, hS, hW, evalE, hat i hi, hB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact hv
  -- The goal's hypotheses hold at ρs too: no witness is read there.
  have hhyp : ∀ h ∈ g.hyps, evalC ρs M h = true := fun h hm => by
    rw [congrC ρs ρ M h (fun j hj => hother j (fun i hi hij => by
      have := (witFresh_parts (hfresh i hi)).1 h hm; rw [hij] at this; simp [this] at hj))]
    exact hH h hm
  have hholds' : ∀ c ∈ g.counts, c.Holds ρs M := by
    intro c hcm
    have h1 : ρ c.v = sumBelow (fun k => evalE (upd ρ c.key k) M c.body) (evalE ρ M c.below) := hc c hcm
    simp only [Count.Holds]
    rw [hvar c hcm, h1, hbound c.below (fun i hi => ((witFresh_parts (hfresh i hi)).2.1 c hcm).2.1)]
    exact sumBelow_congr _ (fun k _ => (hbody c hcm k).symm)
  exact goalFrames_sound ⟨tab, g.hyps ++ hs⟩ g.counts t lemmas frames monos lins hgoal ρs M hholds' (fun h hm => by
    rcases List.mem_append.mp hm with hm | hm
    · exact hhyp h hm
    · obtain ⟨i, hi, hh⟩ := countHyps_mem hhs h hm
      exact hinst i hi h hh)

end Kern

#print axioms Kern.exists_lt_of_sumBelow_lt
#print axioms Kern.pigeonhole
#print axioms Kern.majorities_meet
#print axioms Kern.quorums_meet_outside
#print axioms Kern.lemma_sound
#print axioms Kern.goalLemmas_sound
#print axioms Kern.counted_sound
#print axioms Kern.frame_sound
#print axioms Kern.goalFrames_sound
#print axioms Kern.countedF_sound

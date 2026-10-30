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

-- The check: fresh witnesses, every instance built, and the tree refuting the goal's hypotheses followed by the
-- instances', in that order.
def checkCounted (g : CGoal) (is : List CInst) (tab : List VDef) (t : Tree) : Bool :=
  countedOk g.hyps g.counts is && match countHyps g.counts is with
    | some hs => checkGoal ⟨tab, g.hyps ++ hs⟩ t
    | none => false

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
theorem counted_sound (g : CGoal) (is : List CInst) (tab : List VDef) (t : Tree) (hck : checkCounted g is tab t = true)
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
  exact sound ⟨tab, g.hyps ++ hs⟩ t hgoal ρs M (fun h hm => by
    rcases List.mem_append.mp hm with hm | hm
    · exact hhyp h hm
    · obtain ⟨i, hi, hh⟩ := countHyps_mem hhs h hm
      exact hinst i hi h hh)

end Kern

#print axioms Kern.exists_lt_of_sumBelow_lt
#print axioms Kern.pigeonhole
#print axioms Kern.majorities_meet
#print axioms Kern.quorums_meet_outside
#print axioms Kern.counted_sound

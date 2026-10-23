import Kernel
/-!
Rationals: linear arithmetic over ℚ, the twin of kernel/kernel.ts's rational section and core/check.ts's derivations
without cuts, with its soundness proof. Lean 4.34.0, core only (core's `Rat`).

The rows are Cert's (integer coefficients and constant), read at a rational point, each with a strictness: `(r, false)`
says r ≤ 0, `(r, true)` says r < 0. A derivation is Cert's steps: an input row, or a positive combination of two
earlier rows (strict when either is). A cut is refused: it is the one step whose soundness needs an integer point
(`Cert.cut_sound`), so the naturals' and integers' checks are this one with the cut added. `checkQ` accepts when the
last row has only zero coefficients and a positive constant, or a constant ≥ 0 and is strict: Farkas' lemma with
strict rows (Motzkin's), the refutation complete for linear arithmetic over ℚ. `checkQ_sound`: no rational point
satisfies every input.

Terms (`QE`) are rationals: variables, rational constants, +, − (not truncated), × by a rational constant, min, max,
if; conditions (`QC`) ≤, <, =, and, or, not. A term's linear form is a Cert row over a positive denominator (`LF`:
the term's value is `evalQ row / den`), so every row a leaf reads has integer coefficients and none is rounded. A
proof is a tree of splits on rows (yes: r ≤ 0, no: −r < 0) with a leaf certificate: the rows it claims (each one of
the leaf's rows, by coefficients) and a derivation over them. `sound`: if `checkGoal` accepts, no rational
environment satisfies every hypothesis. `machine_sound`: the induction rule for a step machine whose state, params and
inputs are rationals.
-/

namespace Q
open Cert Kern
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! Rows at a rational point. -/

def dotQ : List (Nat × Int) → (Nat → Rat) → Rat
  | [], _ => 0
  | p :: rest, x => (p.2 : Rat) * x p.1 + dotQ rest x

def evalQ (r : Row) (x : Nat → Rat) : Rat := dotQ r.coefs x + r.const

theorem dotQ_app (x : Nat → Rat) : ∀ (a b : List (Nat × Int)), dotQ (a ++ b) x = dotQ a x + dotQ b x
  | [], b => by simp [dotQ, Rat.zero_add]
  | p :: a, b => by simp only [List.cons_append, dotQ, dotQ_app x a b]; grind

theorem dotQ_addF (x : Nat → Rat) : ∀ (n : Nat) (a b : List (Nat × Int)), dotQ (addF n a b) x = dotQ a x + dotQ b x
  | 0, a, b => by simp only [addF, dotQ_app]
  | _ + 1, [], b => by simp [addF, dotQ, Rat.zero_add]
  | _ + 1, _ :: _, [] => by simp [addF, dotQ, Rat.add_zero]
  | n + 1, p :: as, q :: bs => by
    simp only [addF]
    split
    · simp only [dotQ, dotQ_addF x n as (q :: bs)]; grind
    · split
      · simp only [dotQ, dotQ_addF x n (p :: as) bs]; grind
      · have hpq : p.1 = q.1 := by omega
        split
        · rename_i hz
          simp only [dotQ, dotQ_addF x n as bs, hpq]
          have hz' : (p.2 : Rat) + (q.2 : Rat) = 0 := by rw [← Rat.intCast_add, hz]; rfl
          have : (p.2 : Rat) * x q.1 + (q.2 : Rat) * x q.1 = 0 := by rw [← Rat.add_mul, hz', Rat.zero_mul]
          grind
        · simp only [dotQ, dotQ_addF x n as bs, hpq, Rat.intCast_add, Rat.add_mul]; grind

theorem dotQ_addL (a b : List (Nat × Int)) (x : Nat → Rat) : dotQ (addL a b) x = dotQ a x + dotQ b x := dotQ_addF x _ a b

theorem dotQ_map (m : Int) (x : Nat → Rat) : ∀ (a : List (Nat × Int)), dotQ (a.map (fun p => (p.1, m * p.2))) x = m * dotQ a x
  | [] => by simp [dotQ]
  | p :: a => by simp only [List.map_cons, dotQ, dotQ_map m x a, Rat.intCast_mul, Rat.mul_add, Rat.mul_assoc]

theorem dotQ_scaleL (m : Int) (a : List (Nat × Int)) (x : Nat → Rat) : dotQ (scaleL m a) x = m * dotQ a x := by
  unfold scaleL
  split
  · rename_i h; subst h; simp [dotQ]
  · exact dotQ_map m x a

theorem dotQ_allZero : ∀ (a : List (Nat × Int)) (x : Nat → Rat), allZero a = true → dotQ a x = 0
  | [], _, _ => rfl
  | p :: a, x, h => by
    simp only [allZero, Bool.and_eq_true, beq_iff_eq] at h
    simp [dotQ, h.1, dotQ_allZero a x h.2, Rat.zero_add]

theorem evalQ_ladd (a b : Row) (x : Nat → Rat) : evalQ (ladd a b) x = evalQ a x + evalQ b x := by
  simp only [evalQ, ladd, dotQ_addL, Rat.intCast_add]; grind
theorem evalQ_lscale (m : Int) (a : Row) (x : Nat → Rat) : evalQ (lscale m a) x = m * evalQ a x := by
  simp only [evalQ, lscale, dotQ_scaleL, Rat.intCast_mul, Rat.mul_add]
theorem evalQ_lsub (a b : Row) (x : Nat → Rat) : evalQ (lsub a b) x = evalQ a x - evalQ b x := by
  simp only [lsub, evalQ_ladd, evalQ_lscale]; grind
theorem evalQ_lunit (j : Nat) (x : Nat → Rat) : evalQ (lunit j) x = x j := by
  simp [evalQ, lunit, dotQ, Rat.add_zero]
theorem evalQ_lconst (n : Int) (x : Nat → Rat) : evalQ (lconst n) x = n := by
  simp [evalQ, lconst, dotQ, Rat.zero_add]
theorem same_evalQ {a b : Row} (h : same a b = true) (x : Nat → Rat) : evalQ a x = evalQ b x := by
  simp only [same, Bool.and_eq_true, beq_iff_eq] at h
  have h1 : evalQ (lsub a b) x = 0 := by simp only [evalQ, dotQ_allZero _ x h.1, h.2]; grind
  rw [evalQ_lsub] at h1; grind

/-! Derivations without cuts, over strict and non-strict rows. -/

-- `(r, s)` holds at x: r < 0 if s, else r ≤ 0.
def Holds (x : Nat → Rat) (p : Row × Bool) : Prop := if p.2 then evalQ p.1 x < 0 else evalQ p.1 x ≤ 0

theorem Holds.le {x : Nat → Rat} {p : Row × Bool} (h : Holds x p) : evalQ p.1 x ≤ 0 := by
  unfold Holds at h; split at h
  · exact Rat.le_of_lt h
  · exact h

def replayQ (inputs : List (Row × Bool)) : List Step → Nat → List (Row × Bool) → Option (List (Row × Bool))
  | [], _, rows => some rows
  | .input i :: ss, n, rows =>
    match inputs[i]? with
    | some r => replayQ inputs ss (n + 1) (r :: rows)
    | none => none
  | .combine a b ma mb :: ss, n, rows =>
    match rows[n - 1 - a]?, rows[n - 1 - b]? with
    | some A, some B => if a < n ∧ b < n ∧ 0 < ma ∧ 0 < mb then replayQ inputs ss (n + 1) ((combineRow ma mb A.1 B.1, A.2 || B.2) :: rows) else none
    | _, _ => none
  | .cut _ _ _ _ :: _, _, _ => none

def checkQ (inputs : List (Row × Bool)) (steps : List Step) : Bool :=
  match replayQ inputs steps 0 [] with
  | some rows =>
    match rows.head? with
    | some r => allZero r.1.coefs && (decide (0 < r.1.const) || (r.2 && decide (0 ≤ r.1.const)))
    | none => false
  | none => false

theorem combine_holds {x : Nat → Rat} {ma mb : Int} (hma : 0 < ma) (hmb : 0 < mb) {A B : Row × Bool}
    (hA : Holds x A) (hB : Holds x B) : Holds x (combineRow ma mb A.1 B.1, A.2 || B.2) := by
  have eq : evalQ (combineRow ma mb A.1 B.1) x = (ma : Rat) * evalQ A.1 x + (mb : Rat) * evalQ B.1 x := by
    simp only [evalQ, combineRow, dotQ_addL, dotQ_scaleL, Rat.intCast_add, Rat.intCast_mul]; grind
  have pa : (0 : Rat) < ma := Rat.intCast_pos.mpr hma
  have pb : (0 : Rat) < mb := Rat.intCast_pos.mpr hmb
  have la : (ma : Rat) * evalQ A.1 x ≤ 0 := by
    have := Rat.mul_le_mul_of_nonneg_left hA.le (Rat.le_of_lt pa); simpa using this
  have lb : (mb : Rat) * evalQ B.1 x ≤ 0 := by
    have := Rat.mul_le_mul_of_nonneg_left hB.le (Rat.le_of_lt pb); simpa using this
  unfold Holds
  simp only [eq]
  split
  · rename_i hs
    simp only [Bool.or_eq_true] at hs
    rcases hs with hs | hs
    · have hA' : evalQ A.1 x < 0 := by unfold Holds at hA; simp [hs] at hA; exact hA
      have : (ma : Rat) * evalQ A.1 x < 0 := by
        have := Rat.mul_lt_mul_of_pos_left hA' pa; simpa using this
      grind
    · have hB' : evalQ B.1 x < 0 := by unfold Holds at hB; simp [hs] at hB; exact hB
      have : (mb : Rat) * evalQ B.1 x < 0 := by
        have := Rat.mul_lt_mul_of_pos_left hB' pb; simpa using this
      grind
  · grind

-- Every row a replay produces holds wherever the inputs and the rows so far hold.
theorem replayQ_holds (inputs : List (Row × Bool)) (x : Nat → Rat) (hx : ∀ r ∈ inputs, Holds x r) :
    ∀ (ss : List Step) (n : Nat) (rows out : List (Row × Bool)), (∀ r ∈ rows, Holds x r) →
      replayQ inputs ss n rows = some out → ∀ r ∈ out, Holds x r := by
  intro ss
  induction ss with
  | nil =>
    intro n rows out hrows h
    simp only [replayQ, Option.some.injEq] at h
    exact h ▸ hrows
  | cons s ss ih =>
    intro n rows out hrows h
    cases s with
    | input i =>
      simp only [replayQ] at h
      split at h
      · rename_i r hr
        refine ih _ _ out ?_ h
        intro r' hr'
        rcases List.mem_cons.mp hr' with hr' | hr'
        · exact hr' ▸ hx r (List.mem_of_getElem? hr)
        · exact hrows r' hr'
      · exact absurd h (by simp)
    | combine a b ma mb =>
      simp only [replayQ] at h
      split at h
      · rename_i A B hA hB
        split at h
        · rename_i hm
          refine ih _ _ out ?_ h
          intro r' hr'
          rcases List.mem_cons.mp hr' with hr' | hr'
          · subst hr'
            exact combine_holds hm.2.2.1 hm.2.2.2 (hrows A (List.mem_of_getElem? hA)) (hrows B (List.mem_of_getElem? hB))
          · exact hrows r' hr'
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    | cut o g q c => simp [replayQ] at h

/-- A certificate `checkQ` accepts refutes its inputs: no rational point satisfies them all. -/
theorem checkQ_sound (inputs : List (Row × Bool)) (steps : List Step) (h : checkQ inputs steps = true) (x : Nat → Rat)
    (hx : ∀ r ∈ inputs, Holds x r) : False := by
  simp only [checkQ] at h
  split at h
  · rename_i rows hrows
    split at h
    · rename_i r hr
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      have hall := replayQ_holds inputs x hx steps 0 [] rows (by simp) hrows
      have hm : r ∈ rows := by
        cases rows with
        | nil => simp at hr
        | cons a as => simp only [List.head?, Option.some.injEq] at hr; subst hr; exact List.mem_cons_self
      have hh := hall r hm
      have hv : evalQ r.1 x = r.1.const := by simp only [evalQ, dotQ_allZero r.1.coefs x h.1]; grind
      unfold Holds at hh
      rcases h.2 with hc | ⟨hs, hc⟩
      · have hc' : (0 : Rat) < r.1.const := Rat.intCast_pos.mpr hc
        split at hh <;> grind
      · have hc' : (0 : Rat) ≤ r.1.const := Rat.intCast_nonneg.mpr hc
        simp only [hs, ite_true] at hh
        grind
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! Terms and conditions over the rationals. -/

mutual
inductive QE where
  | var (i : Nat)
  | const (q : Rat)
  | add (a b : QE)
  | sub (a b : QE)
  | mul (k : Rat) (a : QE)
  | min (a b : QE)
  | max (a b : QE)
  | ite (c : QC) (t f : QE)
inductive QC where
  | le (a b : QE)
  | lt (a b : QE)
  | eq (a b : QE)
  | and (a b : QC)
  | or (a b : QC)
  | not (a : QC)
end

mutual
def evalE (ρ : Nat → Rat) : QE → Rat
  | .var i => ρ i
  | .const q => q
  | .add a b => evalE ρ a + evalE ρ b
  | .sub a b => evalE ρ a - evalE ρ b
  | .mul k a => k * evalE ρ a
  | .min a b => if evalE ρ a ≤ evalE ρ b then evalE ρ a else evalE ρ b
  | .max a b => if evalE ρ a ≤ evalE ρ b then evalE ρ b else evalE ρ a
  | .ite c t f => if evalC ρ c then evalE ρ t else evalE ρ f
def evalC (ρ : Nat → Rat) : QC → Bool
  | .le a b => decide (evalE ρ a ≤ evalE ρ b)
  | .lt a b => decide (evalE ρ a < evalE ρ b)
  | .eq a b => decide (evalE ρ a = evalE ρ b)
  | .and a b => evalC ρ a && evalC ρ b
  | .or a b => evalC ρ a || evalC ρ b
  | .not a => !evalC ρ a
end

/-! Linear forms: a row over a positive denominator, the term's value being `evalQ row / den`. -/

structure LF where
  row : Row
  den : Nat

-- The row of a − b (its value a positive multiple of a's value minus b's).
def dif (a b : LF) : Row := lsub (lscale b.den a.row) (lscale a.den b.row)

-- The path: rows decided so far. `(l, true)` says l ≤ 0, `(l, false)` says l > 0.
def PathHolds (path : Path) (x : Nat → Rat) : Prop := ∀ a ∈ path, decide (evalQ a.1 x ≤ 0) = a.2

-- Whether the path decides l ≤ 0: a constant row decides itself, else the path's own decision on the same row.
def dec (path : Path) (l : Row) : Option Bool :=
  if allZero l.coefs then some (decide (l.const ≤ 0)) else (lookup (fun a => same a.1 l) path).map (·.2)

mutual
def linear (path : Path) : QE → Option LF
  | .var i => some ⟨lunit i, 1⟩
  | .const q => some ⟨lconst q.num, q.den⟩
  | .add a b => match linear path a, linear path b with
    | some la, some lb => some ⟨ladd (lscale lb.den la.row) (lscale la.den lb.row), la.den * lb.den⟩
    | _, _ => none
  | .sub a b => match linear path a, linear path b with
    | some la, some lb => some ⟨dif la lb, la.den * lb.den⟩
    | _, _ => none
  | .mul k a => match linear path a with
    | some la => some ⟨lscale k.num la.row, k.den * la.den⟩
    | none => none
  | .min a b => match linear path a, linear path b with
    | some la, some lb => match dec path (dif la lb) with
      | some true => some la
      | some false => some lb
      | none => none
    | _, _ => none
  | .max a b => match linear path a, linear path b with
    | some la, some lb => match dec path (dif la lb) with
      | some true => some lb
      | some false => some la
      | none => none
    | _, _ => none
  | .ite c t f => match truth path c with
    | some true => linear path t
    | some false => linear path f
    | none => none
def truth (path : Path) : QC → Option Bool
  | .le a b => match linear path a, linear path b with
    | some la, some lb => dec path (dif la lb)
    | _, _ => none
  | .lt a b => match linear path a, linear path b with
    | some la, some lb => (dec path (dif lb la)).map (!·)
    | _, _ => none
  | .eq a b => match linear path a, linear path b with
    | some la, some lb => match dec path (dif la lb), dec path (dif lb la) with
      | some false, _ => some false
      | _, some false => some false
      | some true, some true => some true
      | _, _ => none
    | _, _ => none
  | .and a b => match truth path a, truth path b with
    | some false, _ => some false
    | _, some false => some false
    | some true, some true => some true
    | _, _ => none
  | .or a b => match truth path a, truth path b with
    | some true, _ => some true
    | _, some true => some true
    | some false, some false => some false
    | _, _ => none
  | .not a => (truth path a).map (!·)
end

/-! Facts: the rows a hypothesis gives under the path when it has the truth value `pos` (strict ones flagged). -/

def facts (path : Path) : Bool → QC → List (Row × Bool)
  | pos, .not a => facts path (!pos) a
  | pos, .and a b =>
    if pos then facts path pos a ++ facts path pos b
    else if truth path a = some true then facts path false b
    else if truth path b = some true then facts path false a
    else []
  | pos, .or a b =>
    if !pos then facts path false a ++ facts path false b
    else if truth path a = some false then facts path true b
    else if truth path b = some false then facts path true a
    else []
  | pos, .le a b => match linear path a, linear path b with
    | some la, some lb => if pos then [(dif la lb, false)] else [(dif lb la, true)]
    | _, _ => []
  | pos, .lt a b => match linear path a, linear path b with
    | some la, some lb => if pos then [(dif la lb, true)] else [(dif lb la, false)]
    | _, _ => []
  | pos, .eq a b => match linear path a, linear path b with
    | some la, some lb =>
      if pos then [(dif la lb, false), (dif lb la, false)]
      else if dec path (dif la lb) = some true then [(dif la lb, true)]
      else if dec path (dif lb la) = some true then [(dif lb la, true)]
      else []
    | _, _ => []

/-! Leaves and trees. -/

-- A decided atom as a row: l ≤ 0, or −l < 0.
def atomRow (a : Row × Bool) : Row × Bool := if a.2 then (a.1, false) else (lscale (-1) a.1, true)
def leafRows (path : Path) (hyps : List QC) : List (Row × Bool) := path.map atomRow ++ hyps.flatMap (facts path true)

-- A claimed row is a leaf row with the same coefficients, as strict as claimed (a strict row may be claimed as ≤).
def claimOk (rows : List (Row × Bool)) (r : Row × Bool) : Bool := rows.any fun q => same q.1 r.1 && (q.2 || !r.2)

inductive QTree where
  | split (l : Row) (yes no : QTree)
  | leaf (rows : List (Row × Bool)) (steps : List Step)

-- A split on a row the path already decides is refused (its two sides would read one decision two ways).
def checkT (hyps : List QC) : Path → QTree → Bool
  | path, .leaf rows steps => rows.all (claimOk (leafRows path hyps)) && checkQ rows steps
  | path, .split l yes no => (dec path l).isNone && checkT hyps ((l, true) :: path) yes && checkT hyps ((l, false) :: path) no

def checkGoal (hyps : List QC) (t : QTree) : Bool := checkT hyps [] t

/-! Soundness. -/

theorem num_eq (q : Rat) : (q.num : Rat) = (q.den : Rat) * q := by
  have h1 := Rat.num_divInt_den q
  rw [Rat.divInt_eq_div] at h1
  have hd : (q.den : Rat) ≠ 0 := by simp [q.den_nz]
  have e : ((q.den : Int) : Rat) = (q.den : Rat) := rfl
  rw [e] at h1
  calc (q.num : Rat) = (q.num : Rat) / q.den * q.den := (Rat.div_mul_cancel hd).symm
    _ = q * q.den := by rw [h1]
    _ = q.den * q := Rat.mul_comm _ _

theorem mul_nonpos_iff {k t : Rat} (hk : 0 < k) : k * t ≤ 0 ↔ t ≤ 0 := by
  constructor
  · intro h; exact Rat.le_of_mul_le_mul_left (by simpa using h) hk
  · intro h; have := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt hk); simpa using this
theorem mul_neg_iff {k t : Rat} (hk : 0 < k) : k * t < 0 ↔ t < 0 := by
  have := Rat.mul_lt_mul_left (a := t) (b := 0) hk; simpa using this

-- l represents the value v at x.
def Rep (x : Nat → Rat) (l : LF) (v : Rat) : Prop := 0 < l.den ∧ evalQ l.row x = (l.den : Rat) * v

theorem dif_eval {x : Nat → Rat} {la lb : LF} {va vb : Rat} (ha : Rep x la va) (hb : Rep x lb vb) :
    evalQ (dif la lb) x = ((la.den : Rat) * lb.den) * (va - vb) := by
  simp only [dif, evalQ_lsub, evalQ_lscale, ha.2, hb.2, Rat.intCast_natCast]; grind

theorem den_pos {la lb : LF} {va vb : Rat} {x : Nat → Rat} (ha : Rep x la va) (hb : Rep x lb vb) :
    (0 : Rat) < (la.den : Rat) * lb.den :=
  Rat.mul_pos (Rat.natCast_pos.mpr ha.1) (Rat.natCast_pos.mpr hb.1)

theorem dif_le {x : Nat → Rat} {la lb : LF} {va vb : Rat} (ha : Rep x la va) (hb : Rep x lb vb) :
    evalQ (dif la lb) x ≤ 0 ↔ va ≤ vb := by
  rw [dif_eval ha hb, mul_nonpos_iff (den_pos ha hb)]; grind
theorem dif_lt {x : Nat → Rat} {la lb : LF} {va vb : Rat} (ha : Rep x la va) (hb : Rep x lb vb) :
    evalQ (dif la lb) x < 0 ↔ va < vb := by
  rw [dif_eval ha hb, mul_neg_iff (den_pos ha hb)]; grind

theorem dec_sound {path : Path} {x : Nat → Rat} (hP : PathHolds path x) {l : Row} {b : Bool}
    (h : dec path l = some b) : decide (evalQ l x ≤ 0) = b := by
  simp only [dec] at h
  split at h
  · rename_i hz
    simp only [Option.some.injEq] at h
    subst h
    have hv : evalQ l x = l.const := by simp only [evalQ, dotQ_allZero _ x hz]; grind
    rw [hv]; simp only [decide_eq_decide]
    exact ⟨fun h => Rat.intCast_nonpos.mp h, fun h => Rat.intCast_nonpos.mpr h⟩
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    have ⟨hm, hs⟩ := lookup_some ha
    rw [← hP a hm, same_evalQ hs]

theorem dec_le {path : Path} {x : Nat → Rat} (hP : PathHolds path x) {la lb : LF} {va vb : Rat}
    (ha : Rep x la va) (hb : Rep x lb vb) {b : Bool} (h : dec path (dif la lb) = some b) : decide (va ≤ vb) = b := by
  rw [← dec_sound hP h]; simp only [decide_eq_decide]; exact (dif_le ha hb).symm

section
variable {x : Nat → Rat} {path : Path}

mutual
theorem linear_sound (hP : PathHolds path x) : (e : QE) → (l : LF) → linear path e = some l → Rep x l (evalE x e)
  | .var i, l, h => by
    simp only [linear, Option.some.injEq] at h; subst h
    refine ⟨Nat.one_pos, ?_⟩
    simp only [evalQ_lunit, evalE]; grind
  | .const q, l, h => by
    simp only [linear, Option.some.injEq] at h; subst h
    exact ⟨q.den_pos, by simp only [evalQ_lconst, evalE]; exact num_eq q⟩
  | .add a b, l, h => by
    simp only [linear] at h
    split at h
    · rename_i la lb ha hb
      simp only [Option.some.injEq] at h; subst h
      have ea := linear_sound hP a la ha
      have eb := linear_sound hP b lb hb
      refine ⟨Nat.mul_pos ea.1 eb.1, ?_⟩
      simp only [evalQ_ladd, evalQ_lscale, ea.2, eb.2, evalE, Rat.intCast_natCast, Rat.natCast_mul]; grind
    · simp at h
  | .sub a b, l, h => by
    simp only [linear] at h
    split at h
    · rename_i la lb ha hb
      simp only [Option.some.injEq] at h; subst h
      have ea := linear_sound hP a la ha
      have eb := linear_sound hP b lb hb
      refine ⟨Nat.mul_pos ea.1 eb.1, ?_⟩
      simp only [dif_eval ea eb, evalE, Rat.natCast_mul]
    · simp at h
  | .mul k a, l, h => by
    simp only [linear] at h
    split at h
    · rename_i la ha
      simp only [Option.some.injEq] at h; subst h
      have ea := linear_sound hP a la ha
      refine ⟨Nat.mul_pos k.den_pos ea.1, ?_⟩
      simp only [evalQ_lscale, ea.2, evalE, Rat.natCast_mul, num_eq k]; grind
    · simp at h
  | .min a b, l, h => by
    simp only [linear] at h
    split at h
    · rename_i la lb ha hb
      have ea := linear_sound hP a la ha
      have eb := linear_sound hP b lb hb
      split at h
      · rename_i hd
        simp only [Option.some.injEq] at h; subst h
        have := dec_le hP ea eb hd
        simp only [decide_eq_true_eq] at this
        simp only [evalE, this, ite_true]; exact ea
      · rename_i hd
        simp only [Option.some.injEq] at h; subst h
        have := dec_le hP ea eb hd
        simp only [decide_eq_false_iff_not] at this
        simp only [evalE, this, ite_false]; exact eb
      · simp at h
    · simp at h
  | .max a b, l, h => by
    simp only [linear] at h
    split at h
    · rename_i la lb ha hb
      have ea := linear_sound hP a la ha
      have eb := linear_sound hP b lb hb
      split at h
      · rename_i hd
        simp only [Option.some.injEq] at h; subst h
        have := dec_le hP ea eb hd
        simp only [decide_eq_true_eq] at this
        simp only [evalE, this, ite_true]; exact eb
      · rename_i hd
        simp only [Option.some.injEq] at h; subst h
        have := dec_le hP ea eb hd
        simp only [decide_eq_false_iff_not] at this
        simp only [evalE, this, ite_false]; exact ea
      · simp at h
    · simp at h
  | .ite c t f, l, h => by
    simp only [linear] at h
    split at h
    · rename_i hc
      simp only [evalE, truth_sound hP c true hc, ite_true]; exact linear_sound hP t l h
    · rename_i hc
      simp only [evalE, truth_sound hP c false hc]; exact linear_sound hP f l h
    · simp at h
theorem truth_sound (hP : PathHolds path x) : (c : QC) → (b : Bool) → truth path c = some b → evalC x c = b
  | .le a b', r, h => by
    simp only [truth] at h
    split at h
    · rename_i la lb ha hb
      simp only [evalC]; exact dec_le hP (linear_sound hP a la ha) (linear_sound hP b' lb hb) h
    · simp at h
  | .lt a b', r, h => by
    simp only [truth] at h
    split at h
    · rename_i la lb ha hb
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨r', hr, rfl⟩ := h
      have := dec_le hP (linear_sound hP b' lb hb) (linear_sound hP a la ha) hr
      simp only [evalC]; rw [← this]
      cases h' : decide (evalE x b' ≤ evalE x a) <;> simp at h' <;> simp [h'] <;> grind
    · simp at h
  | .eq a b', r, h => by
    simp only [truth] at h
    split at h
    · rename_i la lb ha hb
      have ea := linear_sound hP a la ha
      have eb := linear_sound hP b' lb hb
      simp only [evalC]
      revert h
      rcases h1 : dec path (dif la lb) with _ | _ | _ <;> rcases h2 : dec path (dif lb la) with _ | _ | _ <;>
        intro h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
        first
          | (have t1 := dec_le hP ea eb h1; have t2 := dec_le hP eb ea h2
             simp only [decide_eq_true_eq, decide_eq_false_iff_not, decide_eq_decide] at t1 t2 ⊢; grind)
          | (have t1 := dec_le hP ea eb h1
             simp only [decide_eq_true_eq, decide_eq_false_iff_not, decide_eq_decide] at t1 ⊢; grind)
          | (have t2 := dec_le hP eb ea h2
             simp only [decide_eq_true_eq, decide_eq_false_iff_not, decide_eq_decide] at t2 ⊢; grind)
    · simp at h
  | .and a b', r, h => by
    simp only [truth] at h
    simp only [evalC]
    split at h
    · rename_i h1; simp only [Option.some.injEq] at h; subst h; simp [truth_sound hP a false h1]
    · rename_i h2 _; simp only [Option.some.injEq] at h; subst h; simp [truth_sound hP b' false h2]
    · rename_i h1 h2; simp only [Option.some.injEq] at h; subst h; simp [truth_sound hP a true h1, truth_sound hP b' true h2]
    · simp at h
  | .or a b', r, h => by
    simp only [truth] at h
    simp only [evalC]
    split at h
    · rename_i h1; simp only [Option.some.injEq] at h; subst h; simp [truth_sound hP a true h1]
    · rename_i h2 _; simp only [Option.some.injEq] at h; subst h; simp [truth_sound hP b' true h2]
    · rename_i h1 h2; simp only [Option.some.injEq] at h; subst h; simp [truth_sound hP a false h1, truth_sound hP b' false h2]
    · simp at h
  | .not a, r, h => by
    simp only [truth, Option.map_eq_some_iff] at h
    obtain ⟨r', h1, rfl⟩ := h
    simp [evalC, truth_sound hP a r' h1]
end

theorem facts_sound (hP : PathHolds path x) : (pos : Bool) → (c : QC) → evalC x c = pos → ∀ r ∈ facts path pos c, Holds x r
  | pos, .not a, h, r, hr => by
    simp only [facts] at hr
    exact facts_sound hP (!pos) a (by simp only [evalC] at h; cases pos <;> simp_all) r hr
  | pos, .and a b, h, r, hr => by
    simp only [facts] at hr
    simp only [evalC] at h
    split at hr
    · rename_i hp; subst hp
      simp only [Bool.and_eq_true] at h
      rcases List.mem_append.mp hr with hr | hr
      · exact facts_sound hP true a h.1 r hr
      · exact facts_sound hP true b h.2 r hr
    · rename_i hp
      simp only [Bool.not_eq_true] at hp; subst hp
      split at hr
      · rename_i ht; have := truth_sound hP a true ht
        exact facts_sound hP false b (by simp_all) r hr
      · split at hr
        · rename_i _ ht; have := truth_sound hP b true ht
          exact facts_sound hP false a (by simp_all) r hr
        · simp at hr
  | pos, .or a b, h, r, hr => by
    simp only [facts] at hr
    simp only [evalC] at h
    split at hr
    · rename_i hp
      simp only [Bool.not_eq_true'] at hp; subst hp
      simp only [Bool.or_eq_false_iff] at h
      rcases List.mem_append.mp hr with hr | hr
      · exact facts_sound hP false a h.1 r hr
      · exact facts_sound hP false b h.2 r hr
    · rename_i hp
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hp; subst hp
      split at hr
      · rename_i ht; have := truth_sound hP a false ht
        exact facts_sound hP true b (by simp_all) r hr
      · split at hr
        · rename_i _ ht; have := truth_sound hP b false ht
          exact facts_sound hP true a (by simp_all) r hr
        · simp at hr
  | pos, .le a b, h, r, hr => by
    simp only [facts] at hr
    split at hr
    · rename_i la lb ha hb
      have ea := linear_sound hP a la ha
      have eb := linear_sound hP b lb hb
      simp only [evalC] at h
      cases pos
      · simp only [Bool.false_eq_true, ite_false, List.mem_singleton] at hr; subst hr
        simp only [decide_eq_false_iff_not] at h
        unfold Holds; simp only [ite_true]; exact (dif_lt eb ea).mpr (by grind)
      · simp only [ite_true, List.mem_singleton] at hr; subst hr
        simp only [decide_eq_true_eq] at h
        unfold Holds; simp only [Bool.false_eq_true, ite_false]; exact (dif_le ea eb).mpr h
    · simp at hr
  | pos, .lt a b, h, r, hr => by
    simp only [facts] at hr
    split at hr
    · rename_i la lb ha hb
      have ea := linear_sound hP a la ha
      have eb := linear_sound hP b lb hb
      simp only [evalC] at h
      cases pos
      · simp only [Bool.false_eq_true, ite_false, List.mem_singleton] at hr; subst hr
        simp only [decide_eq_false_iff_not] at h
        unfold Holds; simp only [Bool.false_eq_true, ite_false]; exact (dif_le eb ea).mpr (by grind)
      · simp only [ite_true, List.mem_singleton] at hr; subst hr
        simp only [decide_eq_true_eq] at h
        unfold Holds; simp only [ite_true]; exact (dif_lt ea eb).mpr h
    · simp at hr
  | pos, .eq a b, h, r, hr => by
    simp only [facts] at hr
    split at hr
    · rename_i la lb ha hb
      have ea := linear_sound hP a la ha
      have eb := linear_sound hP b lb hb
      simp only [evalC] at h
      cases pos
      · simp only [decide_eq_false_iff_not] at h
        simp only [Bool.false_eq_true, ite_false] at hr
        split at hr
        · rename_i hd
          simp only [List.mem_singleton] at hr; subst hr
          have := dec_le hP ea eb hd; simp only [decide_eq_true_eq] at this
          unfold Holds; simp only [ite_true]; exact (dif_lt ea eb).mpr (by grind)
        · split at hr
          · rename_i _ hd
            simp only [List.mem_singleton] at hr; subst hr
            have := dec_le hP eb ea hd; simp only [decide_eq_true_eq] at this
            unfold Holds; simp only [ite_true]; exact (dif_lt eb ea).mpr (by grind)
          · simp at hr
      · simp only [decide_eq_true_eq] at h
        simp only [ite_true, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
        unfold Holds
        rcases hr with rfl | rfl
        · simp only [Bool.false_eq_true, ite_false]; exact (dif_le ea eb).mpr (by grind)
        · simp only [Bool.false_eq_true, ite_false]; exact (dif_le eb ea).mpr (by grind)
    · simp at hr

theorem atomRow_holds (hP : PathHolds path x) : ∀ a ∈ path, Holds x (atomRow a) := by
  intro a ha
  have := hP a ha
  unfold atomRow Holds
  cases hb : a.2
  · simp only [hb, decide_eq_false_iff_not] at this
    simp only [Bool.false_eq_true, ite_false, ite_true, evalQ_lscale]; grind
  · simp only [hb, decide_eq_true_eq] at this
    simp only [ite_true, Bool.false_eq_true, ite_false]; exact this

theorem leafRows_sound (hP : PathHolds path x) {hyps : List QC} (hH : ∀ c ∈ hyps, evalC x c = true) :
    ∀ r ∈ leafRows path hyps, Holds x r := by
  intro r hr
  simp only [leafRows, List.mem_append, List.mem_map, List.mem_flatMap] at hr
  rcases hr with ⟨a, ha, rfl⟩ | ⟨c, hc, hr⟩
  · exact atomRow_holds hP a ha
  · exact facts_sound hP true c (hH c hc) r hr

theorem claim_holds {rows : List (Row × Bool)} (hrows : ∀ q ∈ rows, Holds x q) {r : Row × Bool}
    (h : claimOk rows r = true) : Holds x r := by
  simp only [claimOk, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨q, hq, hs, hst⟩ := h
  have hq' := hrows q hq
  have e := same_evalQ hs x
  unfold Holds at hq' ⊢
  rw [← e]
  rcases hst with h1 | h1
  · simp only [h1, ite_true] at hq'
    split
    · exact hq'
    · exact Rat.le_of_lt hq'
  · simp only [h1, Bool.false_eq_true, ite_false]
    split at hq'
    · exact Rat.le_of_lt hq'
    · exact hq'
end

theorem checkT_sound {x : Nat → Rat} {hyps : List QC} (hH : ∀ c ∈ hyps, evalC x c = true) :
    ∀ (t : QTree) (path : Path), PathHolds path x → checkT hyps path t = true → False
  | .leaf rows steps, path, hP, h => by
    simp only [checkT, Bool.and_eq_true, List.all_eq_true] at h
    exact checkQ_sound rows steps h.2 x (fun r hr => claim_holds (leafRows_sound hP hH) (h.1 r hr))
  | .split l yes no, path, hP, h => by
    simp only [checkT, Bool.and_eq_true] at h
    by_cases hl : evalQ l x ≤ 0
    · refine checkT_sound hH yes ((l, true) :: path) ?_ h.1.2
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [hl]
      · exact hP a ha
    · refine checkT_sound hH no ((l, false) :: path) ?_ h.2
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [hl]
      · exact hP a ha

/-- The tree check is sound: an accepted goal's hypotheses hold together at no rational point. -/
theorem sound (hyps : List QC) (t : QTree) (h : checkGoal hyps t = true) (x : Nat → Rat) :
    ¬ (∀ c ∈ hyps, evalC x c = true) :=
  fun hH => checkT_sound hH t [] (by simp [PathHolds]) h

/-! Step machines over the rationals: the induction rule over these goals, built here in Lean from the machine (as
Kernel.lean's `checkMachine`), so the TypeScript obligations are not trusted. A law holds at the start (`startGoal` is
refuted) and one step keeps every law (`stepGoal` is refuted, assuming them all and the request's assumption), so every
law holds in every reachable state. Laws may not read the request's inputs. -/

def assoc (σ : List (Nat × QE)) (i : Nat) : Option QE := (lookup (fun p => p.1 == i) σ).map (·.2)

mutual
def substE (σ : List (Nat × QE)) : QE → QE
  | .var i => match assoc σ i with
    | some e => e
    | none => .var i
  | .const q => .const q
  | .add a b => .add (substE σ a) (substE σ b)
  | .sub a b => .sub (substE σ a) (substE σ b)
  | .mul k a => .mul k (substE σ a)
  | .min a b => .min (substE σ a) (substE σ b)
  | .max a b => .max (substE σ a) (substE σ b)
  | .ite c t f => .ite (substC σ c) (substE σ t) (substE σ f)
def substC (σ : List (Nat × QE)) : QC → QC
  | .le a b => .le (substE σ a) (substE σ b)
  | .lt a b => .lt (substE σ a) (substE σ b)
  | .eq a b => .eq (substE σ a) (substE σ b)
  | .and a b => .and (substC σ a) (substC σ b)
  | .or a b => .or (substC σ a) (substC σ b)
  | .not a => .not (substC σ a)
end

-- The environment after σ: each assigned variable takes its term's value, the rest keep theirs.
def applyS (σ : List (Nat × QE)) (ρ : Nat → Rat) : Nat → Rat :=
  fun i => match assoc σ i with
    | some e => evalE ρ e
    | none => ρ i

mutual
theorem subst_evalE (σ : List (Nat × QE)) (ρ : Nat → Rat) : (e : QE) → evalE ρ (substE σ e) = evalE (applyS σ ρ) e
  | .var i => by
    simp only [substE]
    cases h : assoc σ i <;> simp [evalE, applyS, h]
  | .const q => by simp [substE, evalE]
  | .add a b => by simp [substE, evalE, subst_evalE σ ρ a, subst_evalE σ ρ b]
  | .sub a b => by simp [substE, evalE, subst_evalE σ ρ a, subst_evalE σ ρ b]
  | .mul k a => by simp [substE, evalE, subst_evalE σ ρ a]
  | .min a b => by simp [substE, evalE, subst_evalE σ ρ a, subst_evalE σ ρ b]
  | .max a b => by simp [substE, evalE, subst_evalE σ ρ a, subst_evalE σ ρ b]
  | .ite c t f => by simp [substE, evalE, subst_evalC σ ρ c, subst_evalE σ ρ t, subst_evalE σ ρ f]
theorem subst_evalC (σ : List (Nat × QE)) (ρ : Nat → Rat) : (c : QC) → evalC ρ (substC σ c) = evalC (applyS σ ρ) c
  | .le a b => by simp [substC, evalC, subst_evalE σ ρ a, subst_evalE σ ρ b]
  | .lt a b => by simp [substC, evalC, subst_evalE σ ρ a, subst_evalE σ ρ b]
  | .eq a b => by simp [substC, evalC, subst_evalE σ ρ a, subst_evalE σ ρ b]
  | .and a b => by simp [substC, evalC, subst_evalC σ ρ a, subst_evalC σ ρ b]
  | .or a b => by simp [substC, evalC, subst_evalC σ ρ a, subst_evalC σ ρ b]
  | .not a => by simp [substC, evalC, subst_evalC σ ρ a]
end

mutual
def occE (i : Nat) : QE → Bool
  | .var j => j == i
  | .const _ => false
  | .add a b => occE i a || occE i b
  | .sub a b => occE i a || occE i b
  | .mul _ a => occE i a
  | .min a b => occE i a || occE i b
  | .max a b => occE i a || occE i b
  | .ite c t f => occC i c || occE i t || occE i f
def occC (i : Nat) : QC → Bool
  | .le a b => occE i a || occE i b
  | .lt a b => occE i a || occE i b
  | .eq a b => occE i a || occE i b
  | .and a b => occC i a || occC i b
  | .or a b => occC i a || occC i b
  | .not a => occC i a
end

mutual
theorem congrE (ρ ρ' : Nat → Rat) : (e : QE) → (∀ i, occE i e = true → ρ i = ρ' i) → evalE ρ e = evalE ρ' e
  | .var j, h => by simp only [evalE]; exact h j (by simp [occE])
  | .const _, _ => rfl
  | .add a b, h => by
    simp only [evalE, congrE ρ ρ' a (fun i hi => h i (by simp [occE, hi])), congrE ρ ρ' b (fun i hi => h i (by simp [occE, hi]))]
  | .sub a b, h => by
    simp only [evalE, congrE ρ ρ' a (fun i hi => h i (by simp [occE, hi])), congrE ρ ρ' b (fun i hi => h i (by simp [occE, hi]))]
  | .mul k a, h => by simp only [evalE, congrE ρ ρ' a (fun i hi => h i (by simp [occE, hi]))]
  | .min a b, h => by
    simp only [evalE, congrE ρ ρ' a (fun i hi => h i (by simp [occE, hi])), congrE ρ ρ' b (fun i hi => h i (by simp [occE, hi]))]
  | .max a b, h => by
    simp only [evalE, congrE ρ ρ' a (fun i hi => h i (by simp [occE, hi])), congrE ρ ρ' b (fun i hi => h i (by simp [occE, hi]))]
  | .ite c t f, h => by
    simp only [evalE, congrC ρ ρ' c (fun i hi => h i (by simp [occE, hi])), congrE ρ ρ' t (fun i hi => h i (by simp [occE, hi])),
      congrE ρ ρ' f (fun i hi => h i (by simp [occE, hi]))]
theorem congrC (ρ ρ' : Nat → Rat) : (c : QC) → (∀ i, occC i c = true → ρ i = ρ' i) → evalC ρ c = evalC ρ' c
  | .le a b, h => by
    simp only [evalC, congrE ρ ρ' a (fun i hi => h i (by simp [occC, hi])), congrE ρ ρ' b (fun i hi => h i (by simp [occC, hi]))]
  | .lt a b, h => by
    simp only [evalC, congrE ρ ρ' a (fun i hi => h i (by simp [occC, hi])), congrE ρ ρ' b (fun i hi => h i (by simp [occC, hi]))]
  | .eq a b, h => by
    simp only [evalC, congrE ρ ρ' a (fun i hi => h i (by simp [occC, hi])), congrE ρ ρ' b (fun i hi => h i (by simp [occC, hi]))]
  | .and a b, h => by
    simp only [evalC, congrC ρ ρ' a (fun i hi => h i (by simp [occC, hi])), congrC ρ ρ' b (fun i hi => h i (by simp [occC, hi]))]
  | .or a b, h => by
    simp only [evalC, congrC ρ ρ' a (fun i hi => h i (by simp [occC, hi])), congrC ρ ρ' b (fun i hi => h i (by simp [occC, hi]))]
  | .not a, h => by simp only [evalC, congrC ρ ρ' a (fun i hi => h i (by simp [occC, hi]))]
end

structure Machine where
  inputs : List Nat
  init : List (Nat × QE)   -- each state variable's start, over the params
  step : List (Nat × QE)   -- each state variable after a request, over params, inputs and state
  pre : QC                 -- about the params alone: a precondition, so it holds at the start and at every step
  assume : QC              -- about each request (and the params); holds at a step, not at the start

-- A request: its inputs replace those variables; nothing else changes until the step.
def withInputs (inputs : List Nat) (ρ ι : Nat → Rat) : Nat → Rat := fun i => if inputs.contains i then ι i else ρ i

inductive Reach (m : Machine) : (Nat → Rat) → Prop
  | start (ρ : Nat → Rat) : evalC ρ m.pre = true → Reach m (applyS m.init ρ)
  | step (ρ ι : Nat → Rat) : Reach m ρ → evalC (withInputs m.inputs ρ ι) m.assume = true →
      Reach m (applyS m.step (withInputs m.inputs ρ ι))

def startGoal (m : Machine) (law : QC) : List QC := [m.pre, .not (substC m.init law)]
def stepGoal (m : Machine) (laws : List QC) (law : QC) : List QC := [m.pre, m.assume] ++ laws ++ [.not (substC m.step law)]

-- Per law: the law, then the trees of its start goal and of its step goal.
abbrev MachineProof := List (QC × QTree × QTree)

def avoids (vs : List Nat) (c : QC) : Bool := vs.all fun i => !occC i c
-- The precondition reads only params: no input, no variable the start or a step assigns.
def preOk (m : Machine) : Bool := avoids (m.inputs ++ m.init.map (·.1) ++ m.step.map (·.1)) m.pre

def checkMachine (m : Machine) (ps : MachineProof) : Bool :=
  preOk m && ps.all fun p => avoids m.inputs p.1
    && checkGoal (startGoal m p.1) p.2.1
    && checkGoal (stepGoal m (ps.map (·.1)) p.1) p.2.2

theorem avoids_occ {vs : List Nat} {c : QC} (h : avoids vs c = true) {i : Nat} (hi : occC i c = true) : i ∉ vs := by
  intro hm
  simp only [avoids, List.all_eq_true] at h
  have := h i hm; simp [hi] at this

theorem assoc_mem {σ : List (Nat × QE)} {i : Nat} {e : QE} (h : assoc σ i = some e) : i ∈ σ.map (·.1) := by
  simp only [assoc, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, _⟩ := h
  have ⟨hm, hp⟩ := lookup_some ha
  simp only [beq_iff_eq] at hp
  exact List.mem_map.mpr ⟨a, hm, hp⟩

theorem applyS_other {σ : List (Nat × QE)} {i : Nat} (h : i ∉ σ.map (·.1)) (ρ : Nat → Rat) : applyS σ ρ i = ρ i := by
  simp only [applyS]
  cases ha : assoc σ i with
  | none => rfl
  | some e => exact absurd (assoc_mem ha) h

theorem withInputs_other {inputs : List Nat} {i : Nat} (h : i ∉ inputs) (ρ ι : Nat → Rat) : withInputs inputs ρ ι i = ρ i := by
  simp only [withInputs]; split
  · rename_i hc; exact absurd (List.contains_iff_mem.mp hc) h
  · rfl

theorem evalC_avoids {vs : List Nat} {c : QC} (h : avoids vs c = true) {ρ ρ' : Nat → Rat}
    (hρ : ∀ i, i ∉ vs → ρ i = ρ' i) : evalC ρ c = evalC ρ' c :=
  congrC ρ ρ' c (fun i hi => hρ i (avoids_occ h hi))

theorem pre_reach {m : Machine} (hp : preOk m = true) : ∀ {ρ}, Reach m ρ → evalC ρ m.pre = true := by
  intro ρ hr
  induction hr with
  | start ρ h0 =>
    rw [evalC_avoids hp (ρ' := ρ) (fun i hi => applyS_other (fun h => hi (by simp [h])) ρ)]; exact h0
  | step ρ ι _ _ ih =>
    rw [evalC_avoids hp (ρ' := ρ) (fun i hi => by
      rw [applyS_other (fun h => hi (by simp [h])), withInputs_other (fun h => hi (by simp [h]))])]; exact ih

/-- The induction rule over the rationals: for params that meet the precondition, every law of an accepted machine
proof holds in every reachable state. -/
theorem machine_sound (m : Machine) (ps : MachineProof) (h : checkMachine m ps = true) :
    ∀ ρ, Reach m ρ → ∀ l ∈ ps.map (·.1), evalC ρ l = true := by
  simp only [checkMachine, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨hpre, h⟩ := h
  intro ρ hr
  induction hr with
  | start ρ h0 =>
    intro l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    have hs := sound _ _ (h p hp).1.2 ρ
    apply Decidable.byContradiction
    intro hf
    apply hs
    intro c hc
    simp only [startGoal, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact h0
    · simp only [evalC, subst_evalC]; simpa using hf
  | step ρ ι hr ha ih =>
    intro l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    have hs := sound _ _ (h p hp).2 (withInputs m.inputs ρ ι)
    apply Decidable.byContradiction
    intro hf
    apply hs
    intro c hc
    simp only [stepGoal, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl) | hc) | rfl
    · rw [evalC_avoids hpre (ρ' := ρ) (fun i hi => withInputs_other (fun h => hi (by simp [h])) ρ ι)]
      exact pre_reach hpre hr
    · exact ha
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
      rw [evalC_avoids (h q hq).1.1 (ρ' := ρ) (fun i hi => withInputs_other hi ρ ι)]
      exact ih q.1 (List.mem_map.mpr ⟨q, hq, rfl⟩)
    · simp only [evalC, subst_evalC]; simpa using hf

#print axioms checkQ_sound
#print axioms sound
#print axioms machine_sound

end Q

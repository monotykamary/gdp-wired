import Cert
/-!
Kernel: the Lean twin of gdp-wired's kernel/kernel.ts tree check, with its soundness proof. Lean 4.34.0, core only.

A goal is a variable table and hypotheses over naturals (+, ∸, × by a constant, min, max, if, map reads; ≤, <, =,
and, or, not). A proof is a tree of splits on linear atoms, with a leaf certificate: the rows it claims, a Cert
derivation over them, and the pairs of cells it claims equal. At a leaf the twin computes the rows the path, the
hypotheses' facts, the naturals and the verified cell equalities give, checks every claimed row is one of them, and
replays the derivation with `Cert.check`. `sound`: if `checkGoal` accepts, no naturals and no maps satisfy every
hypothesis.

The table names what each column of a row is: a variable of the environment, or a map's cell at a key (a row over
earlier columns). Rows compare by coefficients (`same`), so the exporter's ordering doesn't matter.
-/

namespace Kern
open Cert
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

mutual
inductive E where
  | var (i : Nat)
  | const (n : Nat)
  | add (a b : E)
  | sub (a b : E)
  | mul (k : Nat) (a : E)
  | min (a b : E)
  | max (a b : E)
  | prod (a b : E)
  | ite (c : C) (t f : E)
  | get (m : Nat) (key : E)
inductive C where
  | le (a b : E)
  | lt (a b : E)
  | eq (a b : E)
  | and (a b : C)
  | or (a b : C)
  | not (a : C)
end

deriving instance DecidableEq for E, C

mutual
def evalE (env : Nat → Nat) (maps : Nat → Nat → Nat) : E → Nat
  | .var i => env i
  | .const n => n
  | .add a b => evalE env maps a + evalE env maps b
  | .sub a b => evalE env maps a - evalE env maps b
  | .mul k a => k * evalE env maps a
  | .min a b => min (evalE env maps a) (evalE env maps b)
  | .max a b => max (evalE env maps a) (evalE env maps b)
  | .prod a b => evalE env maps a * evalE env maps b
  | .ite c t f => if evalC env maps c then evalE env maps t else evalE env maps f
  | .get m key => maps m (evalE env maps key)
def evalC (env : Nat → Nat) (maps : Nat → Nat → Nat) : C → Bool
  | .le a b => decide (evalE env maps a ≤ evalE env maps b)
  | .lt a b => decide (evalE env maps a < evalE env maps b)
  | .eq a b => decide (evalE env maps a = evalE env maps b)
  | .and a b => evalC env maps a && evalC env maps b
  | .or a b => evalC env maps a || evalC env maps b
  | .not a => !evalC env maps a
end

-- A condition's meaning as a proposition: what a law says in plain Lean (`evalC_iff`). Exported laws are stated with it,
-- so a statement like `ρ x ≤ ρ cap` is the law itself, up to unfolding.
def holdsC (env : Nat → Nat) (maps : Nat → Nat → Nat) : C → Prop
  | .le a b => evalE env maps a ≤ evalE env maps b
  | .lt a b => evalE env maps a < evalE env maps b
  | .eq a b => evalE env maps a = evalE env maps b
  | .and a b => holdsC env maps a ∧ holdsC env maps b
  | .or a b => holdsC env maps a ∨ holdsC env maps b
  | .not a => ¬ holdsC env maps a

theorem evalC_iff (env : Nat → Nat) (maps : Nat → Nat → Nat) : ∀ c, evalC env maps c = true ↔ holdsC env maps c
  | .le a b => by simp [evalC, holdsC]
  | .lt a b => by simp [evalC, holdsC]
  | .eq a b => by simp [evalC, holdsC]
  | .and a b => by simp [evalC, holdsC, evalC_iff env maps a, evalC_iff env maps b]
  | .or a b => by simp [evalC, holdsC, evalC_iff env maps a, evalC_iff env maps b]
  | .not a => by
    have h := evalC_iff env maps a
    simp only [evalC, holdsC]
    cases hb : evalC env maps a <;> simp_all

/-! Linear forms are Cert rows: `eval r x = dot r.coefs x + r.const`. -/

def lconst (n : Int) : Row := ⟨[], n⟩
def ladd (a b : Row) : Row := ⟨addL a.coefs b.coefs, a.const + b.const⟩
def lscale (m : Int) (a : Row) : Row := ⟨scaleL m a.coefs, m * a.const⟩
def lsub (a b : Row) : Row := ladd a (lscale (-1) b)
def unitL : Nat → List Int
  | 0 => [1]
  | j + 1 => 0 :: unitL j
def lunit (j : Nat) : Row := ⟨unitL j, 0⟩
-- Coefficients by their nonzero entries (column, coefficient), in order: how the exporters write rows, to keep a
-- certificate small. It builds the dense list a row holds (any list of pairs builds some row, which the check reads).
def sparseL : Nat → List (Nat × Int) → List Int
  | _, [] => []
  | i, (j, c) :: rest => List.replicate (j - i) 0 ++ c :: sparseL (j + 1) rest
def sp (cs : List (Nat × Int)) (c : Int) : Row := ⟨sparseL 0 cs, c⟩
def same (a b : Row) : Bool := allZero (lsub a b).coefs && (lsub a b).const == 0
-- 1 − a: over the integers, a ≤ 0 fails exactly when 1 − a ≤ 0 holds.
def flip (a : Row) : Row := lsub (lconst 1) a

theorem eval_lconst (n : Int) (x : List Int) : eval (lconst n) x = n := by
  cases x <;> simp [eval, lconst, dot]
theorem eval_ladd (a b : Row) (x : List Int) : eval (ladd a b) x = eval a x + eval b x := by
  simp only [eval, ladd, dot_addL]; omega
theorem eval_lscale (m : Int) (a : Row) (x : List Int) : eval (lscale m a) x = m * eval a x := by
  simp only [eval, lscale, dot_scaleL, Int.mul_add]
theorem eval_lsub (a b : Row) (x : List Int) : eval (lsub a b) x = eval a x - eval b x := by
  simp only [lsub, eval_ladd, eval_lscale]; omega
theorem eval_flip (a : Row) (x : List Int) : eval (flip a) x = 1 - eval a x := by
  simp only [flip, eval_lsub, eval_lconst]
theorem dot_unitL : ∀ (j : Nat) (x : List Int), dot (unitL j) x = x.getD j 0
  | 0, [] => rfl
  | 0, y :: ys => by simp [unitL, dot]
  | _ + 1, [] => rfl
  | j + 1, y :: ys => by simp [unitL, dot, dot_unitL j ys]
theorem eval_lunit (j : Nat) (x : List Int) : eval (lunit j) x = x.getD j 0 := by
  simp [eval, lunit, dot_unitL]
theorem same_eval {a b : Row} (h : same a b = true) (x : List Int) : eval a x = eval b x := by
  simp only [same, Bool.and_eq_true, beq_iff_eq] at h
  have h1 : eval (lsub a b) x = 0 := by simp only [eval, dot_allZero _ x h.1, h.2]; rfl
  rw [eval_lsub] at h1; omega

/-! The path: atoms decided so far. `(l, true)` says l ≤ 0, `(l, false)` says l ≥ 1. -/

abbrev Path := List (Row × Bool)
def PathHolds (path : Path) (x : List Int) : Prop := ∀ a ∈ path, decide (eval a.1 x ≤ 0) = a.2

def lookup {α : Type} (p : α → Bool) : List α → Option α
  | [] => none
  | a :: as => if p a then some a else lookup p as
theorem lookup_some {α : Type} {p : α → Bool} : ∀ {l : List α} {a : α}, lookup p l = some a → a ∈ l ∧ p a = true
  | [], _, h => by simp [lookup] at h
  | b :: bs, a, h => by
    simp only [lookup] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact ⟨List.mem_cons_self, by assumption⟩
    · have := lookup_some h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

def dec (path : Path) (l : Row) : Option Bool :=
  if allZero l.coefs then some (decide (l.const ≤ 0))
  else match lookup (fun a => same a.1 l) path with
    | some a => some a.2
    | none => match lookup (fun a => same a.1 (flip l)) path with
      | some a => some (!a.2)
      | none => none

theorem dec_sound {path : Path} {x : List Int} (hP : PathHolds path x) {l : Row} {b : Bool}
    (h : dec path l = some b) : decide (eval l x ≤ 0) = b := by
  simp only [dec] at h
  split at h
  · rename_i hz
    simp only [Option.some.injEq] at h
    subst h
    simp [eval, dot_allZero _ x hz]
  · split at h
    · rename_i a ha
      simp only [Option.some.injEq] at h; subst h
      have ⟨hm, hs⟩ := lookup_some ha
      rw [← hP a hm, same_eval hs]
    · split at h
      · rename_i a ha
        simp only [Option.some.injEq] at h; subst h
        have ⟨hm, hs⟩ := lookup_some ha
        have := hP a hm
        rw [same_eval hs, eval_flip] at this
        rw [← this]
        by_cases hl : eval l x ≤ 0 <;> simp [hl] <;> omega
      · simp at h

/-! The table: column j is a variable of the environment, or map m's cell at a key (a row over earlier columns). -/

inductive VDef where
  | var (i : Nat)
  | cell (m : Nat) (key : Row)
  | mono (fs : List Nat)        -- the product of earlier columns (a monomial)
  | term (e : E)                -- a choice the path leaves open (∸, min, max, if), standing for its value

def prodV (x : List Int) : List Nat → Int
  | [] => 1
  | j :: js => x.getD j 0 * prodV x js

def valD (env : Nat → Nat) (maps : Nat → Nat → Nat) : VDef → List Int → Int
  | .var i, _ => (env i : Int)
  | .cell m k, x => (maps m (eval k x).toNat : Int)
  | .mono fs, x => ((prodV x fs).toNat : Int)
  | .term e, _ => (evalE env maps e : Int)

-- x is a valuation of the table: each column holds what its definition says, and every value is a natural.
def Model (tab : List VDef) (env : Nat → Nat) (maps : Nat → Nat → Nat) (x : List Int) : Prop :=
  (∀ j d, tab[j]? = some d → x.getD j 0 = valD env maps d x) ∧ ∀ j, 0 ≤ x.getD j 0

def findIdx {α : Type} (p : α → Bool) : List α → Option Nat
  | [] => none
  | a :: as => if p a then some 0 else (findIdx p as).map (· + 1)
theorem findIdx_some {α : Type} {p : α → Bool} : ∀ {l : List α} {j : Nat}, findIdx p l = some j → ∃ a, l[j]? = some a ∧ p a = true
  | [], _, h => by simp [findIdx] at h
  | b :: bs, j, h => by
    simp only [findIdx] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact ⟨b, rfl, by assumption⟩
    · cases hj : findIdx p bs with
      | none => simp [hj] at h
      | some i =>
        simp only [hj, Option.map_some, Option.some.injEq] at h; subst h
        obtain ⟨a, ha, hp⟩ := findIdx_some (l := bs) hj
        exact ⟨a, by simpa using ha, hp⟩

def isVar (i : Nat) : VDef → Bool
  | .var i' => i' == i
  | _ => false
def isCell (m : Nat) (k : Row) : VDef → Bool
  | .cell m' k' => m' == m && same k' k
  | _ => false
def isTerm (e : E) : VDef → Bool
  | .term e' => e' == e
  | _ => false
-- An open choice's column: the table's column for the whole term, if it has one.
def termCol (tab : List VDef) (e : E) : Option Row := (findIdx (isTerm e) tab).map lunit
def isMono (fs : List Nat) : VDef → Bool
  | .mono fs' => fs' == fs
  | _ => false

/-! Products: monomials are columns, each the product of the columns its factors name (sorted, so one monomial is one
column). Multiplying two rows looks up the column of each product of two columns. -/

def ins (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: ins a bs
def srt : List Nat → List Nat
  | [] => []
  | a :: as => ins a (srt as)

theorem prodV_ins (x : List Int) (a : Nat) : ∀ l, prodV x (ins a l) = x.getD a 0 * prodV x l
  | [] => by simp [ins, prodV]
  | b :: bs => by
    simp only [ins]; split
    · rfl
    · simp only [prodV, prodV_ins x a bs]; rw [Int.mul_left_comm]
theorem prodV_srt (x : List Int) : ∀ l, prodV x (srt l) = prodV x l
  | [] => rfl
  | a :: as => by simp only [srt, prodV_ins, prodV_srt x as, prodV]
theorem prodV_append (x : List Int) : ∀ l1 l2, prodV x (l1 ++ l2) = prodV x l1 * prodV x l2
  | [], l2 => by simp [prodV]
  | a :: as, l2 => by simp only [List.cons_append, prodV, prodV_append x as l2, Int.mul_assoc]
theorem prodV_nonneg {x : List Int} (h : ∀ j, 0 ≤ x.getD j 0) : ∀ l, 0 ≤ prodV x l
  | [] => by simp [prodV]
  | a :: as => Int.mul_nonneg (h a) (prodV_nonneg h as)

def fac (tab : List VDef) (i : Nat) : Option (List Nat) :=
  match tab[i]? with
  | some (.var _) => some [i]
  | some (.mono fs) => some fs
  | _ => none
def pcol (tab : List VDef) (i j : Nat) : Option Nat :=
  match fac tab i, fac tab j with
  | some a, some b => findIdx (isMono (srt (a ++ b))) tab
  | _, _ => none

-- x_i · Σ_t b_t x_(j+t)
def mulRow (tab : List VDef) (i : Nat) : Nat → List Int → Option Row
  | _, [] => some (lconst 0)
  | j, b :: bs => match mulRow tab i (j + 1) bs with
    | none => none
    | some r => if b == 0 then some r else match pcol tab i j with
      | some k => some (ladd (lscale b (lunit k)) r)
      | none => none
-- (Σ_s a_s x_(i+s)) · Σ_t b_t x_t
def mulRows (tab : List VDef) (bs : List Int) : Nat → List Int → Option Row
  | _, [] => some (lconst 0)
  | i, a :: as => match mulRows tab bs (i + 1) as with
    | none => none
    | some r => if a == 0 then some r else match mulRow tab i 0 bs with
      | some q => some (ladd (lscale a q) r)
      | none => none
def rowMul (tab : List VDef) (a b : Row) : Option Row :=
  match mulRows tab b.coefs 0 a.coefs with
  | some p => some (ladd p (ladd (lscale a.const ⟨b.coefs, 0⟩) (ladd (lscale b.const ⟨a.coefs, 0⟩) (lconst (a.const * b.const)))))
  | none => none

def dotAt (x : List Int) : Nat → List Int → Int
  | _, [] => 0
  | j, b :: bs => b * x.getD j 0 + dotAt x (j + 1) bs
theorem dotAt_cons (y : Int) (ys : List Int) : ∀ j bs, dotAt (y :: ys) (j + 1) bs = dotAt ys j bs
  | _, [] => rfl
  | j, b :: bs => by simp only [dotAt, List.getD_cons_succ, dotAt_cons y ys (j + 1) bs]
theorem dotAt_nil : ∀ j bs, dotAt [] j bs = 0
  | _, [] => rfl
  | j, b :: bs => by simp [dotAt, dotAt_nil (j + 1) bs]
theorem dot_dotAt : ∀ (bs x : List Int), dot bs x = dotAt x 0 bs
  | [], x => by cases x <;> rfl
  | b :: bs, [] => by simp [dot, dotAt, dotAt_nil]
  | b :: bs, y :: ys => by simp only [dot, dotAt, List.getD_cons_zero, dotAt_cons, dot_dotAt bs ys]

mutual
def linear (tab : List VDef) (path : Path) : E → Option Row
  | .var i => (findIdx (isVar i) tab).map lunit
  | .const n => some (lconst n)
  | .add a b => match linear tab path a, linear tab path b with
    | some la, some lb => some (ladd la lb)
    | _, _ => none
  | .mul k a => match linear tab path a with
    | some la => some (lscale k la)
    | none => none
  | .sub a b => match linear tab path a, linear tab path b with
    | some la, some lb => match dec path (lsub lb la) with
      | some true => some (lsub la lb)
      | some false => some (lconst 0)
      | none => termCol tab (.sub a b)
    | _, _ => none
  | .min a b => match linear tab path a, linear tab path b with
    | some la, some lb => match dec path (lsub la lb) with
      | some true => some la
      | some false => some lb
      | none => termCol tab (.min a b)
    | _, _ => none
  | .max a b => match linear tab path a, linear tab path b with
    | some la, some lb => match dec path (lsub la lb) with
      | some true => some lb
      | some false => some la
      | none => termCol tab (.max a b)
    | _, _ => none
  | .prod a b => match linear tab path a, linear tab path b with
    | some la, some lb => rowMul tab la lb
    | _, _ => none
  | .ite c t f => match truth tab path c with
    | some true => linear tab path t
    | some false => linear tab path f
    | none => termCol tab (.ite c t f)
  | .get m key => match linear tab path key with
    | some lk => (findIdx (isCell m lk) tab).map lunit
    | none => none
def truth (tab : List VDef) (path : Path) : C → Option Bool
  | .le a b => match linear tab path a, linear tab path b with
    | some la, some lb => dec path (lsub la lb)
    | _, _ => none
  | .lt a b => match linear tab path a, linear tab path b with
    | some la, some lb => dec path (ladd (lsub la lb) (lconst 1))
    | _, _ => none
  | .eq a b => match linear tab path a, linear tab path b with
    | some la, some lb => match dec path (lsub la lb), dec path (lsub lb la) with
      | some false, _ => some false
      | _, some false => some false
      | some true, some true => some true
      | _, _ => none
    | _, _ => none
  | .and a b => match truth tab path a, truth tab path b with
    | some false, _ => some false
    | _, some false => some false
    | some true, some true => some true
    | _, _ => none
  | .or a b => match truth tab path a, truth tab path b with
    | some true, _ => some true
    | _, some true => some true
    | some false, some false => some false
    | _, _ => none
  | .not a => match truth tab path a with
    | some b => some (!b)
    | none => none
end

section
variable {tab : List VDef} {env : Nat → Nat} {maps : Nat → Nat → Nat} {x : List Int} {path : Path}

theorem var_col (hM : Model tab env maps x) {i j : Nat} (h : findIdx (isVar i) tab = some j) : x.getD j 0 = env i := by
  obtain ⟨d, hd, hv⟩ := findIdx_some h
  rw [hM.1 j d hd]
  cases d with
  | var i' => simp only [isVar, beq_iff_eq] at hv; subst hv; rfl
  | _ => simp [isVar] at hv

theorem term_col (hM : Model tab env maps x) {e : E} {j : Nat} (h : findIdx (isTerm e) tab = some j) :
    x.getD j 0 = (evalE env maps e : Int) := by
  obtain ⟨d, hd, hv⟩ := findIdx_some h
  rw [hM.1 j d hd]
  cases d with
  | term e' => simp only [isTerm, beq_iff_eq] at hv; subst hv; rfl
  | _ => simp [isTerm] at hv

theorem termCol_sound (hM : Model tab env maps x) {e : E} {l : Row} (h : termCol tab e = some l) :
    eval l x = (evalE env maps e : Int) := by
  simp only [termCol] at h
  cases hj : findIdx (isTerm e) tab with
  | none => simp [hj] at h
  | some j => simp only [hj, Option.map_some, Option.some.injEq] at h; subst h; rw [eval_lunit, term_col hM hj]

theorem cell_col (hM : Model tab env maps x) {m j : Nat} {k : Row} (h : findIdx (isCell m k) tab = some j) :
    x.getD j 0 = (maps m (eval k x).toNat : Int) := by
  obtain ⟨d, hd, hv⟩ := findIdx_some h
  rw [hM.1 j d hd]
  cases d with
  | cell m' k' =>
    simp only [isCell, Bool.and_eq_true, beq_iff_eq] at hv
    obtain ⟨rfl, hs⟩ := hv
    simp only [valD, same_eval hs x]
  | _ => simp [isCell] at hv

theorem fac_val (hM : Model tab env maps x) {i : Nat} {fs : List Nat} (h : fac tab i = some fs) : x.getD i 0 = prodV x fs := by
  simp only [fac] at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; simp [prodV]
  · rename_i fs' hd
    simp only [Option.some.injEq] at h; subst h
    rw [hM.1 i _ hd]; simp only [valD]; exact Int.toNat_of_nonneg (prodV_nonneg hM.2 _)
  · simp at h

theorem pcol_val (hM : Model tab env maps x) {i j k : Nat} (h : pcol tab i j = some k) :
    x.getD k 0 = x.getD i 0 * x.getD j 0 := by
  simp only [pcol] at h
  split at h
  · rename_i a b ha hb
    obtain ⟨d, hd, hv⟩ := findIdx_some h
    cases d with
    | mono fs =>
      simp only [isMono, beq_iff_eq] at hv; subst hv
      rw [hM.1 k _ hd]; simp only [valD]
      rw [Int.toNat_of_nonneg (prodV_nonneg hM.2 _), prodV_srt, prodV_append, ← fac_val hM ha, ← fac_val hM hb]
    | _ => simp [isMono] at hv
  · simp at h

theorem mulRow_sound (hM : Model tab env maps x) (i : Nat) :
    ∀ j bs r, mulRow tab i j bs = some r → eval r x = x.getD i 0 * dotAt x j bs
  | _, [], r, h => by simp only [mulRow, Option.some.injEq] at h; subst h; simp [eval_lconst, dotAt]
  | j, b :: bs, r, h => by
    simp only [mulRow] at h
    split at h
    · simp at h
    · rename_i r' hr'
      have ih := mulRow_sound hM i (j + 1) bs r' hr'
      split at h
      · rename_i hb
        simp only [Option.some.injEq] at h; subst h
        simp only [beq_iff_eq] at hb; subst hb; simp [dotAt, ih]
      · split at h
        · rename_i k hk
          simp only [Option.some.injEq] at h; subst h
          rw [eval_ladd, eval_lscale, eval_lunit, pcol_val hM hk, ih]
          simp only [dotAt]; rw [Int.mul_add, Int.mul_left_comm (x.getD i 0) b]
        · simp at h

theorem mulRows_sound (hM : Model tab env maps x) (bs : List Int) :
    ∀ i as r, mulRows tab bs i as = some r → eval r x = dotAt x i as * dotAt x 0 bs
  | _, [], r, h => by simp only [mulRows, Option.some.injEq] at h; subst h; simp [eval_lconst, dotAt]
  | i, a :: as, r, h => by
    simp only [mulRows] at h
    split at h
    · simp at h
    · rename_i r' hr'
      have ih := mulRows_sound hM bs (i + 1) as r' hr'
      split at h
      · rename_i ha
        simp only [Option.some.injEq] at h; subst h
        simp only [beq_iff_eq] at ha; subst ha; simp [dotAt, ih]
      · split at h
        · rename_i q hq
          simp only [Option.some.injEq] at h; subst h
          rw [eval_ladd, eval_lscale, mulRow_sound hM i 0 bs q hq, ih]
          simp only [dotAt]; rw [Int.add_mul, Int.mul_assoc]
        · simp at h

theorem rowMul_sound (hM : Model tab env maps x) {a b r : Row} (h : rowMul tab a b = some r) : eval r x = eval a x * eval b x := by
  simp only [rowMul] at h
  split at h
  · rename_i p hp
    simp only [Option.some.injEq] at h; subst h
    have e := mulRows_sound hM b.coefs 0 a.coefs p hp
    rw [← dot_dotAt, ← dot_dotAt] at e
    simp only [eval_ladd, eval_lscale, eval_lconst, e]
    simp only [eval, Int.add_zero]
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm b.const]; omega
  · simp at h

mutual
theorem linear_sound (hM : Model tab env maps x) (hP : PathHolds path x) :
    (e : E) → (l : Row) → linear tab path e = some l → eval l x = (evalE env maps e : Int)
  | .var i, l, h => by
    simp only [linear] at h
    cases hj : findIdx (isVar i) tab with
    | none => simp [hj] at h
    | some j =>
      simp only [hj, Option.map_some, Option.some.injEq] at h; subst h
      rw [eval_lunit, var_col hM hj, evalE]
  | .const n, l, h => by
    simp only [linear, Option.some.injEq] at h; subst h
    simp [eval_lconst, evalE]
  | .add a b, l, h => by
    simp only [linear] at h
    split at h
    · rename_i la lb ha hb
      simp only [Option.some.injEq] at h; subst h
      rw [eval_ladd, linear_sound hM hP a la ha, linear_sound hM hP b lb hb, evalE]; omega
    · simp at h
  | .mul k a, l, h => by
    simp only [linear] at h
    split at h
    · rename_i la ha
      simp only [Option.some.injEq] at h; subst h
      rw [eval_lscale, linear_sound hM hP a la ha, evalE]; simp
    · simp at h
  | .sub a b, l, h => by
    simp only [linear] at h
    split at h
    · rename_i la lb ha hb
      have ea := linear_sound hM hP a la ha
      have eb := linear_sound hM hP b lb hb
      split at h
      · rename_i hd
        simp only [Option.some.injEq] at h; subst h
        have := dec_sound hP hd
        simp only [decide_eq_true_eq, eval_lsub] at this
        rw [eval_lsub, evalE]; omega
      · rename_i hd
        simp only [Option.some.injEq] at h; subst h
        have := dec_sound hP hd
        simp only [decide_eq_false_iff_not, eval_lsub] at this
        rw [eval_lconst, evalE]; omega
      · exact termCol_sound hM h
    · simp at h
  | .min a b, l, h => by
    simp only [linear] at h
    split at h
    · rename_i la lb ha hb
      have ea := linear_sound hM hP a la ha
      have eb := linear_sound hM hP b lb hb
      split at h
      · rename_i hd
        simp only [Option.some.injEq] at h; subst h
        have := dec_sound hP hd
        simp only [decide_eq_true_eq, eval_lsub] at this
        rw [evalE, Nat.min_def]; split <;> omega
      · rename_i hd
        simp only [Option.some.injEq] at h; subst h
        have := dec_sound hP hd
        simp only [decide_eq_false_iff_not, eval_lsub] at this
        rw [evalE, Nat.min_def]; split <;> omega
      · exact termCol_sound hM h
    · simp at h
  | .max a b, l, h => by
    simp only [linear] at h
    split at h
    · rename_i la lb ha hb
      have ea := linear_sound hM hP a la ha
      have eb := linear_sound hM hP b lb hb
      split at h
      · rename_i hd
        simp only [Option.some.injEq] at h; subst h
        have := dec_sound hP hd
        simp only [decide_eq_true_eq, eval_lsub] at this
        rw [evalE, Nat.max_def]; split <;> omega
      · rename_i hd
        simp only [Option.some.injEq] at h; subst h
        have := dec_sound hP hd
        simp only [decide_eq_false_iff_not, eval_lsub] at this
        rw [evalE, Nat.max_def]; split <;> omega
      · exact termCol_sound hM h
    · simp at h
  | .prod a b, l, h => by
    simp only [linear] at h
    split at h
    · rename_i la lb ha hb
      rw [rowMul_sound hM h, linear_sound hM hP a la ha, linear_sound hM hP b lb hb, evalE]; simp
    · simp at h
  | .ite c t f, l, h => by
    simp only [linear] at h
    split at h
    · rename_i hc
      have := truth_sound hM hP c true hc
      rw [linear_sound hM hP t l h, evalE, this]; rfl
    · rename_i hc
      have := truth_sound hM hP c false hc
      rw [linear_sound hM hP f l h, evalE, this]; rfl
    · exact termCol_sound hM h
  | .get m key, l, h => by
    simp only [linear] at h
    split at h
    · rename_i lk hk
      cases hj : findIdx (isCell m lk) tab with
      | none => simp [hj] at h
      | some j =>
        simp only [hj, Option.map_some, Option.some.injEq] at h; subst h
        rw [eval_lunit, cell_col hM hj, linear_sound hM hP key lk hk, evalE]; simp
    · simp at h
theorem truth_sound (hM : Model tab env maps x) (hP : PathHolds path x) :
    (c : C) → (b : Bool) → truth tab path c = some b → evalC env maps c = b
  | .le a b', r, h => by
    simp only [truth] at h
    split at h
    · rename_i la lb ha hb
      have ea := linear_sound hM hP a la ha
      have eb := linear_sound hM hP b' lb hb
      have := dec_sound hP h
      rw [eval_lsub] at this
      simp only [evalC]; rw [← this]; simp only [decide_eq_decide]; omega
    · simp at h
  | .lt a b', r, h => by
    simp only [truth] at h
    split at h
    · rename_i la lb ha hb
      have ea := linear_sound hM hP a la ha
      have eb := linear_sound hM hP b' lb hb
      have := dec_sound hP h
      rw [eval_ladd, eval_lsub, eval_lconst] at this
      simp only [evalC]; rw [← this]; simp only [decide_eq_decide]; omega
    · simp at h
  | .eq a b', r, h => by
    simp only [truth] at h
    split at h
    · rename_i la lb ha hb
      have ea := linear_sound hM hP a la ha
      have eb := linear_sound hM hP b' lb hb
      simp only [evalC]
      revert h
      rcases h1 : dec path (lsub la lb) with _ | _ | _ <;> rcases h2 : dec path (lsub lb la) with _ | _ | _ <;>
        intro h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
        first
          | (have t1 := dec_sound hP h1; have t2 := dec_sound hP h2; rw [eval_lsub] at t1 t2
             simp only [decide_eq_true_eq, decide_eq_false_iff_not] at t1 t2 ⊢; omega)
          | (have t1 := dec_sound hP h1; rw [eval_lsub] at t1
             simp only [decide_eq_true_eq, decide_eq_false_iff_not] at t1 ⊢; omega)
          | (have t2 := dec_sound hP h2; rw [eval_lsub] at t2
             simp only [decide_eq_true_eq, decide_eq_false_iff_not] at t2 ⊢; omega)
    · simp at h
  | .and a b', r, h => by
    simp only [truth] at h
    simp only [evalC]
    split at h
    · rename_i h1; simp only [Option.some.injEq] at h; subst h; simp [truth_sound hM hP a false h1]
    · rename_i h2 _; simp only [Option.some.injEq] at h; subst h; simp [truth_sound hM hP b' false h2]
    · rename_i h1 h2; simp only [Option.some.injEq] at h; subst h; simp [truth_sound hM hP a true h1, truth_sound hM hP b' true h2]
    · simp at h
  | .or a b', r, h => by
    simp only [truth] at h
    simp only [evalC]
    split at h
    · rename_i h1; simp only [Option.some.injEq] at h; subst h; simp [truth_sound hM hP a true h1]
    · rename_i h2 _; simp only [Option.some.injEq] at h; subst h; simp [truth_sound hM hP b' true h2]
    · rename_i h1 h2; simp only [Option.some.injEq] at h; subst h; simp [truth_sound hM hP a false h1, truth_sound hM hP b' false h2]
    · simp at h
  | .not a, r, h => by
    simp only [truth] at h
    split at h
    · rename_i r' h1; simp only [Option.some.injEq] at h; subst h; simp [evalC, truth_sound hM hP a r' h1]
    · simp at h
end
end

/-! Facts: the rows a hypothesis gives under the path, when it has the truth value `pos`. -/

def facts (tab : List VDef) (path : Path) : Bool → C → List Row
  | pos, .not a => facts tab path (!pos) a
  | pos, .and a b =>
    if pos then facts tab path pos a ++ facts tab path pos b
    else
      let oa := truth tab path a != some (!pos)
      let ob := truth tab path b != some (!pos)
      if oa && ob then [] else if oa then facts tab path pos a else if ob then facts tab path pos b else [lconst 1]
  | pos, .or a b =>
    if !pos then facts tab path pos a ++ facts tab path pos b
    else
      let oa := truth tab path a != some (!pos)
      let ob := truth tab path b != some (!pos)
      if oa && ob then [] else if oa then facts tab path pos a else if ob then facts tab path pos b else [lconst 1]
  | pos, .le a b => match linear tab path a, linear tab path b with
    | some la, some lb =>
      if pos then [lsub la lb]
      else let u := ladd (lsub lb la) (lconst 1); if dec path u == some false then [lconst 1] else [u]
    | _, _ => []
  | pos, .lt a b => match linear tab path a, linear tab path b with
    | some la, some lb =>
      if pos then [ladd (lsub la lb) (lconst 1)]
      else let u := lsub lb la; if dec path u == some false then [lconst 1] else [u]
    | _, _ => []
  | pos, .eq a b => match linear tab path a, linear tab path b with
    | some la, some lb =>
      if pos then [lsub la lb, lsub lb la]
      else
        let u1 := ladd (lsub la lb) (lconst 1)
        let u2 := ladd (lsub lb la) (lconst 1)
        let o1 := dec path u1 != some false
        let o2 := dec path u2 != some false
        if o1 && o2 then [] else if o1 then [u1] else if o2 then [u2] else [lconst 1]
    | _, _ => []

section
variable {tab : List VDef} {env : Nat → Nat} {maps : Nat → Nat → Nat} {x : List Int} {path : Path}

theorem facts_sound (hM : Model tab env maps x) (hP : PathHolds path x) :
    (c : C) → (pos : Bool) → evalC env maps c = pos → ∀ r ∈ facts tab path pos c, eval r x ≤ 0
  | .not a, pos, h, r, hr => by
    simp only [facts] at hr
    exact facts_sound hM hP a (!pos) (by simp [evalC] at h; simp [← h]) r hr
  | .and a b, pos, h, r, hr => by
    simp only [facts] at hr
    cases pos with
    | true =>
      simp only [evalC, Bool.and_eq_true] at h
      simp only [ite_true, List.mem_append] at hr
      rcases hr with hr | hr
      · exact facts_sound hM hP a true h.1 r hr
      · exact facts_sound hM hP b true h.2 r hr
    | false =>
      simp only [Bool.false_eq_true, ite_false, Bool.not_false] at hr
      have ta := fun v (hv : truth tab path a = some v) => truth_sound hM hP a v hv
      have tb := fun v (hv : truth tab path b = some v) => truth_sound hM hP b v hv
      simp only [evalC, Bool.and_eq_false_iff] at h
      split at hr
      · simp at hr
      · split at hr
        · rename_i _ hoa
          have hb : truth tab path b = some true := by simp_all
          have := tb true hb
          exact facts_sound hM hP a false (by simp_all) r hr
        · split at hr
          · rename_i _ _ hob
            have ha : truth tab path a = some true := by simp_all
            have := ta true ha
            exact facts_sound hM hP b false (by simp_all) r hr
          · have ha : truth tab path a = some true := by simp_all
            have hb : truth tab path b = some true := by simp_all
            have := ta true ha; have := tb true hb
            simp_all
  | .or a b, pos, h, r, hr => by
    simp only [facts] at hr
    cases pos with
    | false =>
      simp only [evalC, Bool.or_eq_false_iff] at h
      simp only [Bool.not_false, ite_true, List.mem_append] at hr
      rcases hr with hr | hr
      · exact facts_sound hM hP a false h.1 r hr
      · exact facts_sound hM hP b false h.2 r hr
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hr
      have ta := fun v (hv : truth tab path a = some v) => truth_sound hM hP a v hv
      have tb := fun v (hv : truth tab path b = some v) => truth_sound hM hP b v hv
      simp only [evalC, Bool.or_eq_true] at h
      split at hr
      · simp at hr
      · split at hr
        · have hb : truth tab path b = some false := by simp_all
          have := tb false hb
          exact facts_sound hM hP a true (by simp_all) r hr
        · split at hr
          · have ha : truth tab path a = some false := by simp_all
            have := ta false ha
            exact facts_sound hM hP b true (by simp_all) r hr
          · have ha : truth tab path a = some false := by simp_all
            have hb : truth tab path b = some false := by simp_all
            have := ta false ha; have := tb false hb
            simp_all
  | .le a b, pos, h, r, hr => by
    simp only [facts] at hr
    split at hr
    · rename_i la lb ha hb
      have ea := linear_sound hM hP a la ha
      have eb := linear_sound hM hP b lb hb
      cases pos with
      | true =>
        simp only [evalC, decide_eq_true_eq] at h
        simp only [ite_true, List.mem_singleton] at hr; subst hr
        rw [eval_lsub]; omega
      | false =>
        simp only [evalC, decide_eq_false_iff_not] at h
        simp only [Bool.false_eq_true, ite_false] at hr
        split at hr
        · rename_i hd
          have := dec_sound hP (by simpa using hd)
          simp only [eval_ladd, eval_lsub, eval_lconst, decide_eq_false_iff_not] at this; omega
        · simp only [List.mem_singleton] at hr; subst hr
          rw [eval_ladd, eval_lsub, eval_lconst]; omega
    · simp at hr
  | .lt a b, pos, h, r, hr => by
    simp only [facts] at hr
    split at hr
    · rename_i la lb ha hb
      have ea := linear_sound hM hP a la ha
      have eb := linear_sound hM hP b lb hb
      cases pos with
      | true =>
        simp only [evalC, decide_eq_true_eq] at h
        simp only [ite_true, List.mem_singleton] at hr; subst hr
        rw [eval_ladd, eval_lsub, eval_lconst]; omega
      | false =>
        simp only [evalC, decide_eq_false_iff_not] at h
        simp only [Bool.false_eq_true, ite_false] at hr
        split at hr
        · rename_i hd
          have := dec_sound hP (by simpa using hd)
          simp only [eval_lsub, decide_eq_false_iff_not] at this; omega
        · simp only [List.mem_singleton] at hr; subst hr
          rw [eval_lsub]; omega
    · simp at hr
  | .eq a b, pos, h, r, hr => by
    simp only [facts] at hr
    split at hr
    · rename_i la lb ha hb
      have ea := linear_sound hM hP a la ha
      have eb := linear_sound hM hP b lb hb
      cases pos with
      | true =>
        simp only [evalC, decide_eq_true_eq] at h
        simp only [ite_true, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
        rcases hr with hr | hr <;> subst hr <;> rw [eval_lsub] <;> omega
      | false =>
        simp only [evalC, decide_eq_false_iff_not] at h
        simp only [Bool.false_eq_true, ite_false] at hr
        have d1 := fun (hv : dec path (ladd (lsub la lb) (lconst 1)) = some false) => dec_sound hP hv
        have d2 := fun (hv : dec path (ladd (lsub lb la) (lconst 1)) = some false) => dec_sound hP hv
        simp only [eval_ladd, eval_lsub, eval_lconst, decide_eq_false_iff_not] at d1 d2
        split at hr
        · simp at hr
        · split at hr
          · have := d2 (by simp_all)
            simp only [List.mem_singleton] at hr; subst hr
            rw [eval_ladd, eval_lsub, eval_lconst]; omega
          · split at hr
            · have := d1 (by simp_all)
              simp only [List.mem_singleton] at hr; subst hr
              rw [eval_ladd, eval_lsub, eval_lconst]; omega
            · have := d1 (by simp_all); have := d2 (by simp_all); omega
    · simp at hr
end

/-! Leaves and trees. -/

def atomRow (a : Row × Bool) : Row := if a.2 then a.1 else flip a.1
def natRows : Nat → List Row
  | 0 => []
  | n + 1 => lscale (-1) (lunit n) :: natRows n
-- Two cells of one map whose keys the path proves equal are equal (the pair is the leaf's claim; it is checked here).
def cellEq (tab : List VDef) (path : Path) (p : Nat × Nat) : List Row :=
  match tab[p.1]?, tab[p.2]? with
  | some (.cell m k), some (.cell m' k') =>
    if m == m' && dec path (lsub k k') == some true && dec path (lsub k' k) == some true
    then [lsub (lunit p.1) (lunit p.2), lsub (lunit p.2) (lunit p.1)] else []
  | _, _ => []
-- A term column's rows: its bounds, whichever way its choice goes (min ≤ each side, max ≥ each side, a ∸ b ≥ a − b and
-- ≤ a), and its equality to the term's form under the path (the branch taken, once the path decides it).
def termBounds (j : Nat) (la lb : Row) : E → List Row
  | .min _ _ => [lsub (lunit j) la, lsub (lunit j) lb]
  | .max _ _ => [lsub la (lunit j), lsub lb (lunit j)]
  | .sub _ _ => [lsub (lsub la lb) (lunit j), lsub (lunit j) la]
  | _ => []
def termRowsAt (tab : List VDef) (path : Path) (j : Nat) : List Row :=
  match tab[j]? with
  | some (.term e) =>
    (match e with
     | .min a b | .max a b | .sub a b => match linear tab path a, linear tab path b with
       | some la, some lb => termBounds j la lb e
       | _, _ => []
     | _ => [])
    ++ (match linear tab path e with
        | some r => [lsub (lunit j) r, lsub r (lunit j)]
        | none => [])
  | _ => []
def termRows (tab : List VDef) (path : Path) : List Row := (List.range tab.length).flatMap (termRowsAt tab path)

def leafRows (tab : List VDef) (path : Path) (hyps : List C) (eqs : List (Nat × Nat)) : List Row :=
  path.map atomRow ++ hyps.flatMap (facts tab path true) ++ natRows tab.length ++ eqs.flatMap (cellEq tab path) ++ termRows tab path

-- Where a leaf's row is looked for first: the path's i-th atom (the latest decision first), a hypothesis's facts, column i's naturality, the i-th
-- pair of equal cells, or term column j's rows. A hint only saves work: a row not found there is looked for among all
-- of the leaf's rows, as one without a hint is.
inductive Src where
  | atom (i : Nat)
  | fact (h : Nat)
  | nat (i : Nat)
  | eq (i : Nat)
  | term (j : Nat)
  | any

def srcRows (tab : List VDef) (path : Path) (hyps : List C) (eqs : List (Nat × Nat)) : Src → List Row
  | .atom i => match path[i]? with | some a => [atomRow a] | none => []
  | .fact h => match hyps[h]? with | some c => facts tab path true c | none => []
  | .nat i => if i < tab.length then [lscale (-1) (lunit i)] else []
  | .eq i => match eqs[i]? with | some p => cellEq tab path p | none => []
  | .term j => if j < tab.length then termRowsAt tab path j else []
  | .any => []

-- A leaf may add products of two of its rows (p ≤ 0 and q ≤ 0 give −p·q ≤ 0); a pair may name an earlier product.
-- `leafAt` is a leaf whose rows come with hints.
inductive Tree where
  | split (l : Row) (yes no : Tree)
  | leaf (rows : List Row) (steps : List Step) (eqs : List (Nat × Nat)) (prods : List (Nat × Nat))
  | leafAt (rows : List (Row × Src)) (steps : List Step) (eqs : List (Nat × Nat)) (prods : List (Nat × Nat))

def extend (tab : List VDef) : List Row → List (Nat × Nat) → Option (List Row)
  | acc, [] => some acc
  | acc, (i, j) :: ps => match acc[i]?, acc[j]? with
    | some p, some q => match rowMul tab p q with
      | some r => extend tab (acc ++ [lscale (-1) r]) ps
      | none => none
    | _, _ => none

def leafOk (tab : List VDef) (path : Path) (hyps : List C) (rows : List Row) (steps : List Step) (eqs : List (Nat × Nat))
    (prods : List (Nat × Nat)) : Bool :=
  let comp := leafRows tab path hyps eqs
  rows.all (fun r => comp.any (same r)) && match extend tab rows prods with
    | some rows' => Cert.check rows' steps
    | none => false

-- Each row where its hint says, or else among the leaf's rows.
def leafAtOk (tab : List VDef) (path : Path) (hyps : List C) (rows : List (Row × Src)) (steps : List Step) (eqs : List (Nat × Nat))
    (prods : List (Nat × Nat)) : Bool :=
  rows.all (fun r => (srcRows tab path hyps eqs r.2).any (same r.1) || (leafRows tab path hyps eqs).any (same r.1))
    && match extend tab (rows.map (·.1)) prods with
    | some rows' => Cert.check rows' steps
    | none => false

def checkT (tab : List VDef) (hyps : List C) : Path → Tree → Bool
  | path, .split l y n => checkT tab hyps ((l, true) :: path) y && checkT tab hyps ((l, false) :: path) n
  | path, .leaf rows steps eqs prods => leafOk tab path hyps rows steps eqs prods
  | path, .leafAt rows steps eqs prods => leafAtOk tab path hyps rows steps eqs prods

structure Goal where
  tab : List VDef
  hyps : List C

-- Each cell's key reads only earlier columns, so the table has a valuation.
def wfTab : Nat → List VDef → Bool
  | _, [] => true
  | n, .var _ :: ds => wfTab (n + 1) ds
  | n, .cell _ k :: ds => decide (k.coefs.length ≤ n) && wfTab (n + 1) ds
  | n, .mono fs :: ds => fs.all (· < n) && wfTab (n + 1) ds
  | n, .term _ :: ds => wfTab (n + 1) ds

def checkGoal (g : Goal) (t : Tree) : Bool := wfTab 0 g.tab && checkT g.tab g.hyps [] t

section
variable {tab : List VDef} {env : Nat → Nat} {maps : Nat → Nat → Nat} {x : List Int}

theorem natRows_sound (hM : Model tab env maps x) : ∀ n, ∀ r ∈ natRows n, eval r x ≤ 0
  | 0, r, hr => by simp [natRows] at hr
  | n + 1, r, hr => by
    simp only [natRows, List.mem_cons] at hr
    rcases hr with hr | hr
    · subst hr; rw [eval_lscale, eval_lunit]; have := hM.2 n; omega
    · exact natRows_sound hM n r hr

theorem termRows_sound {path : Path} (hM : Model tab env maps x) (hP : PathHolds path x) :
    ∀ r ∈ termRows tab path, eval r x ≤ 0 := by
  intro r hr
  simp only [termRows, List.mem_flatMap] at hr
  obtain ⟨j, _, hr⟩ := hr
  simp only [termRowsAt] at hr
  split at hr
  · rename_i e hj
    have hx : x.getD j 0 = (evalE env maps e : Int) := by rw [hM.1 j _ hj]; rfl
    simp only [List.mem_append] at hr
    rcases hr with hr | hr
    · cases e with
      | min a b =>
        simp only at hr
        split at hr
        · rename_i la lb ha hb
          have ea := linear_sound hM hP a la ha
          have eb := linear_sound hM hP b lb hb
          simp only [termBounds, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
          simp only [evalE, Nat.min_def] at hx
          split at hx <;> rcases hr with rfl | rfl <;> rw [eval_lsub, eval_lunit] <;> omega
        · simp at hr
      | max a b =>
        simp only at hr
        split at hr
        · rename_i la lb ha hb
          have ea := linear_sound hM hP a la ha
          have eb := linear_sound hM hP b lb hb
          simp only [termBounds, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
          simp only [evalE, Nat.max_def] at hx
          split at hx <;> rcases hr with rfl | rfl <;> rw [eval_lsub, eval_lunit] <;> omega
        · simp at hr
      | sub a b =>
        simp only at hr
        split at hr
        · rename_i la lb ha hb
          have ea := linear_sound hM hP a la ha
          have eb := linear_sound hM hP b lb hb
          simp only [termBounds, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
          simp only [evalE] at hx
          rcases hr with rfl | rfl
          · rw [eval_lsub, eval_lsub, eval_lunit]; omega
          · rw [eval_lsub, eval_lunit]; omega
        · simp at hr
      | _ => simp at hr
    · split at hr
      · rename_i r' hr'
        have := linear_sound hM hP e r' hr'
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> rw [eval_lsub, eval_lunit] <;> omega
      · simp at hr
  · simp at hr

theorem leafRows_sound {path : Path} (hM : Model tab env maps x) (hP : PathHolds path x) {hyps : List C}
    (hH : ∀ c ∈ hyps, evalC env maps c = true) (eqs : List (Nat × Nat)) : ∀ r ∈ leafRows tab path hyps eqs, eval r x ≤ 0 := by
  intro r hr
  simp only [leafRows, List.mem_append, List.mem_map, List.mem_flatMap] at hr
  rcases hr with (((⟨a, ha, rfl⟩ | ⟨c, hc, hr⟩) | hr) | ⟨p, _, hr⟩) | hr
  · have := hP a ha
    simp only [atomRow]
    cases h2 : a.2 with
    | true => rw [h2] at this; simpa using this
    | false => rw [h2] at this; simp only [decide_eq_false_iff_not] at this; simp only [ite_false, Bool.false_eq_true, eval_flip]; omega
  · exact facts_sound hM hP c true (hH c hc) r hr
  · exact natRows_sound hM _ r hr
  · simp only [cellEq] at hr
    split at hr
    · rename_i m k m' k' h1 h2
      split at hr
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨rfl, hk1⟩, hk2⟩ := hc
        have t1 := dec_sound hP hk1; have t2 := dec_sound hP hk2
        simp only [eval_lsub, decide_eq_true_eq] at t1 t2
        have e1 := hM.1 p.1 _ h1; have e2 := hM.1 p.2 _ h2
        simp only [valD] at e1 e2
        have hkk : eval k x = eval k' x := by omega
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> rw [eval_lsub, eval_lunit, eval_lunit, e1, e2, hkk] <;> omega
      · simp at hr
    · simp at hr
  · exact termRows_sound hM hP r hr

-- A hint names some of the leaf's rows.
theorem natRows_mem : ∀ {n i : Nat}, i < n → lscale (-1) (lunit i) ∈ natRows n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    simp only [natRows, List.mem_cons]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · exact Or.inr (natRows_mem h)
    · exact Or.inl rfl

theorem srcRows_sub {path : Path} {hyps : List C} {eqs : List (Nat × Nat)} {r : Row} :
    ∀ s, r ∈ srcRows tab path hyps eqs s → r ∈ leafRows tab path hyps eqs
  | .atom i, hr => by
    simp only [srcRows] at hr
    split at hr
    · rename_i a ha
      simp only [List.mem_singleton] at hr; subst hr
      simp only [leafRows, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl (Or.inl (Or.inl ⟨a, List.mem_of_getElem? ha, rfl⟩)))
    · simp at hr
  | .fact h, hr => by
    simp only [srcRows] at hr
    split at hr
    · rename_i c hc
      simp only [leafRows, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨c, List.mem_of_getElem? hc, hr⟩)))
    · simp at hr
  | .nat i, hr => by
    simp only [srcRows] at hr
    split at hr
    · rename_i hi
      simp only [List.mem_singleton] at hr; subst hr
      simp only [leafRows, List.mem_append]
      exact Or.inl (Or.inl (Or.inr (natRows_mem hi)))
    · simp at hr
  | .eq i, hr => by
    simp only [srcRows] at hr
    split at hr
    · rename_i p hp
      simp only [leafRows, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inr ⟨p, List.mem_of_getElem? hp, hr⟩)
    · simp at hr
  | .term j, hr => by
    simp only [srcRows] at hr
    split at hr
    · rename_i hj
      simp only [leafRows, termRows, List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inr ⟨j, hj, hr⟩
    · simp at hr
  | .any, hr => by simp [srcRows] at hr

theorem extend_sound (hM : Model tab env maps x) :
    ∀ ps acc rows', extend tab acc ps = some rows' → (∀ r ∈ acc, eval r x ≤ 0) → ∀ r ∈ rows', eval r x ≤ 0
  | [], acc, rows', h, ha => by simp only [extend, Option.some.injEq] at h; subst h; exact ha
  | (i, j) :: ps, acc, rows', h, ha => by
    simp only [extend] at h
    split at h
    · rename_i p q hp hq
      split at h
      · rename_i r hr
        refine extend_sound hM ps _ rows' h (fun r' hr' => ?_)
        rcases List.mem_append.mp hr' with hr' | hr'
        · exact ha r' hr'
        · simp only [List.mem_singleton] at hr'; subst hr'
          have e1 := ha p (List.mem_of_getElem? hp)
          have e2 := ha q (List.mem_of_getElem? hq)
          rw [eval_lscale, rowMul_sound hM hr]
          have : 0 ≤ (-eval p x) * (-eval q x) := Int.mul_nonneg (by omega) (by omega)
          rw [Int.neg_mul_neg] at this; omega
      · simp at h
    · simp at h

theorem checkT_sound (hM : Model tab env maps x) {hyps : List C} (hH : ∀ c ∈ hyps, evalC env maps c = true) :
    ∀ (t : Tree) (path : Path), PathHolds path x → checkT tab hyps path t = true → False
  | .split l y n, path, hP, h => by
    simp only [checkT, Bool.and_eq_true] at h
    by_cases hl : eval l x ≤ 0
    · refine checkT_sound hM hH y _ ?_ h.1
      intro a ha
      rcases List.mem_cons.mp ha with ha | ha
      · subst ha; simpa using hl
      · exact hP a ha
    · refine checkT_sound hM hH n _ ?_ h.2
      intro a ha
      rcases List.mem_cons.mp ha with ha | ha
      · subst ha; simpa using hl
      · exact hP a ha
  | .leaf rows steps eqs prods, path, hP, h => by
    simp only [checkT, leafOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    split at h2
    · rename_i rows' he
      refine Cert.sound rows' steps h2 x (extend_sound hM prods rows rows' he ?_)
      intro r hr
      obtain ⟨c, hc, hs⟩ := h1 r hr
      rw [same_eval hs]
      exact leafRows_sound hM hP hH eqs c hc
    · simp at h2
  | .leafAt rows steps eqs prods, path, hP, h => by
    simp only [checkT, leafAtOk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, List.any_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    split at h2
    · rename_i rows' he
      refine Cert.sound rows' steps h2 x (extend_sound hM prods _ rows' he ?_)
      intro r hr
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
      rcases h1 p hp with ⟨c, hc, hs⟩ | ⟨c, hc, hs⟩
      · rw [same_eval hs]; exact leafRows_sound hM hP hH eqs c (srcRows_sub p.2 hc)
      · rw [same_eval hs]; exact leafRows_sound hM hP hH eqs c hc
    · simp at h2
end

/-! The table's valuation. -/

def build (env : Nat → Nat) (maps : Nat → Nat → Nat) : List VDef → List Int → List Int
  | [], acc => acc
  | d :: ds, acc => build env maps ds (acc ++ [valD env maps d acc])

theorem dot_append : ∀ (a l1 l2 : List Int), a.length ≤ l1.length → dot a (l1 ++ l2) = dot a l1
  | [], _, _, _ => by simp [dot]
  | _ :: _, [], _, h => by simp at h
  | c :: cs, y :: ys, l2, h => by
    simp only [List.length_cons, Nat.add_le_add_iff_right] at h
    simp only [List.cons_append, dot, dot_append cs ys l2 h]

-- What a column may refer to: only earlier columns.
def Refs (n : Nat) : VDef → Prop
  | .var _ => True
  | .cell _ k => k.coefs.length ≤ n
  | .mono fs => ∀ f ∈ fs, f < n
  | .term _ => True

theorem Refs.mono_le {n m : Nat} (h : n ≤ m) : ∀ {d : VDef}, Refs n d → Refs m d
  | .var _, _ => trivial
  | .cell _ _, hd => by simp only [Refs] at hd ⊢; omega
  | .mono _, hd => fun f hf => by have := hd f hf; omega
  | .term _, _ => trivial

theorem prodV_append_left (acc more : List Int) : ∀ fs : List Nat, (∀ f ∈ fs, f < acc.length) → prodV (acc ++ more) fs = prodV acc fs
  | [], _ => rfl
  | f :: fs, h => by
    simp only [prodV]
    rw [prodV_append_left acc more fs (fun g hg => h g (List.mem_cons_of_mem _ hg))]
    have hf := h f List.mem_cons_self
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hf]

theorem valD_append (env : Nat → Nat) (maps : Nat → Nat → Nat) (d : VDef) (acc more : List Int)
    (h : Refs acc.length d) : valD env maps d (acc ++ more) = valD env maps d acc := by
  cases d with
  | var i => rfl
  | cell m k => simp only [Refs] at h; simp only [valD, eval, dot_append k.coefs acc more h]
  | mono fs => simp only [valD, prodV_append_left acc more fs h]
  | term e => rfl

def Valid (env : Nat → Nat) (maps : Nat → Nat → Nat) (acc : List Int) (pre : List VDef) : Prop :=
  acc.length = pre.length ∧ (∀ (j : Nat) (d : VDef), pre[j]? = some d → Refs j d) ∧
    ∀ (j : Nat) (d : VDef), pre[j]? = some d → acc[j]? = some (valD env maps d acc)

theorem valid_snoc {env : Nat → Nat} {maps : Nat → Nat → Nat} {acc : List Int} {pre : List VDef} (d : VDef)
    (hv : Valid env maps acc pre) (hd : Refs pre.length d) :
    Valid env maps (acc ++ [valD env maps d acc]) (pre ++ [d]) := by
  obtain ⟨hl, hw, hx⟩ := hv
  refine ⟨by simp [hl], ?_, ?_⟩
  · intro j d' hj
    by_cases hlt : j < pre.length
    · rw [List.getElem?_append_left hlt] at hj; exact hw j d' hj
    · rw [List.getElem?_append_right (by omega)] at hj
      have hj0 : j - pre.length = 0 := by
        cases h : j - pre.length with
        | zero => rfl
        | succ n => rw [h] at hj; simp at hj
      rw [hj0] at hj; simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
      exact Refs.mono_le (by omega) hd
  · intro j d' hj
    by_cases hlt : j < pre.length
    · rw [List.getElem?_append_left hlt] at hj
      rw [List.getElem?_append_left (by omega), hx j d' hj]
      rw [valD_append env maps d' acc _ (Refs.mono_le (by omega) (hw j d' hj))]
    · rw [List.getElem?_append_right (by omega)] at hj
      have hj0 : j - pre.length = 0 := by
        cases h : j - pre.length with
        | zero => rfl
        | succ n => rw [h] at hj; simp at hj
      rw [hj0] at hj; simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
      rw [List.getElem?_append_right (by omega), show j - acc.length = 0 by omega]
      simp only [List.getElem?_cons_zero, Option.some.injEq]
      rw [valD_append env maps d acc _ (by rw [hl]; exact hd)]

theorem build_valid (env : Nat → Nat) (maps : Nat → Nat → Nat) : ∀ (ds : List VDef) (acc : List Int) (pre : List VDef),
    Valid env maps acc pre → wfTab pre.length ds = true → Valid env maps (build env maps ds acc) (pre ++ ds)
  | [], acc, pre, hv, _ => by simpa [build] using hv
  | d :: ds, acc, pre, hv, hw => by
    have hd : Refs pre.length d ∧ wfTab (pre.length + 1) ds = true := by
      cases d with
      | var i => exact ⟨trivial, by simpa [wfTab] using hw⟩
      | cell m k =>
        simp only [wfTab, Bool.and_eq_true, decide_eq_true_eq] at hw
        exact ⟨hw.1, hw.2⟩
      | mono fs =>
        simp only [wfTab, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hw
        exact ⟨hw.1, hw.2⟩
      | term e => exact ⟨trivial, by simpa [wfTab] using hw⟩
    have := build_valid env maps ds _ (pre ++ [d]) (valid_snoc d hv hd.1) (by simpa using hd.2)
    simpa [build] using this

theorem model_of_valid {env : Nat → Nat} {maps : Nat → Nat → Nat} {x : List Int} {tab : List VDef}
    (hv : Valid env maps x tab) : Model tab env maps x := by
  obtain ⟨hl, _, hx⟩ := hv
  refine ⟨fun j d hj => by rw [List.getD_eq_getElem?_getD, hx j d hj]; rfl, fun j => ?_⟩
  rw [List.getD_eq_getElem?_getD]
  cases h : x[j]? with
  | none => simp
  | some v =>
    have hj : j < tab.length := by
      have := (List.getElem?_eq_some_iff.mp h).1; omega
    obtain ⟨d, hd⟩ : ∃ d, tab[j]? = some d := ⟨tab[j], List.getElem?_eq_getElem hj⟩
    rw [hx j d hd] at h
    simp only [Option.some.injEq] at h; subst h
    cases d <;> simp [valD]
    exact Int.le_max_right _ _

/-- The kernel's tree check is sound: an accepted goal's hypotheses hold for no naturals and no maps. -/
theorem sound (g : Goal) (t : Tree) (h : checkGoal g t = true) (env : Nat → Nat) (maps : Nat → Nat → Nat) :
    ¬ ∀ c ∈ g.hyps, evalC env maps c = true := by
  intro hH
  simp only [checkGoal, Bool.and_eq_true] at h
  have hv := build_valid env maps g.tab [] [] ⟨rfl, by simp, by simp⟩ (by simpa using h.1)
  simp only [List.nil_append] at hv
  exact checkT_sound (model_of_valid hv) hH t [] (by simp [PathHolds]) h.2

/-! Step machines with scalar state: the induction rule over kernel goals. The goals are built here, in Lean, from
the machine, so the TypeScript `obligations` is not trusted for these: a law holds at the start (`startGoal` is
refuted) and one step keeps every law (`stepGoal` is refuted, assuming them all and the request's assumption), so every
law holds in every reachable state. Laws may not read the request's inputs. -/

def assoc (σ : List (Nat × E)) (i : Nat) : Option E := (lookup (fun p => p.1 == i) σ).map (·.2)

mutual
def substE (σ : List (Nat × E)) : E → E
  | .var i => match assoc σ i with
    | some e => e
    | none => .var i
  | .const n => .const n
  | .add a b => .add (substE σ a) (substE σ b)
  | .sub a b => .sub (substE σ a) (substE σ b)
  | .mul k a => .mul k (substE σ a)
  | .min a b => .min (substE σ a) (substE σ b)
  | .max a b => .max (substE σ a) (substE σ b)
  | .prod a b => .prod (substE σ a) (substE σ b)
  | .ite c t f => .ite (substC σ c) (substE σ t) (substE σ f)
  | .get m key => .get m (substE σ key)
def substC (σ : List (Nat × E)) : C → C
  | .le a b => .le (substE σ a) (substE σ b)
  | .lt a b => .lt (substE σ a) (substE σ b)
  | .eq a b => .eq (substE σ a) (substE σ b)
  | .and a b => .and (substC σ a) (substC σ b)
  | .or a b => .or (substC σ a) (substC σ b)
  | .not a => .not (substC σ a)
end

-- The environment after σ: each assigned variable takes its term's value, the rest keep theirs.
def applyS (σ : List (Nat × E)) (ρ : Nat → Nat) (maps : Nat → Nat → Nat) : Nat → Nat :=
  fun i => match assoc σ i with
    | some e => evalE ρ maps e
    | none => ρ i

mutual
theorem subst_evalE (σ : List (Nat × E)) (ρ : Nat → Nat) (maps : Nat → Nat → Nat) :
    (e : E) → evalE ρ maps (substE σ e) = evalE (applyS σ ρ maps) maps e
  | .var i => by
    simp only [substE]
    cases h : assoc σ i <;> simp [evalE, applyS, h]
  | .const n => by simp [substE, evalE]
  | .add a b => by simp [substE, evalE, subst_evalE σ ρ maps a, subst_evalE σ ρ maps b]
  | .sub a b => by simp [substE, evalE, subst_evalE σ ρ maps a, subst_evalE σ ρ maps b]
  | .mul k a => by simp [substE, evalE, subst_evalE σ ρ maps a]
  | .min a b => by simp [substE, evalE, subst_evalE σ ρ maps a, subst_evalE σ ρ maps b]
  | .max a b => by simp [substE, evalE, subst_evalE σ ρ maps a, subst_evalE σ ρ maps b]
  | .prod a b => by simp [substE, evalE, subst_evalE σ ρ maps a, subst_evalE σ ρ maps b]
  | .ite c t f => by simp [substE, evalE, subst_evalC σ ρ maps c, subst_evalE σ ρ maps t, subst_evalE σ ρ maps f]
  | .get m key => by simp [substE, evalE, subst_evalE σ ρ maps key]
theorem subst_evalC (σ : List (Nat × E)) (ρ : Nat → Nat) (maps : Nat → Nat → Nat) :
    (c : C) → evalC ρ maps (substC σ c) = evalC (applyS σ ρ maps) maps c
  | .le a b => by simp [substC, evalC, subst_evalE σ ρ maps a, subst_evalE σ ρ maps b]
  | .lt a b => by simp [substC, evalC, subst_evalE σ ρ maps a, subst_evalE σ ρ maps b]
  | .eq a b => by simp [substC, evalC, subst_evalE σ ρ maps a, subst_evalE σ ρ maps b]
  | .and a b => by simp [substC, evalC, subst_evalC σ ρ maps a, subst_evalC σ ρ maps b]
  | .or a b => by simp [substC, evalC, subst_evalC σ ρ maps a, subst_evalC σ ρ maps b]
  | .not a => by simp [substC, evalC, subst_evalC σ ρ maps a]
end

mutual
def occE (i : Nat) : E → Bool
  | .var j => j == i
  | .const _ => false
  | .add a b => occE i a || occE i b
  | .sub a b => occE i a || occE i b
  | .mul _ a => occE i a
  | .min a b => occE i a || occE i b
  | .max a b => occE i a || occE i b
  | .prod a b => occE i a || occE i b
  | .ite c t f => occC i c || occE i t || occE i f
  | .get _ key => occE i key
def occC (i : Nat) : C → Bool
  | .le a b => occE i a || occE i b
  | .lt a b => occE i a || occE i b
  | .eq a b => occE i a || occE i b
  | .and a b => occC i a || occC i b
  | .or a b => occC i a || occC i b
  | .not a => occC i a
end

mutual
theorem congrE (ρ ρ' : Nat → Nat) (maps : Nat → Nat → Nat) :
    (e : E) → (∀ i, occE i e = true → ρ i = ρ' i) → evalE ρ maps e = evalE ρ' maps e
  | .var j, h => by simp only [evalE]; exact h j (by simp [occE])
  | .const n, _ => rfl
  | .add a b, h => by
    simp only [evalE, congrE ρ ρ' maps a (fun i hi => h i (by simp [occE, hi])), congrE ρ ρ' maps b (fun i hi => h i (by simp [occE, hi]))]
  | .sub a b, h => by
    simp only [evalE, congrE ρ ρ' maps a (fun i hi => h i (by simp [occE, hi])), congrE ρ ρ' maps b (fun i hi => h i (by simp [occE, hi]))]
  | .mul k a, h => by simp only [evalE, congrE ρ ρ' maps a (fun i hi => h i (by simp [occE, hi]))]
  | .min a b, h => by
    simp only [evalE, congrE ρ ρ' maps a (fun i hi => h i (by simp [occE, hi])), congrE ρ ρ' maps b (fun i hi => h i (by simp [occE, hi]))]
  | .max a b, h => by
    simp only [evalE, congrE ρ ρ' maps a (fun i hi => h i (by simp [occE, hi])), congrE ρ ρ' maps b (fun i hi => h i (by simp [occE, hi]))]
  | .prod a b, h => by
    simp only [evalE, congrE ρ ρ' maps a (fun i hi => h i (by simp [occE, hi])), congrE ρ ρ' maps b (fun i hi => h i (by simp [occE, hi]))]
  | .ite c t f, h => by
    simp only [evalE, congrC ρ ρ' maps c (fun i hi => h i (by simp [occE, hi])), congrE ρ ρ' maps t (fun i hi => h i (by simp [occE, hi])),
      congrE ρ ρ' maps f (fun i hi => h i (by simp [occE, hi]))]
  | .get m key, h => by simp only [evalE, congrE ρ ρ' maps key (fun i hi => h i (by simp [occE, hi]))]
theorem congrC (ρ ρ' : Nat → Nat) (maps : Nat → Nat → Nat) :
    (c : C) → (∀ i, occC i c = true → ρ i = ρ' i) → evalC ρ maps c = evalC ρ' maps c
  | .le a b, h => by
    simp only [evalC, congrE ρ ρ' maps a (fun i hi => h i (by simp [occC, hi])), congrE ρ ρ' maps b (fun i hi => h i (by simp [occC, hi]))]
  | .lt a b, h => by
    simp only [evalC, congrE ρ ρ' maps a (fun i hi => h i (by simp [occC, hi])), congrE ρ ρ' maps b (fun i hi => h i (by simp [occC, hi]))]
  | .eq a b, h => by
    simp only [evalC, congrE ρ ρ' maps a (fun i hi => h i (by simp [occC, hi])), congrE ρ ρ' maps b (fun i hi => h i (by simp [occC, hi]))]
  | .and a b, h => by
    simp only [evalC, congrC ρ ρ' maps a (fun i hi => h i (by simp [occC, hi])), congrC ρ ρ' maps b (fun i hi => h i (by simp [occC, hi]))]
  | .or a b, h => by
    simp only [evalC, congrC ρ ρ' maps a (fun i hi => h i (by simp [occC, hi])), congrC ρ ρ' maps b (fun i hi => h i (by simp [occC, hi]))]
  | .not a, h => by simp only [evalC, congrC ρ ρ' maps a (fun i hi => h i (by simp [occC, hi]))]
end

structure Machine where
  inputs : List Nat
  init : List (Nat × E)   -- each state variable's start, over the params
  step : List (Nat × E)   -- each state variable after a request, over params, inputs and state
  pre : C                 -- about the params alone: a precondition, so it holds at the start and at every step
  assume : C              -- about each request (and the params); holds at a step, not at the start

-- A request: its inputs replace those variables; nothing else changes until the step.
def withInputs (inputs : List Nat) (ρ ι : Nat → Nat) : Nat → Nat := fun i => if inputs.contains i then ι i else ρ i

inductive Reach (m : Machine) (maps : Nat → Nat → Nat) : (Nat → Nat) → Prop
  | start (ρ : Nat → Nat) : evalC ρ maps m.pre = true → Reach m maps (applyS m.init ρ maps)
  | step (ρ ι : Nat → Nat) : Reach m maps ρ → evalC (withInputs m.inputs ρ ι) maps m.assume = true →
      Reach m maps (applyS m.step (withInputs m.inputs ρ ι) maps)

def startGoal (m : Machine) (law : C) : List C := [m.pre, .not (substC m.init law)]
def stepGoal (m : Machine) (laws : List C) (law : C) : List C := [m.pre, m.assume] ++ laws ++ [.not (substC m.step law)]

-- Per law: the law, then (table, tree) for its start goal and for its step goal.
abbrev MachineProof := List (C × (List VDef × Tree) × (List VDef × Tree))

-- None of `vs` occurs in c.
def avoids (vs : List Nat) (c : C) : Bool := vs.all fun i => !occC i c

-- The precondition reads only params: no input, no variable the start or a step assigns.
def preOk (m : Machine) : Bool := avoids (m.inputs ++ m.init.map (·.1) ++ m.step.map (·.1)) m.pre

def checkMachine (m : Machine) (ps : MachineProof) : Bool :=
  preOk m && ps.all fun p => avoids m.inputs p.1
    && checkGoal ⟨p.2.1.1, startGoal m p.1⟩ p.2.1.2
    && checkGoal ⟨p.2.2.1, stepGoal m (ps.map (·.1)) p.1⟩ p.2.2.2

theorem avoids_occ {vs : List Nat} {c : C} (h : avoids vs c = true) {i : Nat} (hi : occC i c = true) : i ∉ vs := by
  intro hm
  simp only [avoids, List.all_eq_true] at h
  have := h i hm; simp [hi] at this

theorem assoc_mem {σ : List (Nat × E)} {i : Nat} {e : E} (h : assoc σ i = some e) : i ∈ σ.map (·.1) := by
  simp only [assoc, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, _⟩ := h
  have ⟨hm, hp⟩ := lookup_some ha
  simp only [beq_iff_eq] at hp
  exact List.mem_map.mpr ⟨a, hm, hp⟩

-- σ leaves every variable it doesn't assign alone.
theorem applyS_other {σ : List (Nat × E)} {i : Nat} (h : i ∉ σ.map (·.1)) (ρ : Nat → Nat) (maps : Nat → Nat → Nat) :
    applyS σ ρ maps i = ρ i := by
  simp only [applyS]
  cases ha : assoc σ i with
  | none => rfl
  | some e => exact absurd (assoc_mem ha) h

theorem withInputs_other {inputs : List Nat} {i : Nat} (h : i ∉ inputs) (ρ ι : Nat → Nat) : withInputs inputs ρ ι i = ρ i := by
  simp only [withInputs]; split
  · rename_i hc; exact absurd (List.contains_iff_mem.mp hc) h
  · rfl

-- Conditions that avoid some variables read the same before and after anything that only changes those.
theorem evalC_avoids {vs : List Nat} {c : C} (h : avoids vs c = true) {ρ ρ' : Nat → Nat} (maps : Nat → Nat → Nat)
    (hρ : ∀ i, i ∉ vs → ρ i = ρ' i) : evalC ρ maps c = evalC ρ' maps c :=
  congrC ρ ρ' maps c (fun i hi => hρ i (avoids_occ h hi))

theorem pre_reach {m : Machine} (hp : preOk m = true) {maps : Nat → Nat → Nat} :
    ∀ {ρ}, Reach m maps ρ → evalC ρ maps m.pre = true := by
  intro ρ hr
  induction hr with
  | start ρ h0 =>
    rw [evalC_avoids hp maps (ρ' := ρ) (fun i hi => applyS_other (fun h => hi (by simp [h])) ρ maps)]; exact h0
  | step ρ ι _ _ ih =>
    rw [evalC_avoids hp maps (ρ' := ρ) (fun i hi => by
      rw [applyS_other (fun h => hi (by simp [h])), withInputs_other (fun h => hi (by simp [h]))])]; exact ih

/-- The induction rule: for params that meet the precondition, every law of an accepted machine proof holds in every
reachable state, for any maps. -/
theorem machine_sound (m : Machine) (ps : MachineProof) (h : checkMachine m ps = true) (maps : Nat → Nat → Nat) :
    ∀ ρ, Reach m maps ρ → ∀ l ∈ ps.map (·.1), evalC ρ maps l = true := by
  simp only [checkMachine, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨hpre, h⟩ := h
  intro ρ hr
  induction hr with
  | start ρ h0 =>
    intro l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    have hs := sound _ _ (h p hp).1.2 ρ maps
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
    have hs := sound _ _ (h p hp).2 (withInputs m.inputs ρ ι) maps
    apply Decidable.byContradiction
    intro hf
    apply hs
    intro c hc
    simp only [stepGoal, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl) | hc) | rfl
    · rw [evalC_avoids hpre maps (ρ' := ρ) (fun i hi => withInputs_other (fun h => hi (by simp [h])) ρ ι)]
      exact pre_reach hpre hr
    · exact ha
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
      rw [evalC_avoids (h q hq).1.1 maps (ρ' := ρ) (fun i hi => withInputs_other hi ρ ι)]
      exact ih q.1 (List.mem_map.mpr ⟨q, hq, rfl⟩)
    · simp only [evalC, subst_evalC]; simpa using hf

/-! Loops: termination. A loop runs `body` while `guard` holds, each turn reading fresh inputs that meet `assume`. That it
halts is a liveness of its machine (Live.lean's Loop.machine and loop_halts_of): from anywhere, the guard fails later. -/

structure Loop where
  inputs : List Nat
  init : List (Nat × E)
  body : List (Nat × E)
  guard : C               -- while
  pre : C                 -- about the params alone
  assume : C              -- about each turn's inputs

-- One turn: some inputs meeting the assumption, the guard holds, the body runs.
def Turn (l : Loop) (maps : Nat → Nat → Nat) (ρ ρ' : Nat → Nat) : Prop :=
  ∃ ι, evalC (withInputs l.inputs ρ ι) maps l.guard = true ∧ evalC (withInputs l.inputs ρ ι) maps l.assume = true ∧
    ρ' = applyS l.body (withInputs l.inputs ρ ι) maps

/-! Folds over binary trees: structural induction. Each leaf and node carries its own inputs; a leaf's state comes from
its inputs, a node's from its children's (read through copies of the state variables, one per side) and its inputs.
The goals are built here: each law holds at every leaf, and at a node whenever every law holds at both children. -/

structure Fold where
  inputs : List Nat
  state : List (Nat × Nat × Nat)   -- a state variable, its copy for the left child, its copy for the right child
  leaf : List (Nat × E)
  node : List (Nat × E)
  pre : C
  assume : C

inductive BTree where
  | leaf (ι : Nat → Nat)
  | node (ι : Nat → Nat) (l r : BTree)

-- A node's environment: each copy reads the child's state variable.
def withChildren (f : Fold) (env a b : Nat → Nat) : Nat → Nat := fun i =>
  match lookup (fun e => e.2.1 == i) f.state with
  | some e => a e.1
  | none => match lookup (fun e => e.2.2 == i) f.state with
    | some e => b e.1
    | none => env i

def foldT (f : Fold) (ρ : Nat → Nat) (maps : Nat → Nat → Nat) : BTree → Nat → Nat
  | .leaf ι => applyS f.leaf (withInputs f.inputs ρ ι) maps
  | .node ι l r => applyS f.node (withChildren f (withInputs f.inputs ρ ι) (foldT f ρ maps l) (foldT f ρ maps r)) maps

-- Every leaf's and node's inputs meet the assumption.
def Allowed (f : Fold) (ρ : Nat → Nat) (maps : Nat → Nat → Nat) : BTree → Prop
  | .leaf ι => evalC (withInputs f.inputs ρ ι) maps f.assume = true
  | .node ι l r => evalC (withChildren f (withInputs f.inputs ρ ι) (foldT f ρ maps l) (foldT f ρ maps r)) maps f.assume = true
      ∧ Allowed f ρ maps l ∧ Allowed f ρ maps r

def leftSub (f : Fold) : List (Nat × E) := f.state.map fun e => (e.1, .var e.2.1)
def rightSub (f : Fold) : List (Nat × E) := f.state.map fun e => (e.1, .var e.2.2)

def leafGoal (f : Fold) (law : C) : List C := [f.pre, f.assume, .not (substC f.leaf law)]
def nodeGoal (f : Fold) (laws : List C) (law : C) : List C :=
  [f.pre, f.assume] ++ laws.flatMap (fun h => [substC (leftSub f) h, substC (rightSub f) h]) ++ [.not (substC f.node law)]

-- Variables a fold changes or reads per tree: inputs, the copies, and whatever a leaf or node assigns.
def touched (f : Fold) : List Nat :=
  f.inputs ++ f.state.map (·.2.1) ++ f.state.map (·.2.2) ++ f.leaf.map (·.1) ++ f.node.map (·.1)
-- Copies name one state variable each, and no right copy is a left copy.
def copiesOk (f : Fold) : Bool :=
  f.state.all fun e => f.state.all fun e' => (e.2.1 != e'.2.1 || e.1 == e'.1) && (e.2.2 != e'.2.2 || e.1 == e'.1) && e.2.2 != e'.2.1

-- Per law: the law, then (table, tree) for its leaf goal and its node goal.
abbrev FoldProof := MachineProof

def checkFold (f : Fold) (ps : FoldProof) : Bool :=
  copiesOk f && avoids (touched f) f.pre
    && ps.all fun p => avoids ((touched f).filter fun i => !(f.state.map (·.1)).contains i) p.1
      && checkGoal ⟨p.2.1.1, leafGoal f p.1⟩ p.2.1.2
      && checkGoal ⟨p.2.2.1, nodeGoal f (ps.map (·.1)) p.1⟩ p.2.2.2

theorem lookup_none {α : Type} {p : α → Bool} {l : List α} (h : ∀ a ∈ l, p a = false) : lookup p l = none := by
  cases hl : lookup p l with
  | none => rfl
  | some a => have := lookup_some hl; simp [h a this.1] at this

theorem lookup_none_all {α : Type} {p : α → Bool} : ∀ {l : List α}, lookup p l = none → ∀ a ∈ l, p a = false
  | [], _, a, ha => by simp at ha
  | b :: bs, h, a, ha => by
    simp only [lookup] at h
    split at h
    · simp at h
    · rcases List.mem_cons.mp ha with rfl | ha
      · simpa using (by assumption : ¬ p a = true)
      · exact lookup_none_all h a ha

theorem withChildren_plain (f : Fold) (env a b : Nat → Nat) {i : Nat} (hl : i ∉ f.state.map (·.2.1))
    (hr : i ∉ f.state.map (·.2.2)) : withChildren f env a b i = env i := by
  simp only [withChildren]
  rw [lookup_none (fun e he => by simp only [beq_eq_false_iff_ne]; intro h; exact hl (List.mem_map.mpr ⟨e, he, h⟩)),
    lookup_none (fun e he => by simp only [beq_eq_false_iff_ne]; intro h; exact hr (List.mem_map.mpr ⟨e, he, h⟩))]

theorem withChildren_left {f : Fold} (hc : copiesOk f = true) (env a b : Nat → Nat) {e : Nat × Nat × Nat} (he : e ∈ f.state) :
    withChildren f env a b e.2.1 = a e.1 := by
  simp only [copiesOk, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
  simp only [withChildren]
  cases h : lookup (fun e' => e'.2.1 == e.2.1) f.state with
  | none => have := lookup_none_all h e he; simp at this
  | some e' =>
    have ⟨hm, hp⟩ := lookup_some h
    simp only [beq_iff_eq] at hp
    have := (hc e' hm e he).1.1
    simp only [hp, not_true_eq_false, false_or] at this
    simp only [this]

theorem withChildren_right {f : Fold} (hc : copiesOk f = true) (env a b : Nat → Nat) {e : Nat × Nat × Nat} (he : e ∈ f.state) :
    withChildren f env a b e.2.2 = b e.1 := by
  simp only [copiesOk, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
  simp only [withChildren]
  rw [lookup_none (fun e' he' => by simp only [beq_eq_false_iff_ne]; intro h; exact (hc e he e' he').2 h.symm)]
  cases h : lookup (fun e' => e'.2.2 == e.2.2) f.state with
  | none => have := lookup_none_all h e he; simp at this
  | some e' =>
    have ⟨hm, hp⟩ := lookup_some h
    simp only [beq_iff_eq] at hp
    have := (hc e' hm e he).1.2
    simp only [hp, not_true_eq_false, false_or] at this
    simp only [this]

theorem foldT_other (f : Fold) (ρ : Nat → Nat) (maps : Nat → Nat → Nat) {i : Nat} (hi : i ∉ touched f) :
    ∀ t, foldT f ρ maps t i = ρ i
  | .leaf ι => by
    simp only [foldT]
    rw [applyS_other (fun h => hi (by simp [touched, h])), withInputs_other (fun h => hi (by simp [touched, h]))]
  | .node ι l r => by
    simp only [foldT]
    rw [applyS_other (fun h => hi (by simp [touched, h])), withChildren_plain _ _ _ _ (fun h => hi (by simp [touched, h]))
      (fun h => hi (by simp [touched, h])), withInputs_other (fun h => hi (by simp [touched, h]))]

theorem assoc_map {s : List (Nat × Nat × Nat)} {g : Nat × Nat × Nat → Nat} {i : Nat} {x : E}
    (h : assoc (s.map fun e => (e.1, E.var (g e))) i = some x) : ∃ e ∈ s, e.1 = i ∧ x = .var (g e) := by
  simp only [assoc, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  have ⟨hm, hp⟩ := lookup_some ha
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
  simp only [beq_iff_eq] at hp
  exact ⟨e, he, hp, rfl⟩

theorem assoc_map_none {s : List (Nat × Nat × Nat)} {g : Nat × Nat × Nat → Nat} {i : Nat} (hi : i ∉ s.map (·.1)) :
    assoc (s.map fun e => (e.1, E.var (g e))) i = none := by
  cases h : assoc (s.map fun e => (e.1, E.var (g e))) i with
  | none => rfl
  | some x => obtain ⟨e, he, rfl, -⟩ := assoc_map h; exact absurd (List.mem_map.mpr ⟨e, he, rfl⟩) hi

theorem assoc_map_some {s : List (Nat × Nat × Nat)} {g : Nat × Nat × Nat → Nat} {i : Nat} (hi : i ∈ s.map (·.1))
    (h : assoc (s.map fun e => (e.1, E.var (g e))) i = none) : False := by
  simp only [assoc, Option.map_eq_none_iff] at h
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
  have := lookup_none_all h (e.1, E.var (g e)) (List.mem_map.mpr ⟨e, he, rfl⟩)
  simp at this

-- With no assumption (the trivially true one), every tree is allowed.
theorem allowed_trivial (f : Fold) (h : f.assume = .le (.const 0) (.const 0)) (ρ : Nat → Nat) (maps : Nat → Nat → Nat) :
    ∀ t, Allowed f ρ maps t
  | .leaf ι => by simp [Allowed, h, evalC, evalE]
  | .node ι l r => ⟨by simp [h, evalC, evalE], allowed_trivial f h ρ maps l, allowed_trivial f h ρ maps r⟩

/-- Structural induction: for params that meet the precondition, every law of an accepted fold proof holds of every
tree whose inputs meet the assumption, for any maps. -/
theorem fold_sound (f : Fold) (ps : FoldProof) (h : checkFold f ps = true) (maps : Nat → Nat → Nat) (ρ : Nat → Nat)
    (h0 : evalC ρ maps f.pre = true) : ∀ t, Allowed f ρ maps t → ∀ l ∈ ps.map (·.1), evalC (foldT f ρ maps t) maps l = true := by
  simp only [checkFold, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hc, hpre⟩, h⟩ := h
  have preAt : ∀ env : Nat → Nat, (∀ i, i ∉ touched f → env i = ρ i) → evalC env maps f.pre = true := fun env he => by
    rw [evalC_avoids hpre maps (ρ' := ρ) he]; exact h0
  -- What a law reads: the state variables, or variables no tree changes.
  have reads : ∀ q ∈ ps, ∀ i, occC i q.1 = true → i ∈ f.state.map (·.1) ∨ i ∉ touched f := by
    intro q hq i hi
    by_cases hs : i ∈ f.state.map (·.1)
    · exact Or.inl hs
    · refine Or.inr fun ht => avoids_occ (h q hq).1.1 hi ?_
      simp only [List.mem_filter, ht, true_and, Bool.not_eq_true', List.contains_iff_mem]
      simpa using hs
  intro t
  induction t with
  | leaf ι =>
    intro ha l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    apply Decidable.byContradiction; intro hn
    apply sound _ _ (h p hp).1.2 (withInputs f.inputs ρ ι) maps
    intro c hc
    simp only [leafGoal, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact preAt _ (fun i hi => withInputs_other (fun h => hi (by simp [touched, h])) ρ ι)
    · exact ha
    · simp only [evalC, subst_evalC]; simpa [foldT] using hn
  | node ι lt rt ihl ihr =>
    intro ha l hl
    obtain ⟨hA, hal, har⟩ := ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    let Env := withChildren f (withInputs f.inputs ρ ι) (foldT f ρ maps lt) (foldT f ρ maps rt)
    -- A law at a child, read through that side's copies.
    have side : ∀ (g : Nat × Nat × Nat → Nat) (child : BTree),
        (∀ e ∈ f.state, Env (g e) = foldT f ρ maps child e.1) → ∀ q ∈ ps,
        evalC Env maps (substC (f.state.map fun e => (e.1, E.var (g e))) q.1) = evalC (foldT f ρ maps child) maps q.1 := by
      intro g child hg q hq
      rw [subst_evalC]
      refine congrC _ _ maps q.1 (fun i hi => ?_)
      cases hx : assoc (f.state.map fun e => (e.1, E.var (g e))) i with
      | some x =>
        obtain ⟨e, he, rfl, rfl⟩ := assoc_map hx
        simp only [applyS, hx, evalE]; exact hg e he
      | none =>
        have hs : i ∉ f.state.map (·.1) := fun hm => assoc_map_some (g := g) hm hx
        have ht : i ∉ touched f := (reads q hq i hi).resolve_left hs
        simp only [applyS, hx, Env]
        rw [withChildren_plain _ _ _ _ (fun h => ht (by simp [touched, h])) (fun h => ht (by simp [touched, h])),
          withInputs_other (fun h => ht (by simp [touched, h])), foldT_other f ρ maps ht]
    apply Decidable.byContradiction; intro hn
    apply sound _ _ (h p hp).2 Env maps
    intro c hc'
    simp only [nodeGoal, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      List.mem_flatMap] at hc'
    rcases hc' with ((rfl | rfl) | ⟨q, hq, hcq⟩) | rfl
    · exact preAt Env (fun i hi => by
        simp only [Env]
        rw [withChildren_plain _ _ _ _ (fun h => hi (by simp [touched, h])) (fun h => hi (by simp [touched, h])),
          withInputs_other (fun h => hi (by simp [touched, h]))])
    · exact hA
    · obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
      rcases hcq with rfl | rfl
      · simp only [leftSub]
        rw [side (·.2.1) lt (fun e he => withChildren_left hc _ _ _ he) q' hq']
        exact ihl hal _ (List.mem_map.mpr ⟨q', hq', rfl⟩)
      · simp only [rightSub]
        rw [side (·.2.2) rt (fun e he => withChildren_right hc _ _ _ he) q' hq']
        exact ihr har _ (List.mem_map.mpr ⟨q', hq', rfl⟩)
    · simp only [evalC, subst_evalC]; simpa [foldT, Env] using hn

/-! Step machines with maps. A step may write each map at one key (read-over-write: a read after the step is the
written value at the written key, the old cell elsewhere). A law may hold at every key: it is proven at a fresh skolem
variable and assumed, before the step, at whatever keys the proof names (instantiating ∀ is sound at any term). The
goals are built here, as for scalar machines. -/

mutual
def readsE : E → Bool
  | .var _ => false
  | .const _ => false
  | .add a b => readsE a || readsE b
  | .sub a b => readsE a || readsE b
  | .mul _ a => readsE a
  | .min a b => readsE a || readsE b
  | .max a b => readsE a || readsE b
  | .prod a b => readsE a || readsE b
  | .ite c t f => readsC c || readsE t || readsE f
  | .get _ _ => true
def readsC : C → Bool
  | .le a b => readsE a || readsE b
  | .lt a b => readsE a || readsE b
  | .eq a b => readsE a || readsE b
  | .and a b => readsC a || readsC b
  | .or a b => readsC a || readsC b
  | .not a => readsC a
end

mutual
theorem noReadsE (ρ : Nat → Nat) (M M' : Nat → Nat → Nat) : (e : E) → readsE e = false → evalE ρ M e = evalE ρ M' e
  | .var _, _ => rfl
  | .const _, _ => rfl
  | .add a b, h => by simp only [readsE, Bool.or_eq_false_iff] at h; simp only [evalE, noReadsE ρ M M' a h.1, noReadsE ρ M M' b h.2]
  | .sub a b, h => by simp only [readsE, Bool.or_eq_false_iff] at h; simp only [evalE, noReadsE ρ M M' a h.1, noReadsE ρ M M' b h.2]
  | .mul _ a, h => by simp only [readsE] at h; simp only [evalE, noReadsE ρ M M' a h]
  | .min a b, h => by simp only [readsE, Bool.or_eq_false_iff] at h; simp only [evalE, noReadsE ρ M M' a h.1, noReadsE ρ M M' b h.2]
  | .max a b, h => by simp only [readsE, Bool.or_eq_false_iff] at h; simp only [evalE, noReadsE ρ M M' a h.1, noReadsE ρ M M' b h.2]
  | .prod a b, h => by simp only [readsE, Bool.or_eq_false_iff] at h; simp only [evalE, noReadsE ρ M M' a h.1, noReadsE ρ M M' b h.2]
  | .ite c t f, h => by
    simp only [readsE, Bool.or_eq_false_iff] at h
    simp only [evalE, noReadsC ρ M M' c h.1.1, noReadsE ρ M M' t h.1.2, noReadsE ρ M M' f h.2]
  | .get _ _, h => by simp [readsE] at h
theorem noReadsC (ρ : Nat → Nat) (M M' : Nat → Nat → Nat) : (c : C) → readsC c = false → evalC ρ M c = evalC ρ M' c
  | .le a b, h => by simp only [readsC, Bool.or_eq_false_iff] at h; simp only [evalC, noReadsE ρ M M' a h.1, noReadsE ρ M M' b h.2]
  | .lt a b, h => by simp only [readsC, Bool.or_eq_false_iff] at h; simp only [evalC, noReadsE ρ M M' a h.1, noReadsE ρ M M' b h.2]
  | .eq a b, h => by simp only [readsC, Bool.or_eq_false_iff] at h; simp only [evalC, noReadsE ρ M M' a h.1, noReadsE ρ M M' b h.2]
  | .and a b, h => by simp only [readsC, Bool.or_eq_false_iff] at h; simp only [evalC, noReadsC ρ M M' a h.1, noReadsC ρ M M' b h.2]
  | .or a b, h => by simp only [readsC, Bool.or_eq_false_iff] at h; simp only [evalC, noReadsC ρ M M' a h.1, noReadsC ρ M M' b h.2]
  | .not a, h => by simp only [readsC] at h; simp only [evalC, noReadsC ρ M M' a h]
end

-- Substitution of variables by σ and of each read by `rd` (applied to the substituted key).
mutual
def substRE (σ : List (Nat × E)) (rd : Nat → E → E) : E → E
  | .var i => match assoc σ i with
    | some e => e
    | none => .var i
  | .const n => .const n
  | .add a b => .add (substRE σ rd a) (substRE σ rd b)
  | .sub a b => .sub (substRE σ rd a) (substRE σ rd b)
  | .mul k a => .mul k (substRE σ rd a)
  | .min a b => .min (substRE σ rd a) (substRE σ rd b)
  | .max a b => .max (substRE σ rd a) (substRE σ rd b)
  | .prod a b => .prod (substRE σ rd a) (substRE σ rd b)
  | .ite c t f => .ite (substRC σ rd c) (substRE σ rd t) (substRE σ rd f)
  | .get m key => rd m (substRE σ rd key)
def substRC (σ : List (Nat × E)) (rd : Nat → E → E) : C → C
  | .le a b => .le (substRE σ rd a) (substRE σ rd b)
  | .lt a b => .lt (substRE σ rd a) (substRE σ rd b)
  | .eq a b => .eq (substRE σ rd a) (substRE σ rd b)
  | .and a b => .and (substRC σ rd a) (substRC σ rd b)
  | .or a b => .or (substRC σ rd a) (substRC σ rd b)
  | .not a => .not (substRC σ rd a)
end

section
variable (σ : List (Nat × E)) (rd : Nat → E → E) (W : Nat → Nat) (M M' : Nat → Nat → Nat)
  (hrd : ∀ m k, evalE W M (rd m k) = M' m (evalE W M k))
include hrd
mutual
theorem substR_evalE : (e : E) → evalE W M (substRE σ rd e) = evalE (applyS σ W M) M' e
  | .var i => by
    simp only [substRE]
    cases h : assoc σ i <;> simp [evalE, applyS, h]
  | .const n => by simp [substRE, evalE]
  | .add a b => by simp [substRE, evalE, substR_evalE a, substR_evalE b]
  | .sub a b => by simp [substRE, evalE, substR_evalE a, substR_evalE b]
  | .mul k a => by simp [substRE, evalE, substR_evalE a]
  | .min a b => by simp [substRE, evalE, substR_evalE a, substR_evalE b]
  | .max a b => by simp [substRE, evalE, substR_evalE a, substR_evalE b]
  | .prod a b => by simp [substRE, evalE, substR_evalE a, substR_evalE b]
  | .ite c t f => by simp [substRE, evalE, substR_evalC c, substR_evalE t, substR_evalE f]
  | .get m key => by simp only [substRE, evalE, hrd, substR_evalE key]
theorem substR_evalC : (c : C) → evalC W M (substRC σ rd c) = evalC (applyS σ W M) M' c
  | .le a b => by simp [substRC, evalC, substR_evalE a, substR_evalE b]
  | .lt a b => by simp [substRC, evalC, substR_evalE a, substR_evalE b]
  | .eq a b => by simp [substRC, evalC, substR_evalE a, substR_evalE b]
  | .and a b => by simp [substRC, evalC, substR_evalC a, substR_evalC b]
  | .or a b => by simp [substRC, evalC, substR_evalC a, substR_evalC b]
  | .not a => by simp [substRC, evalC, substR_evalC a]
end
end

structure MMachine where
  inputs : List Nat
  init : List (Nat × E)
  maps0 : List (Nat × Nat)       -- each map's value at every key at the start
  step : List (Nat × E)
  writes : List (Nat × E × E)    -- a map, the key it's written at and the value, over the state before the step
  pre : C                        -- about the params alone, reading no map
  assume : C                     -- about each request

def writeMaps (ws : List (Nat × E × E)) (W : Nat → Nat) (M : Nat → Nat → Nat) : Nat → Nat → Nat := fun m key =>
  match lookup (fun w => w.1 == m) ws with
  | some w => if key = evalE W M w.2.1 then evalE W M w.2.2 else M m key
  | none => M m key

def StartMaps (m : MMachine) (M : Nat → Nat → Nat) : Prop := ∀ p ∈ m.maps0, ∀ key, M p.1 key = p.2

inductive MReach (m : MMachine) : (Nat → Nat) → (Nat → Nat → Nat) → Prop
  | start (ρ : Nat → Nat) (M : Nat → Nat → Nat) : StartMaps m M → evalC ρ M m.pre = true → MReach m (applyS m.init ρ M) M
  | step (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) : MReach m ρ M →
      evalC (withInputs m.inputs ρ ι) M m.assume = true →
      MReach m (applyS m.step (withInputs m.inputs ρ ι) M) (writeMaps m.writes (withInputs m.inputs ρ ι) M)

def upd (ρ : Nat → Nat) (i v : Nat) : Nat → Nat := fun j => if j = i then v else ρ j

-- A law, and for a law about every key, the variable it holds at.
structure MLaw where
  holds : C
  key : Option Nat

def MLaw.Holds (l : MLaw) (ρ : Nat → Nat) (M : Nat → Nat → Nat) : Prop :=
  match l.key with
  | none => evalC ρ M l.holds = true
  | some kv => ∀ v, evalC (upd ρ kv v) M l.holds = true

def rdStart (m : MMachine) : Nat → E → E := fun mp k =>
  match lookup (fun p => p.1 == mp) m.maps0 with
  | some p => .const p.2
  | none => .get mp k
def rdStep (m : MMachine) : Nat → E → E := fun mp k =>
  match lookup (fun w => w.1 == mp) m.writes with
  | some w => .ite (.eq k w.2.1) w.2.2 (.get mp k)
  | none => .get mp k

-- What a goal proves: the law, at the skolem variable if it holds at every key.
def goalOf (l : MLaw) (sk : Nat) : C :=
  match l.key with
  | none => l.holds
  | some kv => substC [(kv, .var sk)] l.holds

structure MEntry where
  law : MLaw
  sk : Nat                    -- the skolem variable
  insts : List (Nat × E)      -- (law index, key): where the step goal assumes the laws about every key
  start : List VDef × Tree
  step : List VDef × Tree

def scalarHyps (laws : List MLaw) : List C := laws.filterMap fun l =>
  match l.key with
  | none => some l.holds
  | some _ => none
def instHyps (laws : List MLaw) (insts : List (Nat × E)) : List C := insts.filterMap fun p =>
  match laws[p.1]? with
  | some l => match l.key with
    | some kv => some (substC [(kv, p.2)] l.holds)
    | none => none
  | none => none

def mStartGoal (m : MMachine) (e : MEntry) : List C := [m.pre, .not (substRC m.init (rdStart m) (goalOf e.law e.sk))]
def mStepGoal (m : MMachine) (laws : List MLaw) (e : MEntry) : List C :=
  [m.pre, m.assume] ++ scalarHyps laws ++ instHyps laws e.insts ++ [.not (substRC m.step (rdStep m) (goalOf e.law e.sk))]

-- The skolem is fresh: no input or state variable, and nothing the machine or a law reads.
def skOk (m : MMachine) (laws : List MLaw) (sk : Nat) : Bool :=
  !(m.inputs ++ m.init.map (·.1) ++ m.step.map (·.1)).contains sk && !occC sk m.pre && !occC sk m.assume
    && laws.all (fun l => !occC sk l.holds) && m.init.all (fun p => !occE sk p.2) && m.step.all (fun p => !occE sk p.2)
    && m.writes.all (fun w => !occE sk w.2.1 && !occE sk w.2.2)

def checkMMachine (m : MMachine) (ps : List MEntry) : Bool :=
  avoids (m.inputs ++ m.init.map (·.1) ++ m.step.map (·.1)) m.pre && !readsC m.pre
    && ps.all fun e => avoids m.inputs e.law.holds && skOk m (ps.map (·.law)) e.sk
      && checkGoal ⟨e.start.1, mStartGoal m e⟩ e.start.2
      && checkGoal ⟨e.step.1, mStepGoal m (ps.map (·.law)) e⟩ e.step.2

theorem occ_false {i : Nat} {c : C} (h : (!occC i c) = true) : occC i c = false := by simpa using h

-- A law reads the same at the skolem as it holds at every key.
theorem goalOf_holds (l : MLaw) {sk : Nat} (hs : occC sk l.holds = false) (ρ : Nat → Nat) (M : Nat → Nat → Nat) :
    (∀ v, evalC (upd ρ sk v) M (goalOf l sk) = true) → l.Holds ρ M := by
  intro h
  unfold MLaw.Holds
  unfold goalOf at h
  split
  · rename_i hk
    simp only [hk] at h
    have := h 0
    rwa [congrC _ ρ M l.holds (fun i hi => by simp only [upd]; split <;> simp_all)] at this
  · rename_i kv hk
    simp only [hk] at h
    intro v
    have := h v
    rw [subst_evalC] at this
    rwa [congrC _ (upd ρ kv v) M l.holds (fun i hi => by
      simp only [applyS, assoc, lookup, upd]
      by_cases hik : i = kv
      · subst hik; simp [evalE, upd]
      · have hb : (kv == i) = false := by simp; omega
        simp only [hb, Bool.false_eq_true, ite_false, Option.map_none, hik]
        split <;> simp_all)] at this

theorem pre_mreach {m : MMachine} (hp : avoids (m.inputs ++ m.init.map (·.1) ++ m.step.map (·.1)) m.pre = true)
    (hr : readsC m.pre = false) : ∀ {ρ M}, MReach m ρ M → evalC ρ M m.pre = true := by
  intro ρ M h
  induction h with
  | start ρ M _ h0 =>
    rw [evalC_avoids hp M (ρ' := ρ) (fun i hi => applyS_other (fun h => hi (by simp [h])) ρ M)]; exact h0
  | step ρ M ι _ _ ih =>
    rw [noReadsC _ _ M m.pre hr]
    rw [evalC_avoids hp M (ρ' := ρ) (fun i hi => by
      rw [applyS_other (fun h => hi (by simp [h])), withInputs_other (fun h => hi (by simp [h]))])]; exact ih

-- With a fresh skolem, σ commutes with setting it.
theorem applyS_upd {σ : List (Nat × E)} {sk : Nat} (hk : sk ∉ σ.map (·.1)) (he : σ.all (fun p => !occE sk p.2) = true)
    (W : Nat → Nat) (M : Nat → Nat → Nat) (v : Nat) : applyS σ (upd W sk v) M = upd (applyS σ W M) sk v := by
  funext i
  simp only [upd]
  by_cases hi : i = sk
  · subst hi; rw [applyS_other hk]; simp [upd]
  · simp only [hi, ite_false, applyS]
    cases h : assoc σ i with
    | none => simp [upd, hi]
    | some e =>
      simp only [assoc, Option.map_eq_some_iff] at h
      obtain ⟨p, hp, rfl⟩ := h
      have hm := (lookup_some hp).1
      simp only [List.all_eq_true] at he
      have := he p hm
      exact congrE _ _ M p.2 (fun j hj => by simp only [upd]; split <;> simp_all)

/-- The induction rule with maps: for params that meet the precondition and maps that start as declared, every law of
an accepted proof holds in every reachable state (a law about every key, at every key). -/
theorem mmachine_sound (m : MMachine) (ps : List MEntry) (h : checkMMachine m ps = true) :
    ∀ ρ M, MReach m ρ M → ∀ e ∈ ps, e.law.Holds ρ M := by
  simp only [checkMMachine, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hpre, hrp⟩, h⟩ := h
  simp only [Bool.not_eq_true'] at hrp
  have hsk : ∀ e ∈ ps, _ := fun e he => (h e he).1.1.2
  intro ρ M hr
  induction hr with
  | start ρ M hM h0 =>
    intro e he
    obtain ⟨⟨⟨_, hs⟩, hst⟩, _⟩ := h e he
    simp only [skOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hs
    obtain ⟨⟨⟨⟨⟨⟨hfresh, hspre⟩, _⟩, hslaw⟩, hsinit⟩, _⟩, _⟩ := hs
    refine goalOf_holds e.law (by simpa using hslaw e.law (List.mem_map.mpr ⟨e, he, rfl⟩)) _ M (fun v => ?_)
    apply Decidable.byContradiction; intro hn
    apply sound _ _ hst (upd ρ e.sk v) M
    intro c hc
    simp only [mStartGoal, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rw [congrC _ ρ M m.pre (fun i hi => by simp only [upd]; split <;> simp_all)]; exact h0
    · have hrd : ∀ mp k, evalE (upd ρ e.sk v) M (rdStart m mp k) = M mp (evalE (upd ρ e.sk v) M k) := by
        intro mp k
        simp only [rdStart]
        split
        · rename_i p hp
          have ⟨hm, hq⟩ := lookup_some hp
          simp only [beq_iff_eq] at hq
          simp only [evalE]; rw [← hq, hM p hm]
        · rfl
      simp only [evalC, substR_evalC _ _ _ M M hrd]
      rw [applyS_upd (fun h => by simp [h] at hfresh) (by simpa [List.all_eq_true] using hsinit)]
      simpa using hn
  | step ρ M ι hr ha ih =>
    intro e he
    obtain ⟨⟨⟨hin, hs⟩, _⟩, hst⟩ := h e he
    simp only [skOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hs
    obtain ⟨⟨⟨⟨⟨⟨hfresh, hspre⟩, hsas⟩, hslaw⟩, _⟩, hsstep⟩, hsw⟩ := hs
    have hfresh' : e.sk ∉ m.inputs ∧ e.sk ∉ m.step.map (·.1) := by
      constructor <;> intro hm <;> simp [hm] at hfresh
    refine goalOf_holds e.law (by simpa using hslaw e.law (List.mem_map.mpr ⟨e, he, rfl⟩)) _ _ (fun v => ?_)
    let W0 := withInputs m.inputs ρ ι
    apply Decidable.byContradiction; intro hn
    apply sound _ _ hst (upd W0 e.sk v) M
    -- Reading a law about the state before the step, at the goal's environment.
    have before : ∀ (l : MLaw), l ∈ ps.map (·.law) → ∀ (g : Nat → Nat), (∀ i, i ∉ m.inputs → i ≠ e.sk → g i = ρ i) →
        avoids m.inputs l.holds = true → occC e.sk l.holds = false → ∀ c, c = l.holds → evalC g M c = evalC ρ M l.holds := by
      intro l _ g hg hl hsl c hc; subst hc
      exact congrC _ _ M l.holds (fun i hi => hg i (avoids_occ hl hi) (by intro h'; subst h'; simp [hsl] at hi))
    intro c hc
    simp only [mStepGoal, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with (((rfl | rfl) | hc) | hc) | rfl
    · rw [congrC _ ρ M m.pre (fun i hi => by
        simp only [upd, W0]
        split
        · rename_i h'; subst h'; simp [hspre] at hi
        · exact withInputs_other (fun hm => avoids_occ hpre hi (by simp [hm])) ρ ι)]
      exact pre_mreach hpre hrp hr
    · rw [congrC _ W0 M m.assume (fun i hi => by simp only [upd]; split <;> simp_all)]; exact ha
    · simp only [scalarHyps, List.mem_filterMap] at hc
      obtain ⟨l, hl, hk⟩ := hc
      split at hk
      · rename_i hkey
        simp only [Option.some.injEq] at hk; subst hk
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp hl
        have := ih e' he'
        simp only [MLaw.Holds, hkey] at this
        rw [before e'.law hl _ (fun i hi hs' => by simp only [upd, hs', ite_false, W0]; exact withInputs_other hi ρ ι)
          (h e' he').1.1.1 (by simpa using hslaw e'.law hl) _ rfl]
        exact this
      · simp at hk
    · simp only [instHyps, List.mem_filterMap] at hc
      obtain ⟨p, _, hk⟩ := hc
      split at hk
      · rename_i l hl
        split at hk
        · rename_i kv hkey
          simp only [Option.some.injEq] at hk; subst hk
          have hlm : l ∈ ps.map (·.law) := List.mem_of_getElem? hl
          obtain ⟨e', he', rfl⟩ := List.mem_map.mp hlm
          have := ih e' he'
          simp only [MLaw.Holds, hkey] at this
          rw [subst_evalC]
          have hsl : occC e.sk e'.law.holds = false := by simpa using hslaw e'.law hlm
          rw [congrC _ (upd ρ kv (evalE (upd W0 e.sk v) M p.2)) M e'.law.holds (fun i hi => by
            simp only [applyS, assoc, lookup, upd]
            by_cases hik : i = kv
            · subst hik; simp
            · have hb : (kv == i) = false := by simp; omega
              have hs' : i ≠ e.sk := by intro h'; subst h'; simp [hsl] at hi
              simp only [hb, Bool.false_eq_true, ite_false, Option.map_none, hik, hs', W0]
              exact withInputs_other (avoids_occ (h e' he').1.1.1 hi) ρ ι)]
          exact this _
        · simp at hk
      · simp at hk
    · have hrd : ∀ mp k, evalE (upd W0 e.sk v) M (rdStep m mp k) = writeMaps m.writes W0 M mp (evalE (upd W0 e.sk v) M k) := by
        intro mp k
        simp only [rdStep, writeMaps]
        split
        · rename_i w hw
          have hm := (lookup_some hw).1
          have h1 := hsw w hm
          try simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
          have e1 : evalE (upd W0 e.sk v) M w.2.1 = evalE W0 M w.2.1 :=
            congrE _ _ M _ (fun j hj => by simp only [upd]; split <;> simp_all)
          have e2 : evalE (upd W0 e.sk v) M w.2.2 = evalE W0 M w.2.2 :=
            congrE _ _ M _ (fun j hj => by simp only [upd]; split <;> simp_all)
          simp only [evalE, evalC, e1, e2]
          by_cases hk : evalE (upd W0 e.sk v) M k = evalE W0 M w.2.1 <;> simp [hk]
        · rfl
      simp only [evalC, substR_evalC _ _ _ M _ hrd]
      rw [applyS_upd hfresh'.2 (by simpa [List.all_eq_true] using hsstep)]
      simpa using hn

end Kern

#print axioms Kern.sound
#print axioms Kern.machine_sound
#print axioms Kern.fold_sound
#print axioms Kern.mmachine_sound

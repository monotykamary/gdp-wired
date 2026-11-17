import WordDivisionBridge
import WordColumns
import WordLex
import WordOne

/-! The full syntactic word-division fact schema.  A map read premise is a
property of the concrete word interpretation, never an assumption about a
fact produced by this schema. -/
namespace WordFacts
open Kern

structure Spec where
  width : Nat
  args : List E
  qMaps : List Nat
  rMaps : List Nat
  cMaps : List Nat

/-- Right-associated tuple key, matching kernel/word-division.ts. -/
def tupleKey : List E → E
  | [] => .const 0
  | [x] => x
  | x :: xs => .tup x (tupleKey xs)

namespace Spec
def key (s : Spec) : E := tupleKey s.args
def n (s : Spec) : Nat := WordDivision.limbs s.width
def base (s : Spec) : Nat := WordDivision.radix s.width

def a (s : Spec) (i : Nat) : E := s.args[i]?.getD (.const 0)
def b (s : Spec) (i : Nat) : E := s.args[s.n+i]?.getD (.const 0)
def q (s : Spec) (i : Nat) : E := .get (s.qMaps[i]?.getD 0) s.key
def r (s : Spec) (i : Nat) : E := .get (s.rMaps[i]?.getD 0) s.key
def c (s : Spec) (i : Nat) : E :=
  if i = 0 then .const 0 else .get (s.cMaps[i-1]?.getD 0) s.key
end Spec

/-- Width, tuple arity, and all slots exactly match the TypeScript name parser. -/
def Spec.Valid (s : Spec) : Prop :=
  s.width ∈ [8, 16, 32, 64] ∧ s.args.length = 2*s.n ∧
  s.qMaps.length = s.n ∧ s.rMaps.length = s.n ∧ s.cMaps.length = 2*s.n

/-- The exporter retains a connective even for a singleton, using a neutral
binary child, exactly leanConnective in lean-kernel/lean-terms.ts. -/
def both : List C → C
  | [] => .le (.const 0) (.const 0)
  | [x] => .and x (.le (.const 0) (.const 0))
  | [x, y] => .and x y
  | x :: xs => .and x (both xs)
def either : List C → C
  | [] => .lt (.const 0) (.const 0)
  | [x] => .or x (.lt (.const 0) (.const 0))
  | [x, y] => .or x y
  | x :: xs => .or x (either xs)

def sumE (xs : List E) : E := xs.foldl E.add (.const 0)
def domain (s : Spec) : C :=
  both ((List.range (2*s.n)).map (fun i => C.lt (s.args[i]?.getD (.const 0)) (.const s.base)) ++
    [either ((List.range s.n).map (fun i => C.lt (.const 0) (s.b i)))])
def guarded (s : Spec) (fact : C) : C :=
  either [.not (domain s), fact]

def lex (xs ys : List E) (strict : Bool) : C :=
  let m := xs.length
  either (((List.range m).reverse.map fun i =>
    both (((List.range (m-i-1)).map (fun j => .eq (xs[i+1+j]?.getD (.const 0))
      (ys[i+1+j]?.getD (.const 0)))) ++
      [.lt (xs[i]?.getD (.const 0)) (ys[i]?.getD (.const 0))])) ++
    if strict then [] else [both ((List.range m).map fun i =>
      .eq (xs[i]?.getD (.const 0)) (ys[i]?.getD (.const 0)))])

def column (s : Spec) (i : Nat) : C :=
  let products := ((List.range s.n).filter fun j => j ≤ i && i-j < s.n).map
    (fun j => E.prod (s.q j) (s.b (i-j)))
  .eq (sumE ([s.c i] ++ (if i < s.n then [s.r i] else []) ++ products))
    (sumE [if i < s.n then s.a i else .const 0, .mul s.base (s.c (i+1))])

/-- Unconditional range clauses of the generator, including zero divisor. -/
def rangeFacts (s : Spec) : List C :=
  ((List.range s.n).map (fun i => C.lt (s.q i) (.const s.base))) ++
  ((List.range s.n).map (fun i => C.lt (s.r i) (.const s.base))) ++
  ((List.range (2*s.n)).map (fun j => C.le (s.c (j+1)) (.const (s.n*s.base))))

def bOne (s : Spec) : C :=
  both ([.eq (s.b 0) (.const 1)] ++
    ((List.range (s.n-1)).map fun j => .eq (s.b (j+1)) (.const 0)))
def oneResult (s : Spec) : C :=
  both (((List.range s.n).map fun i => .eq (s.q i) (s.a i)) ++
    ((List.range s.n).map fun i => .eq (s.r i) (.const 0)))
def oneClause (s : Spec) : C := either [.not (bOne s), oneResult s]

/-- Exactly the list emitted by wordDivisionFacts for one encountered key. -/
def facts (s : Spec) : List C :=
  rangeFacts s ++
  ((List.range (2*s.n)).map (fun i => guarded s (column s i))) ++
  [guarded s (.eq (s.c s.n) (.const 0)),
   guarded s (lex ((List.range s.n).map s.r) ((List.range s.n).map s.b) true),
   guarded s (lex ((List.range s.n).map s.q) ((List.range s.n).map s.a) false),
   guarded s (oneClause s)]

/-- This condition concerns only concrete getters, not any generated clause. -/
def ReadSemantics (s : Spec) (X : Nat → Nat) (M : Nat → Nat → Nat) : Prop :=
  let v := s.args.map (evalE X M)
  (∀ i < s.n, evalE X M (s.q i) = WordDivision.value s.width 0 i v) ∧
  (∀ i < s.n, evalE X M (s.r i) = WordDivision.value s.width 1 i v) ∧
  (∀ i, 1 ≤ i → i ≤ 2*s.n →
    evalE X M (s.c i) = WordDivision.value s.width 2 i v)

/-- A concrete map interpretation decodes all operands from its queried key,
not from an ambient environment.  The actual map-ID dispatch is supplied by
WordReach and the emitter; this is the generic semantic equation they need. -/
def keyValues : Nat → Nat → List Nat
  | 0, _ => []
  | 1, k => [k]
  | i+2, k => Kern.pickP 0 k :: keyValues (i+1) (Kern.pickP 1 k)

theorem keyValues_tuple (xs : List E) (X : Nat → Nat) (M : Nat → Nat → Nat)
    (h : xs ≠ []) :
    keyValues xs.length (evalE X M (tupleKey xs)) = xs.map (evalE X M) := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => simp [keyValues, tupleKey]
    | cons y ys =>
      have ht : (y :: ys) ≠ [] := by simp
      have hh := ih ht
      simp only [tupleKey, evalE, keyValues, List.length_cons, List.map_cons]
      rw [Kern.pickP, Kern.pickP]
      simp only [if_pos rfl, if_neg (by decide : (1 : Nat) ≠ 0)]
      simp only [Kern.cun_cpair]
      exact congrArg (List.cons (evalE X M x)) hh




private theorem both_sound (xs : List C) (X : Nat → Nat) (M : Nat → Nat → Nat) :
    evalC X M (both xs) = true ↔ ∀ c ∈ xs, evalC X M c = true := by
  induction xs with
  | nil => simp [both, evalC]
  | cons x xs ih =>
    cases xs with
    | nil => simp [both, evalC]
    | cons y ys =>
      cases ys with
      | nil => simp [both, evalC]
      | cons z zs =>
        simpa only [both, evalC, Bool.and_eq_true, List.mem_cons,
          forall_eq_or_imp] using
          (show (evalC X M x = true ∧ evalC X M (both (y :: z :: zs)) = true) ↔
             ∀ c ∈ x :: y :: z :: zs, evalC X M c = true from by
             simpa only [List.mem_cons, forall_eq_or_imp, ih] )

private theorem either_sound (xs : List C) (X : Nat → Nat) (M : Nat → Nat → Nat) :
    evalC X M (either xs) = true ↔ ∃ c ∈ xs, evalC X M c = true := by
  induction xs with
  | nil => simp [either, evalC]
  | cons x xs ih =>
    cases xs with
    | nil => simp [either, evalC]
    | cons y ys =>
      cases ys with
      | nil => simp [either, evalC]
      | cons z zs =>
        simp only [either, evalC, Bool.or_eq_true, List.mem_cons]
        simpa [ih, or_assoc]

/-- Guard discharge requires proof only on the bounded nonzero-divisor branch. -/
theorem guarded_sound (s : Spec) (fact : C) (X : Nat → Nat) (M : Nat → Nat → Nat)
    (h : evalC X M (domain s) = true → evalC X M fact = true) :
    evalC X M (guarded s fact) = true := by
  by_cases hd : evalC X M (domain s) = true
  · simp [guarded, either, evalC, hd, h hd]
  · have hf : evalC X M (domain s) = false := by cases hh : evalC X M (domain s) <;> simp_all
    simp [guarded, either, evalC, hf]


/-- Exactly the generated guard implies every source limb is bounded and at
least one divisor limb is positive. -/
theorem domain_sound (s : Spec) (X : Nat → Nat) (M : Nat → Nat → Nat)
    (hd : evalC X M (domain s) = true) :
    (∀ i < 2*s.n, evalE X M (s.args[i]?.getD (.const 0)) < s.base) ∧
    (∃ i, i < s.n ∧ 0 < evalE X M (s.b i)) := by
  have hall := (both_sound _ X M).mp hd
  constructor
  · intro i hi
    have hh := hall _ (List.mem_append.mpr (Or.inl
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))
    change decide (evalE X M (s.args[i]?.getD (.const 0)) < s.base) = true at hh
    exact of_decide_eq_true hh
  · have hh := hall (either ((List.range s.n).map (fun i => C.lt (.const 0) (s.b i))))
      (List.mem_append.mpr (Or.inr (by simp)))
    obtain ⟨f, hf, hv⟩ := (either_sound _ X M).mp hh
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    refine ⟨i, List.mem_range.mp hi, ?_⟩
    change decide (0 < evalE X M (s.b i)) = true at hv
    exact of_decide_eq_true hv


/-- Evaluation commutes with optional list indexing, including malformed or
out-of-range descriptors; validity later ensures the actual slots exist. -/
private theorem eval_arg (xs : List E) (X : Nat → Nat) (M : Nat → Nat → Nat)
    (i : Nat) : evalE X M (xs[i]?.getD (.const 0)) =
      (xs.map (evalE X M))[i]?.getD 0 := by
  induction xs generalizing i with
  | nil => simp [evalE]
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i

/-- The generated guard means raw operand digits equal their normalized
concrete-word digits.  No equality is assumed for unbounded operands. -/
theorem operand_digit (s : Spec) (X : Nat → Nat) (M : Nat → Nat → Nat)
    (hd : evalC X M (domain s) = true) (i : Nat) (hi : i < 2*s.n) :
    evalE X M (s.args[i]?.getD (.const 0)) =
      WordDivision.inputDigit s.width (s.args.map (evalE X M)) i := by
  have hb := (domain_sound s X M hd).1 i hi
  simp only [WordDivision.inputDigit, ← eval_arg]
  exact (Nat.mod_eq_of_lt hb).symm


private theorem sumE_eval (xs : List E) (X : Nat → Nat) (M : Nat → Nat → Nat) :
    evalE X M (sumE xs) = (xs.map (evalE X M)).sum := by
  have hf (ys : List E) (acc : E) :
      evalE X M (ys.foldl E.add acc) =
        evalE X M acc + (ys.map (evalE X M)).sum := by
    induction ys generalizing acc with
    | nil => simp
    | cons y ys ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, evalE]
      omega
  simpa [sumE, evalE] using hf xs (.const 0)

private theorem filter_sum (xs : List Nat) (p : Nat → Bool) (f : Nat → Nat) :
    ((xs.filter p).map f).sum =
      (xs.map fun j => if p j then f j else 0).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hp : p x <;> simp [hp, ih]


/-- A filtered TypeScript convolution sum is the concrete word convolution,
without specializing or enumerating expression trees. -/
private theorem products_eval (s : Spec) (X : Nat → Nat) (M : Nat → Nat → Nat)
    (hr : ReadSemantics s X M) (hd : evalC X M (domain s) = true)
    (i : Nat) :
    ((((List.range s.n).filter fun j => j ≤ i && i-j < s.n).map
      (fun j => evalE X M (.prod (s.q j) (s.b (i-j))))).sum) =
      WordDivision.convolution s.width (s.args.map (evalE X M)) i := by
  let p : Nat → Bool := fun j => j ≤ i && i-j < s.n
  let v := s.args.map (evalE X M)
  rw [filter_sum (List.range s.n) p
    (fun j => evalE X M (.prod (s.q j) (s.b (i-j))))]
  unfold WordDivision.convolution
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  have hjlt : j < s.n := List.mem_range.mp hj
  by_cases hp : j ≤ i ∧ i-j < s.n
  · have hpb : p j = true := by simp [p, hp.1, hp.2]
    simp only [hpb, ↓reduceIte, evalE]
    rw [hr.1 j hjlt, show evalE X M (s.b (i-j)) =
      WordDivision.bDigit s.width v (i-j) from by
        simpa only [Spec.b, Spec.n, WordDivision.bDigit, v] using
          operand_digit s X M hd (s.n+(i-j)) (by omega)]
    change j ≤ i ∧ i-j < WordDivision.limbs s.width at hp
    simp only [if_pos hp, WordDivision.value_q, v]
  · have hpb : p j = false := by
      simp only [p, Bool.and_eq_true, decide_eq_true_eq]
      simp at hp ⊢
      omega
    change ¬(j ≤ i ∧ i-j < WordDivision.limbs s.width) at hp
    simp [hpb, hp]

/-- Each guarded syntactic column has exactly the arithmetic shape proved by
WordColumns, for arbitrary source terms and environment. -/
theorem column_sound (s : Spec) (hv : s.Valid) (X : Nat → Nat)
    (M : Nat → Nat → Nat) (hr : ReadSemantics s X M)
    (hd : evalC X M (domain s) = true)
    (hb : WordDivision.wordB s.width (s.args.map (evalE X M)) ≠ 0)
    (i : Nat) (hi : i < 2*s.n) : evalC X M (column s i) = true := by
  let v := s.args.map (evalE X M)
  have hc (j : Nat) (hj : j ≤ 2*s.n) :
      evalE X M (s.c j) = WordDivision.carry s.width v j := by
    by_cases hz : j = 0
    · subst j
      change evalE X M (.const 0) = 0
      rfl
    · simpa only [WordDivision.value_c] using hr.2.2 j (by omega) hj
  have hq (j : Nat) (hj : j < s.n) :
      evalE X M (s.r j) = WordDivision.rDigit s.width v j := by
    simpa only [WordDivision.value_r] using hr.2.1 j hj
  have hleft : evalE X M (sumE ([s.c i] ++
      (if i < s.n then [s.r i] else []) ++
      ((List.range s.n).filter fun j => j ≤ i && i-j < s.n).map
        (fun j => E.prod (s.q j) (s.b (i-j))))) =
      WordDivision.carry s.width v i +
        (if i < s.n then WordDivision.rDigit s.width v i else 0) +
        WordDivision.convolution s.width v i := by
    rw [sumE_eval]
    simp only [List.map_append, List.sum_append]
    simp only [List.map_map, Function.comp_def]
    rw [products_eval s X M hr hd i]
    by_cases h : i < s.n
    · simp [h, hc i (by omega), hq i h, v]
    · simp [h, hc i (by omega), v]
  have hright : evalE X M (sumE
      [if i < s.n then s.a i else .const 0, .mul s.base (s.c (i+1))]) =
      (if i < s.n then WordDivision.inputDigit s.width v i else 0) +
      WordDivision.radix s.width * WordDivision.carry s.width v (i+1) := by
    rw [sumE_eval]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases h : i < s.n
    · simp only [if_pos h, evalE, Spec.base]
      rw [hc (i+1) (by omega)]
      rw [show evalE X M (s.a i) = WordDivision.inputDigit s.width v i from by
        simpa only [Spec.a, v] using operand_digit s X M hd i (by omega)]
    · simp only [if_neg h, evalE, Spec.base]
      rw [hc (i+1) (by omega)]
  change decide (_ = _) = true
  apply decide_eq_true
  rw [hleft, hright]
  exact (WordColumns.columns_and_carry s.width v hv.1
    (by simpa only [Spec.n, v, List.length_map] using hv.2.1) hb).1 i
    (by simpa only [Spec.n] using hi)


/-- A highest-differing-digit witness satisfies the exact nested AST
lexicographic disjunction; works for every digit count, not examples. -/
theorem lex_lt_sound (xs ys : List E) (X : Nat → Nat) (M : Nat → Nat → Nat)
    (h : WordLex.lt (xs.map (evalE X M)) (ys.map (evalE X M))) :
    evalC X M (lex xs ys true) = true := by
  obtain ⟨i, hi, heq, hlt⟩ := h
  simp only [List.length_map] at hi
  apply (either_sound _ X M).2
  let atom := both (((List.range (xs.length-i-1)).map fun j =>
    C.eq (xs[i+1+j]?.getD (.const 0)) (ys[i+1+j]?.getD (.const 0))) ++
    [C.lt (xs[i]?.getD (.const 0)) (ys[i]?.getD (.const 0))])
  refine ⟨atom, ?_, ?_⟩
  · simp only [lex, ↓reduceIte, List.append_nil]
    apply List.mem_map.mpr
    exact ⟨i, by simp [hi], rfl⟩
  · apply (both_sound _ X M).2
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hf
      have hjlt : i+1+j < xs.length := by
        have hh := List.mem_range.mp hj
        omega
      change decide (evalE X M (xs[i+1+j]?.getD (.const 0)) =
        evalE X M (ys[i+1+j]?.getD (.const 0))) = true
      apply decide_eq_true
      rw [eval_arg, eval_arg]
      exact heq (i+1+j) (by omega) (by simpa only [List.length_map] using hjlt)
    · have hf' : f = C.lt (xs[i]?.getD (.const 0)) (ys[i]?.getD (.const 0)) := by
        simpa using hf
      subst f
      change decide (evalE X M (xs[i]?.getD (.const 0)) <
        evalE X M (ys[i]?.getD (.const 0))) = true
      apply decide_eq_true
      rw [eval_arg, eval_arg]
      exact hlt

/-- Non-strict quotient comparison permits the equality alternative, exactly
as TS digitLex(..., false), with no finite-width case split. -/
theorem lex_le_sound (xs ys : List E) (X : Nat → Nat) (M : Nat → Nat → Nat)
    (h : WordLex.lt (xs.map (evalE X M)) (ys.map (evalE X M)) ∨
      xs.map (evalE X M) = ys.map (evalE X M)) :
    evalC X M (lex xs ys false) = true := by
  rcases h with h | h
  · obtain ⟨i, hi, heq, hlt⟩ := h
    simp only [List.length_map] at hi
    apply (either_sound _ X M).2
    let atom := both (((List.range (xs.length-i-1)).map fun j =>
      C.eq (xs[i+1+j]?.getD (.const 0)) (ys[i+1+j]?.getD (.const 0))) ++
      [C.lt (xs[i]?.getD (.const 0)) (ys[i]?.getD (.const 0))])
    refine ⟨atom, ?_, ?_⟩
    · apply List.mem_append.mpr
      exact Or.inl (List.mem_map.mpr ⟨i, by simp [hi], rfl⟩)
    · apply (both_sound _ X M).2
      intro f hf
      rcases List.mem_append.mp hf with hf | hf
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hf
        have hjlt : i+1+j < xs.length := by
          have hh := List.mem_range.mp hj
          omega
        change decide (evalE X M (xs[i+1+j]?.getD (.const 0)) =
          evalE X M (ys[i+1+j]?.getD (.const 0))) = true
        apply decide_eq_true
        rw [eval_arg, eval_arg]
        exact heq (i+1+j) (by omega) (by simpa only [List.length_map] using hjlt)
      · have hf' : f = C.lt (xs[i]?.getD (.const 0)) (ys[i]?.getD (.const 0)) := by
          simpa using hf
        subst f
        change decide (evalE X M (xs[i]?.getD (.const 0)) <
          evalE X M (ys[i]?.getD (.const 0))) = true
        apply decide_eq_true
        rw [eval_arg, eval_arg]
        exact hlt
  · apply (either_sound _ X M).2
    refine ⟨both ((List.range xs.length).map fun i =>
      C.eq (xs[i]?.getD (.const 0)) (ys[i]?.getD (.const 0))), ?_, ?_⟩
    · apply List.mem_append.mpr
      exact Or.inr (by simp)
    · apply (both_sound _ X M).2
      intro f hf
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
      change decide (evalE X M (xs[i]?.getD (.const 0)) =
        evalE X M (ys[i]?.getD (.const 0))) = true
      apply decide_eq_true
      rw [eval_arg, eval_arg, h]


/-- The TS guard's positive divisor limb witnesses the concrete nonzero word;
all operands may be arbitrary syntax and the underlying Nat inputs unbounded. -/
theorem nonzero_of_domain (s : Spec) (hv : s.Valid)
    (X : Nat → Nat) (M : Nat → Nat → Nat)
    (hd : evalC X M (domain s) = true) :
    WordDivision.wordB s.width (s.args.map (evalE X M)) ≠ 0 := by
  obtain ⟨i, hi, hp⟩ := (domain_sound s X M hd).2
  apply WordLex.wordB_nonzero s.width (s.args.map (evalE X M)) hv.1
    (by simpa only [Spec.n, List.length_map] using hv.2.1)
  refine ⟨i, by simpa only [Spec.n] using hi, ?_⟩
  have he : evalE X M (s.b i) = WordDivision.bDigit s.width
      (s.args.map (evalE X M)) i := by
    simpa only [Spec.b, Spec.n, WordDivision.bDigit] using
      operand_digit s X M hd (s.n+i) (by omega)
  rw [← he]
  exact hp

/-- Every numeric digit list in WordLex is definitionally the evaluation of
its corresponding generated q/r/a/b expression list under the guard. -/
theorem digit_lists (s : Spec) (X : Nat → Nat) (M : Nat → Nat → Nat)
    (hr : ReadSemantics s X M) (hd : evalC X M (domain s) = true) :
    (((List.range s.n).map s.q).map (evalE X M) =
      (List.range s.n).map (WordDivision.qDigit s.width (s.args.map (evalE X M)))) ∧
    (((List.range s.n).map s.r).map (evalE X M) =
      (List.range s.n).map (WordDivision.rDigit s.width (s.args.map (evalE X M)))) ∧
    (((List.range s.n).map s.a).map (evalE X M) =
      (List.range s.n).map (WordDivision.inputDigit s.width (s.args.map (evalE X M)))) ∧
    (((List.range s.n).map s.b).map (evalE X M) =
      (List.range s.n).map (WordDivision.bDigit s.width (s.args.map (evalE X M)))) := by
  have hq : ∀ i < s.n, evalE X M (s.q i) =
      WordDivision.qDigit s.width (s.args.map (evalE X M)) i := by
    intro i hi
    simpa only [WordDivision.value_q] using hr.1 i hi
  have hrem : ∀ i < s.n, evalE X M (s.r i) =
      WordDivision.rDigit s.width (s.args.map (evalE X M)) i := by
    intro i hi
    simpa only [WordDivision.value_r] using hr.2.1 i hi
  have ha : ∀ i < s.n, evalE X M (s.a i) =
      WordDivision.inputDigit s.width (s.args.map (evalE X M)) i := by
    intro i hi
    simpa only [Spec.a] using operand_digit s X M hd i (by omega)
  have hb : ∀ i < s.n, evalE X M (s.b i) =
      WordDivision.bDigit s.width (s.args.map (evalE X M)) i := by
    intro i hi
    simpa only [Spec.b, Spec.n, WordDivision.bDigit] using
      operand_digit s X M hd (s.n+i) (by omega)
  repeat' constructor
  all_goals
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro i hi
    first
    | exact hq i (List.mem_range.mp hi)
    | exact hrem i (List.mem_range.mp hi)
    | exact ha i (List.mem_range.mp hi)
    | exact hb i (List.mem_range.mp hi)


/-- The guarded carry at the word boundary is zero for all supported widths. -/
theorem carry_zero_sound (s : Spec) (hv : s.Valid)
    (X : Nat → Nat) (M : Nat → Nat → Nat)
    (hr : ReadSemantics s X M) (hd : evalC X M (domain s) = true) :
    evalC X M (.eq (s.c s.n) (.const 0)) = true := by
  have hn : 0 < s.n := by
    have hw : s.width = 8 ∨ s.width = 16 ∨ s.width = 32 ∨ s.width = 64 := by
      simpa using hv.1
    rcases hw with h | h | h | h <;> simp [h, Spec.n, WordDivision.limbs]
  have hc := hr.2.2 s.n (by omega) (by omega)
  have hb := nonzero_of_domain s hv X M hd
  have hz := (WordColumns.columns_and_carry s.width
    (s.args.map (evalE X M)) hv.1
    (by simpa only [Spec.n, List.length_map] using hv.2.1) hb).2
  change decide (evalE X M (s.c s.n) = 0) = true
  apply decide_eq_true
  rw [hc, WordDivision.value_c]
  simpa only [Spec.n] using hz

/-- The full strict/non-strict lex clauses are not merely arithmetic claims:
these are their evaluated generated disjunctions for arbitrary AST operands. -/
theorem lex_facts_sound (s : Spec) (hv : s.Valid)
    (X : Nat → Nat) (M : Nat → Nat → Nat)
    (hr : ReadSemantics s X M) (hd : evalC X M (domain s) = true) :
    evalC X M (lex ((List.range s.n).map s.r)
      ((List.range s.n).map s.b) true) = true ∧
    evalC X M (lex ((List.range s.n).map s.q)
      ((List.range s.n).map s.a) false) = true := by
  have hn := WordLex.word_lex s.width (s.args.map (evalE X M)) hv.1
    (by simpa only [Spec.n, List.length_map] using hv.2.1)
    (nonzero_of_domain s hv X M hd)
  obtain ⟨hq, hr', ha, hb⟩ := digit_lists s X M hr hd
  constructor
  · apply lex_lt_sound
    rw [hr', hb]
    exact hn.1
  · apply lex_le_sound
    rw [hq, ha]
    exact hn.2


/-- Divisor-one shape of the generated b digit terms entails every generated
q=a and r=0 equality; no generic fact is taken as a premise. -/
theorem one_result_sound (s : Spec) (hv : s.Valid)
    (X : Nat → Nat) (M : Nat → Nat → Nat)
    (hr : ReadSemantics s X M) (hd : evalC X M (domain s) = true)
    (hon : evalC X M (bOne s) = true) :
    evalC X M (oneResult s) = true := by
  let v := s.args.map (evalE X M)
  have hall := (both_sound _ X M).mp hon
  have he0 : evalE X M (s.b 0) = 1 := by
    have he := hall (C.eq (s.b 0) (.const 1))
      (List.mem_append.mpr (Or.inl (by simp)))
    change decide (evalE X M (s.b 0) = 1) = true at he
    exact of_decide_eq_true he
  have heRest : ∀ i, 1 ≤ i → i < s.n → evalE X M (s.b i) = 0 := by
    intro i hlo hhi
    have hj : i-1 < s.n-1 := by omega
    have heq : i-1+1=i := by omega
    have hm : C.eq (s.b i) (.const 0) ∈
        ((List.range (s.n-1)).map fun j => C.eq (s.b (j+1)) (.const 0)) := by
      apply List.mem_map.mpr
      exact ⟨i-1, List.mem_range.mpr hj, by rw [heq]⟩
    have he := hall (C.eq (s.b i) (.const 0))
      (List.mem_append.mpr (Or.inr hm))
    change decide (evalE X M (s.b i) = 0) = true at he
    exact of_decide_eq_true he
  have hb : WordDivision.wordB s.width v = 1 := by
    apply WordOne.b_digits_one s.width v hv.1
      (by simpa only [Spec.n, v, List.length_map] using hv.2.1)
    · have he : evalE X M (s.b 0) = WordDivision.bDigit s.width v 0 := by
        simpa only [Spec.b, Spec.n, WordDivision.bDigit, v] using
          operand_digit s X M hd (s.n+0) (by
            have hn : 0 < s.n := by
              have hw : s.width=8 ∨ s.width=16 ∨ s.width=32 ∨ s.width=64 := by
                simpa using hv.1
              rcases hw with h | h | h | h <;> simp [h, Spec.n, WordDivision.limbs]
            omega)
      rw [← he]
      exact he0
    · intro i hlo hhi
      have hidx : i < s.n := by simpa only [Spec.n] using hhi
      have he : evalE X M (s.b i) = WordDivision.bDigit s.width v i := by
        simpa only [Spec.b, Spec.n, WordDivision.bDigit, v] using
          operand_digit s X M hd (s.n+i) (by omega)
      rw [← he]
      exact heRest i hlo (by simpa only [Spec.n] using hhi)
  have hdigits := WordOne.divisor_one_digits s.width v hv.1
    (by simpa only [Spec.n, v, List.length_map] using hv.2.1) hb
  apply (both_sound _ X M).2
  intro f hf
  simp only [oneResult, List.mem_append] at hf
  rcases hf with hf | hf
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    have hidx : i < s.n := List.mem_range.mp hi
    change decide (evalE X M (s.q i) = evalE X M (s.a i)) = true
    apply decide_eq_true
    rw [hr.1 i hidx, WordDivision.value_q]
    rw [show evalE X M (s.a i) = WordDivision.inputDigit s.width v i from by
      simpa only [Spec.a, v] using operand_digit s X M hd i (by omega)]
    exact (hdigits i (by simpa only [Spec.n] using hidx)).1
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    have hidx : i < s.n := List.mem_range.mp hi
    change decide (evalE X M (s.r i) = 0) = true
    apply decide_eq_true
    rw [hr.2.1 i hidx, WordDivision.value_r]
    exact (hdigits i (by simpa only [Spec.n] using hidx)).2

/-- The generated b=1 implication has its own syntactic disjunction, whose
antecedent is discharged by the previous theorem under the domain guard. -/
theorem one_clause_sound (s : Spec) (hv : s.Valid)
    (X : Nat → Nat) (M : Nat → Nat → Nat)
    (hr : ReadSemantics s X M) (hd : evalC X M (domain s) = true) :
    evalC X M (oneClause s) = true := by
  by_cases h : evalC X M (bOne s) = true
  · simp [oneClause, either, evalC, h, one_result_sound s hv X M hr hd h]
  · have hf : evalC X M (bOne s) = false := by
      cases hh : evalC X M (bOne s) <;> simp_all
    simp [oneClause, either, evalC, hf]

/-- All unconditional q/r/c inequalities are valid for arbitrary input terms
and all four widths, without a nonzero-divisor hypothesis. -/
theorem rangeFacts_sound (s : Spec) (X : Nat → Nat) (M : Nat → Nat → Nat)
    (hr : ReadSemantics s X M) :
    ∀ f ∈ rangeFacts s, evalC X M f = true := by
  intro f hf
  simp only [rangeFacts, List.mem_append] at hf
  rcases hf with (hf | hf) | hf
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    have hidx : i < s.n := List.mem_range.mp hi
    simp only [evalC, evalE, Spec.base, hr.1 i hidx]
    exact decide_eq_true (WordDivision.value_q_lt s.width i (s.args.map (evalE X M)))
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    have hidx : i < s.n := List.mem_range.mp hi
    simp only [evalC, evalE, Spec.base, hr.2.1 i hidx]
    exact decide_eq_true (WordDivision.value_r_lt s.width i (s.args.map (evalE X M)))
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hf
    have hidx : j + 1 ≤ 2*s.n := by
      have hh := List.mem_range.mp hj
      omega
    simp only [evalC, evalE, Spec.base, Spec.n,
      hr.2.2 (j+1) (by omega) hidx, WordDivision.value_c]
    exact decide_eq_true (WordDivision.carry_bound s.width (s.args.map (evalE X M)) (j+1))

def Spec.reserved (s : Spec) : List Nat := s.qMaps ++ s.rMaps ++ s.cMaps

private theorem getD_mem (xs : List Nat) (i : Nat) (h : i < xs.length) :
    xs[i]?.getD 0 ∈ xs := by
  induction xs generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.length_cons] at h
      simp only [List.getElem?_cons_succ, List.mem_cons]
      exact Or.inr (ih i (by omega))

/-- A concrete, environment-independent value function can be supplied by the
emitter (a finite dispatch on the native map indices and decoded key).  Its
association with this descriptor is checked pointwise, never postulated as a
fact's truth. -/
def ValueMatches (s : Spec) (value : Nat → Nat → Nat) : Prop :=
  (∀ i < s.n, ∀ k, value (s.qMaps[i]?.getD 0) k =
    WordDivision.value s.width 0 i (keyValues (2*s.n) k)) ∧
  (∀ i < s.n, ∀ k, value (s.rMaps[i]?.getD 0) k =
    WordDivision.value s.width 1 i (keyValues (2*s.n) k)) ∧
  (∀ i, 1 ≤ i → i ≤ 2*s.n → ∀ k,
    value (s.cMaps[i-1]?.getD 0) k =
      WordDivision.value s.width 2 i (keyValues (2*s.n) k))

/-- The only bridge from a reserved-map world to the getter premise.  It uses
right-associated tuple decoding and never assumes any generated clause. -/
theorem interpret_sound (s : Spec) (hv : s.Valid)
    (value M : Nat → Nat → Nat) (X : Nat → Nat)
    (hvalue : ValueMatches s value)
    (hi : ∀ mp ∈ s.reserved, ∀ k, M mp k = value mp k) :
    ReadSemantics s X M := by
  have hk : keyValues (2*s.n) (evalE X M s.key) = s.args.map (evalE X M) := by
    rw [← hv.2.1]
    exact keyValues_tuple s.args X M (by
      intro hz
      have hlen : s.args.length = 0 := by simp [hz]
      have hn : 0 < s.n := by
        have hw : s.width = 8 ∨ s.width = 16 ∨ s.width = 32 ∨ s.width = 64 := by
          simpa using hv.1
        rcases hw with h | h | h | h <;> simp [h, Spec.n, WordDivision.limbs]
      have hlength := hv.2.1
      omega)
  constructor
  · intro i h
    have hqLen := hv.2.2.1
    change M (s.qMaps[i]?.getD 0) (evalE X M s.key) = _
    rw [hi _ (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inl (getD_mem s.qMaps i (by omega)))))) _]
    rw [(hvalue.1 i h) _, hk]
  constructor
  · intro i h
    have hrLen := hv.2.2.2.1
    change M (s.rMaps[i]?.getD 0) (evalE X M s.key) = _
    rw [hi _ (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inr (getD_mem s.rMaps i (by omega)))))) _]
    rw [(hvalue.2.1 i h) _, hk]
  · intro i hlo hhi
    have hcLen := hv.2.2.2.2
    have hpos : i ≠ 0 := by omega
    simp only [Spec.c, if_neg hpos, evalE]
    rw [hi _ (List.mem_append.mpr (Or.inr
      (getD_mem s.cMaps (i-1) (by omega)))) _]
    rw [(hvalue.2.2 i hlo hhi) _, hk]


/-- Every clause of the exact TypeScript wordDivisionFacts schema evaluates to
true at every environment under concrete word getter semantics. The only
premise about maps is equality of getter reads with WordDivision.value; there
are no assumptions about any generated clauses, source law, or examples. -/
theorem facts_sound (s : Spec) (hv : s.Valid)
    (X : Nat → Nat) (M : Nat → Nat → Nat)
    (hr : ReadSemantics s X M) (f : C) (hf : f ∈ facts s) :
    evalC X M f = true := by
  simp only [facts] at hf
  rcases List.mem_append.mp hf with hPrefix | hTail
  rcases List.mem_append.mp hPrefix with hRange | hColumn
  · exact rangeFacts_sound s X M hr f hRange
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hColumn
    apply guarded_sound
    intro hd
    exact column_sound s hv X M hr hd
      (nonzero_of_domain s hv X M hd) i (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hTail
  rcases hTail with rfl | rfl | rfl | rfl
  · apply guarded_sound
    intro hd
    exact carry_zero_sound s hv X M hr hd
  · apply guarded_sound
    intro hd
    exact (lex_facts_sound s hv X M hr hd).1
  · apply guarded_sound
    intro hd
    exact (lex_facts_sound s hv X M hr hd).2
  · apply guarded_sound
    intro hd
    exact one_clause_sound s hv X M hr hd

#print axioms WordFacts.facts_sound

end WordFacts

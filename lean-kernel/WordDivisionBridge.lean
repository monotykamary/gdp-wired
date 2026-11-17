import Kernel
import WordDivision

/-! Sound checker extension for *proved* facts about one fixed concrete map interpretation.
The ordinary Kern.checkMachine is unchanged. Extra premises are checked as proof
hypotheses, and are discharged separately for every environment; no declaration
of a reserved map may substitute for the semantic proof. -/
namespace WordDivisionBridge
open Kern

abbrev FactProof := List (C × (List VDef × Tree) × (List VDef × Tree))

def startGoal (m : Machine) (law : C) (extra : List C) : List C :=
  Kern.startGoal m law ++ extra

def stepGoal (m : Machine) (ps : FactProof) (law : C) (extra : List C) : List C :=
  Kern.stepGoal m (ps.map (·.1)) law ++ extra

def checkWithFacts (m : Machine) (ps : FactProof) (extra : List C) : Bool :=
  preOk m && ps.all fun p => avoids m.inputs p.1
    && checkGoal ⟨p.2.1.1, startGoal m p.1 extra⟩ p.2.1.2
    && checkGoal ⟨p.2.2.1, stepGoal m ps p.1 extra⟩ p.2.2.2

/-- Every accepted tree yields an actual invariant when its additional facts
are *proved for the concrete interpretation at every environment*. -/
theorem checkWithFacts_sound (m : Machine) (ps : FactProof) (extra : List C)
    (h : checkWithFacts m ps extra = true) (maps : Nat → Nat → Nat)
    (facts : ∀ env, ∀ c ∈ extra, evalC env maps c = true) :
    ∀ ρ, Reach m maps ρ → ∀ l ∈ ps.map (·.1), evalC ρ maps l = true := by
  simp only [checkWithFacts, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨hpre, h⟩ := h
  intro ρ hr
  induction hr with
  | start ρ h0 =>
    intro l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    have hs := Kern.sound _ _ (h p hp).1.2 ρ maps
    apply Decidable.byContradiction
    intro hf
    apply hs
    intro c hc
    simp only [startGoal] at hc
    rcases List.mem_append.mp hc with hc | hc
    · simp only [Kern.startGoal, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact h0
      · simp only [evalC, subst_evalC]; simpa using hf
    · exact facts ρ c hc
  | step ρ ι hr ha ih =>
    intro l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    have hs := Kern.sound _ _ (h p hp).2 (withInputs m.inputs ρ ι) maps
    apply Decidable.byContradiction
    intro hf
    apply hs
    intro c hc
    simp only [stepGoal] at hc
    rcases List.mem_append.mp hc with hc | hc
    · simp only [Kern.stepGoal, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with ((rfl | rfl) | hc) | rfl
      · rw [evalC_avoids hpre maps (ρ' := ρ) (fun i hi => withInputs_other (fun h => hi (by simp [h])) ρ ι)]
        exact pre_reach hpre hr
      · exact ha
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
        rw [evalC_avoids (h q hq).1.1 maps (ρ' := ρ) (fun i hi => withInputs_other hi ρ ι)]
        exact ih q.1 (List.mem_map.mpr ⟨q, hq, rfl⟩)
      · simp only [evalC, subst_evalC]; simpa using hf
    · exact facts (withInputs m.inputs ρ ι) c hc

/-! Per-obligation facts match the original generated certificate's order: they
are inserted immediately before the negated conclusion, not appended after it.
This is the shape required by leaf row indices in real proof trees. -/
structure Entry where
  law : C
  startFacts : List C
  stepFacts : List C
  start : List VDef × Tree
  step : List VDef × Tree

def startGoalAt (m : Machine) (p : Entry) : List C :=
  [m.pre] ++ p.startFacts ++ [.not (substC m.init p.law)]

def stepGoalAt (m : Machine) (ps : List Entry) (p : Entry) : List C :=
  [m.pre, m.assume] ++ ps.map (·.law) ++ p.stepFacts ++ [.not (substC m.step p.law)]

def checkEntries (m : Machine) (ps : List Entry) : Bool :=
  preOk m && ps.all fun p => avoids m.inputs p.law
    && checkGoal ⟨p.start.1, startGoalAt m p⟩ p.start.2
    && checkGoal ⟨p.step.1, stepGoalAt m ps p⟩ p.step.2

/-- The exact generated-facts checker shape: each obligation may use only its
own facts, and every such fact is proved for every environment under the fixed
concrete map interpretation. -/
theorem checkEntries_sound (m : Machine) (ps : List Entry)
    (h : checkEntries m ps = true) (maps : Nat → Nat → Nat)
    (facts : ∀ env p, p ∈ ps →
      (∀ c ∈ p.startFacts, evalC env maps c = true) ∧
      (∀ c ∈ p.stepFacts, evalC env maps c = true)) :
    ∀ ρ, Reach m maps ρ → ∀ l ∈ ps.map (·.law), evalC ρ maps l = true := by
  simp only [checkEntries, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨hpre, h⟩ := h
  intro ρ hr
  induction hr with
  | start ρ h0 =>
    intro l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    have hs := Kern.sound _ _ (h p hp).1.2 ρ maps
    apply Decidable.byContradiction
    intro hf
    apply hs
    intro c hc
    simp only [startGoalAt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | hc) | rfl
    · exact h0
    · exact (facts ρ p hp).1 c hc
    · simp only [evalC, subst_evalC]; simpa using hf
  | step ρ ι hr ha ih =>
    intro l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    have hs := Kern.sound _ _ (h p hp).2 (withInputs m.inputs ρ ι) maps
    apply Decidable.byContradiction
    intro hf
    apply hs
    intro c hc
    simp only [stepGoalAt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (((rfl | rfl) | hc) | hc) | rfl
    · rw [evalC_avoids hpre maps (ρ' := ρ) (fun i hi => withInputs_other (fun h => hi (by simp [h])) ρ ι)]
      exact pre_reach hpre hr
    · exact ha
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
      rw [evalC_avoids (h q hq).1.1 maps (ρ' := ρ) (fun i hi => withInputs_other hi ρ ι)]
      exact ih q.law (List.mem_map.mpr ⟨q, hq, rfl⟩)
    · exact (facts (withInputs m.inputs ρ ι) p hp).2 c hc
    · simp only [evalC, subst_evalC]; simpa using hf

#print axioms WordDivisionBridge.checkEntries_sound

/-- The unconditional quotient-digit bound is universal in the machine inputs,
not merely a closed test vector. -/
theorem q8_bound (a b : Nat) : WordDivision.value 8 0 0 [a,b] < 256 := by
  simpa [WordDivision.radix] using WordDivision.value_q_lt 8 0 [a,b]

/-- Concrete map semantics for a one-limb quotient. The right tuple key is
unpaired by the same Kern.pickP operations as the exporter. -/
def map8q (base : Nat → Nat → Nat) (mp key : Nat) : Nat :=
  if mp = 0 then WordDivision.value 8 0 0 [Kern.pickP 0 key, Kern.pickP 1 key]
  else base mp key

theorem map8q_range (base : Nat → Nat → Nat) (env : Nat → Nat) (key : E) :
    evalC env (map8q base) (.lt (.get 0 key) (.const 256)) = true := by
  have h := WordDivision.value_q_lt 8 0
    [Kern.pickP 0 (evalE env (map8q base) key),
     Kern.pickP 1 (evalE env (map8q base) key)]
  simpa [evalC, evalE, map8q, WordDivision.radix] using h

#print axioms WordDivisionBridge.map8q_range

/-- All digit and carry range facts emitted by the TypeScript generator have
semantic proofs for arbitrary input limbs, including unbounded operands. -/
theorem quotient_digit_bound (w i : Nat) (v : List Nat) :
    WordDivision.value w 0 i v < WordDivision.radix w :=
  WordDivision.value_q_lt w i v

theorem remainder_digit_bound (w i : Nat) (v : List Nat) :
    WordDivision.value w 1 i v < WordDivision.radix w :=
  WordDivision.value_r_lt w i v

theorem carry_digit_bound (w i : Nat) (v : List Nat) :
    WordDivision.value w 2 i v ≤ WordDivision.limbs w * WordDivision.radix w := by
  rw [WordDivision.value_c]
  exact WordDivision.carry_bound w v i

theorem single_limb_remainder_lex (w a b : Nat) (hn : WordDivision.limbs w = 1)
    (hb : WordDivision.wordB w [a,b] ≠ 0) :
    WordDivision.rDigit w [a,b] 0 < b % WordDivision.radix w := by
  have hr := WordDivision.remainder_lt w [a,b] hb
  have hbe : WordDivision.wordB w [a,b] = b % WordDivision.radix w := by
    simp [WordDivision.wordB, WordDivision.normalize, WordDivision.assemble, hn]
  have hlt : WordDivision.remainder w [a,b] < WordDivision.radix w := by
    rw [hbe] at hr
    exact Nat.lt_trans hr (Nat.mod_lt b (WordDivision.radix_pos w))
  have hd : WordDivision.rDigit w [a,b] 0 = WordDivision.remainder w [a,b] := by
    simp [WordDivision.rDigit, WordDivision.digit, Nat.mod_eq_of_lt hlt]
  simpa [hbe, hd] using hr

theorem single_limb_quotient_lex (w a b : Nat) (hn : WordDivision.limbs w = 1)
    (hb : WordDivision.wordB w [a,b] ≠ 0) :
    WordDivision.qDigit w [a,b] 0 ≤ a % WordDivision.radix w := by
  have hq := WordDivision.quotient_le w [a,b] hb
  have hae : WordDivision.wordA w [a,b] = a % WordDivision.radix w := by
    simp [WordDivision.wordA, WordDivision.normalize, WordDivision.assemble, hn]
  have hlt : WordDivision.quotient w [a,b] < WordDivision.radix w := by
    rw [hae] at hq
    exact Nat.lt_of_le_of_lt hq (Nat.mod_lt a (WordDivision.radix_pos w))
  have hd : WordDivision.qDigit w [a,b] 0 = WordDivision.quotient w [a,b] := by
    simp [WordDivision.qDigit, WordDivision.digit, Nat.mod_eq_of_lt hlt]
  simpa [hae, hd] using hq

#print axioms WordDivisionBridge.single_limb_remainder_lex
#print axioms WordDivisionBridge.single_limb_quotient_lex

/-- Two-limb radix comparison; for 32-bit normalized word arrays. -/
theorem two_digit_lt_lex (a₀ a₁ b₀ b₁ : Nat)
    (ha₀ : a₀ < 65536) (hb₀ : b₀ < 65536)
    (h : WordDivision.assemble 65536 [a₀,a₁] <
      WordDivision.assemble 65536 [b₀,b₁]) :
    a₁ < b₁ ∨ (a₁ = b₁ ∧ a₀ < b₀) := by
  simp only [WordDivision.assemble, Nat.mul_zero, Nat.add_zero] at h
  omega

theorem two_digit_le_lex (a₀ a₁ b₀ b₁ : Nat)
    (ha₀ : a₀ < 65536) (hb₀ : b₀ < 65536)
    (h : WordDivision.assemble 65536 [a₀,a₁] ≤
      WordDivision.assemble 65536 [b₀,b₁]) :
    a₁ < b₁ ∨ (a₁ = b₁ ∧ a₀ < b₀) ∨ (a₁ = b₁ ∧ a₀ = b₀) := by
  simp only [WordDivision.assemble, Nat.mul_zero, Nat.add_zero] at h
  omega

theorem remainder32_digit_lex (a₀ a₁ b₀ b₁ : Nat)
    (hb : WordDivision.wordB 32 [a₀,a₁,b₀,b₁] ≠ 0) :
    let v := [a₀,a₁,b₀,b₁]
    WordDivision.rDigit 32 v 1 < b₁ % 65536 ∨
      (WordDivision.rDigit 32 v 1 = b₁ % 65536 ∧
       WordDivision.rDigit 32 v 0 < b₀ % 65536) := by
  dsimp only
  let v := [a₀,a₁,b₀,b₁]
  have hr := WordDivision.remainder_lt 32 v hb
  have hbound : WordDivision.wordB 32 v < 65536 ^ 2 := by
    simpa [v, WordDivision.radix, WordDivision.limbs] using WordDivision.wordB_bound 32 v
  have he := WordDivision.two_digit_expand 65536 (WordDivision.remainder 32 v) (Nat.lt_trans hr hbound)
  have hre : WordDivision.assemble 65536
      [WordDivision.rDigit 32 v 0, WordDivision.rDigit 32 v 1] =
      WordDivision.remainder 32 v := by
    simpa [WordDivision.rDigit, WordDivision.digit, WordDivision.radix,
      WordDivision.assemble] using he.symm
  have hbe : WordDivision.wordB 32 v = WordDivision.assemble 65536
      [b₀ % 65536, b₁ % 65536] := by
    simp [v, WordDivision.wordB, WordDivision.normalize, WordDivision.radix,
      WordDivision.limbs]
  rw [← hre, hbe] at hr
  exact two_digit_lt_lex _ _ _ _
    (by simpa [WordDivision.radix] using WordDivision.rDigit_lt 32 v 0)
    (Nat.mod_lt _ (by decide)) hr

theorem quotient32_digit_lex (a₀ a₁ b₀ b₁ : Nat)
    (hb : WordDivision.wordB 32 [a₀,a₁,b₀,b₁] ≠ 0) :
    let v := [a₀,a₁,b₀,b₁]
    WordDivision.qDigit 32 v 1 < a₁ % 65536 ∨
      (WordDivision.qDigit 32 v 1 = a₁ % 65536 ∧
       WordDivision.qDigit 32 v 0 < a₀ % 65536) ∨
      (WordDivision.qDigit 32 v 1 = a₁ % 65536 ∧
       WordDivision.qDigit 32 v 0 = a₀ % 65536) := by
  dsimp only
  let v := [a₀,a₁,b₀,b₁]
  have hq := WordDivision.quotient_le 32 v hb
  have hbound : WordDivision.wordA 32 v < 65536 ^ 2 := by
    simpa [v, WordDivision.radix, WordDivision.limbs] using WordDivision.wordA_bound 32 v
  have he := WordDivision.two_digit_expand 65536 (WordDivision.quotient 32 v) (Nat.lt_of_le_of_lt hq hbound)
  have hqe : WordDivision.assemble 65536
      [WordDivision.qDigit 32 v 0, WordDivision.qDigit 32 v 1] =
      WordDivision.quotient 32 v := by
    simpa [WordDivision.qDigit, WordDivision.digit, WordDivision.radix,
      WordDivision.assemble] using he.symm
  have hae : WordDivision.wordA 32 v = WordDivision.assemble 65536
      [a₀ % 65536, a₁ % 65536] := by
    simp [v, WordDivision.wordA, WordDivision.normalize, WordDivision.radix,
      WordDivision.limbs]
  rw [← hqe, hae] at hq
  exact two_digit_le_lex _ _ _ _
    (by simpa [WordDivision.radix] using WordDivision.qDigit_lt 32 v 0)
    (Nat.mod_lt _ (by decide)) hq

#print axioms WordDivisionBridge.remainder32_digit_lex
#print axioms WordDivisionBridge.quotient32_digit_lex
#print axioms WordDivisionBridge.two_digit_lt_lex
#print axioms WordDivisionBridge.two_digit_le_lex

/-- Arithmetic comparison of four bounded radix-65536 digit arrays. The input
and output use the same most-significant-first alternatives as digitLex in the
TypeScript intrinsic fact generator. -/
theorem four_digit_lt_lex (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat)
    (ha₀ : a₀ < 65536) (ha₁ : a₁ < 65536) (ha₂ : a₂ < 65536)
    (hb₀ : b₀ < 65536) (hb₁ : b₁ < 65536) (hb₂ : b₂ < 65536)
    (h : WordDivision.assemble 65536 [a₀,a₁,a₂,a₃] <
      WordDivision.assemble 65536 [b₀,b₁,b₂,b₃]) :
    a₃ < b₃ ∨ (a₃ = b₃ ∧ a₂ < b₂) ∨
      (a₃ = b₃ ∧ a₂ = b₂ ∧ a₁ < b₁) ∨
      (a₃ = b₃ ∧ a₂ = b₂ ∧ a₁ = b₁ ∧ a₀ < b₀) := by
  simp only [WordDivision.assemble, Nat.mul_zero, Nat.add_zero] at h
  omega

theorem four_digit_le_lex (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat)
    (ha₀ : a₀ < 65536) (ha₁ : a₁ < 65536) (ha₂ : a₂ < 65536)
    (hb₀ : b₀ < 65536) (hb₁ : b₁ < 65536) (hb₂ : b₂ < 65536)
    (h : WordDivision.assemble 65536 [a₀,a₁,a₂,a₃] ≤
      WordDivision.assemble 65536 [b₀,b₁,b₂,b₃]) :
    a₃ < b₃ ∨ (a₃ = b₃ ∧ a₂ < b₂) ∨
      (a₃ = b₃ ∧ a₂ = b₂ ∧ a₁ < b₁) ∨
      (a₃ = b₃ ∧ a₂ = b₂ ∧ a₁ = b₁ ∧ a₀ < b₀) ∨
      (a₃ = b₃ ∧ a₂ = b₂ ∧ a₁ = b₁ ∧ a₀ = b₀) := by
  simp only [WordDivision.assemble, Nat.mul_zero, Nat.add_zero] at h
  omega

theorem remainder64_digit_lex (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat)
    (hb : WordDivision.wordB 64 [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃] ≠ 0) :
    let v := [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃]
    WordDivision.rDigit 64 v 3 < b₃ % 65536 ∨
      (WordDivision.rDigit 64 v 3 = b₃ % 65536 ∧ WordDivision.rDigit 64 v 2 < b₂ % 65536) ∨
      (WordDivision.rDigit 64 v 3 = b₃ % 65536 ∧ WordDivision.rDigit 64 v 2 = b₂ % 65536 ∧ WordDivision.rDigit 64 v 1 < b₁ % 65536) ∨
      (WordDivision.rDigit 64 v 3 = b₃ % 65536 ∧ WordDivision.rDigit 64 v 2 = b₂ % 65536 ∧ WordDivision.rDigit 64 v 1 = b₁ % 65536 ∧ WordDivision.rDigit 64 v 0 < b₀ % 65536) := by
  dsimp only
  let v := [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃]
  have hr := WordDivision.remainder_lt 64 v hb
  have hbound : WordDivision.wordB 64 v < 65536 ^ 4 := by
    simpa [v, WordDivision.radix, WordDivision.limbs] using WordDivision.wordB_bound 64 v
  have he := WordDivision.four_digit_expand 65536 (WordDivision.remainder 64 v) (Nat.lt_trans hr hbound)
  have hre : WordDivision.assemble 65536
      [WordDivision.rDigit 64 v 0, WordDivision.rDigit 64 v 1,
       WordDivision.rDigit 64 v 2, WordDivision.rDigit 64 v 3] =
      WordDivision.remainder 64 v := by
    simpa [WordDivision.rDigit, WordDivision.radix] using he.symm
  have hbe : WordDivision.wordB 64 v = WordDivision.assemble 65536
      [b₀ % 65536, b₁ % 65536, b₂ % 65536, b₃ % 65536] := by
    simp [v, WordDivision.wordB, WordDivision.normalize, WordDivision.radix,
      WordDivision.limbs]
  rw [← hre, hbe] at hr
  exact four_digit_lt_lex _ _ _ _ _ _ _ _
    (by simpa [WordDivision.radix] using WordDivision.rDigit_lt 64 v 0)
    (by simpa [WordDivision.radix] using WordDivision.rDigit_lt 64 v 1)
    (by simpa [WordDivision.radix] using WordDivision.rDigit_lt 64 v 2)
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) hr

theorem quotient64_digit_lex (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat)
    (hb : WordDivision.wordB 64 [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃] ≠ 0) :
    let v := [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃]
    WordDivision.qDigit 64 v 3 < a₃ % 65536 ∨
      (WordDivision.qDigit 64 v 3 = a₃ % 65536 ∧ WordDivision.qDigit 64 v 2 < a₂ % 65536) ∨
      (WordDivision.qDigit 64 v 3 = a₃ % 65536 ∧ WordDivision.qDigit 64 v 2 = a₂ % 65536 ∧ WordDivision.qDigit 64 v 1 < a₁ % 65536) ∨
      (WordDivision.qDigit 64 v 3 = a₃ % 65536 ∧ WordDivision.qDigit 64 v 2 = a₂ % 65536 ∧ WordDivision.qDigit 64 v 1 = a₁ % 65536 ∧ WordDivision.qDigit 64 v 0 < a₀ % 65536) ∨
      (WordDivision.qDigit 64 v 3 = a₃ % 65536 ∧ WordDivision.qDigit 64 v 2 = a₂ % 65536 ∧ WordDivision.qDigit 64 v 1 = a₁ % 65536 ∧ WordDivision.qDigit 64 v 0 = a₀ % 65536) := by
  dsimp only
  let v := [a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃]
  have hq := WordDivision.quotient_le 64 v hb
  have hbound : WordDivision.wordA 64 v < 65536 ^ 4 := by
    simpa [v, WordDivision.radix, WordDivision.limbs] using WordDivision.wordA_bound 64 v
  have he := WordDivision.four_digit_expand 65536 (WordDivision.quotient 64 v) (Nat.lt_of_le_of_lt hq hbound)
  have hqe : WordDivision.assemble 65536
      [WordDivision.qDigit 64 v 0, WordDivision.qDigit 64 v 1,
       WordDivision.qDigit 64 v 2, WordDivision.qDigit 64 v 3] =
      WordDivision.quotient 64 v := by
    simpa [WordDivision.qDigit, WordDivision.radix] using he.symm
  have hae : WordDivision.wordA 64 v = WordDivision.assemble 65536
      [a₀ % 65536, a₁ % 65536, a₂ % 65536, a₃ % 65536] := by
    simp [v, WordDivision.wordA, WordDivision.normalize, WordDivision.radix,
      WordDivision.limbs]
  rw [← hqe, hae] at hq
  exact four_digit_le_lex _ _ _ _ _ _ _ _
    (by simpa [WordDivision.radix] using WordDivision.qDigit_lt 64 v 0)
    (by simpa [WordDivision.radix] using WordDivision.qDigit_lt 64 v 1)
    (by simpa [WordDivision.radix] using WordDivision.qDigit_lt 64 v 2)
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) hq

#print axioms WordDivisionBridge.remainder64_digit_lex
#print axioms WordDivisionBridge.quotient64_digit_lex
#print axioms WordDivisionBridge.four_digit_lt_lex
#print axioms WordDivisionBridge.four_digit_le_lex
#print axioms WordDivisionBridge.checkWithFacts_sound
#print axioms WordDivisionBridge.quotient_digit_bound
#print axioms WordDivisionBridge.remainder_digit_bound
#print axioms WordDivisionBridge.carry_digit_bound
end WordDivisionBridge

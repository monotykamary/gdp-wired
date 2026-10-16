/-
Cert: the trusted core of gdp-wired, with its proofs. Lean 4.34.0, core only.

A row `Σ cᵢ·xᵢ + c ≤ 0` over the integers. A certificate is a list of steps that replays into rows: an input row, a
positive combination of two earlier rows, or a cut (an earlier row whose coefficients are all g times q, replaced by q
with a constant c such that g·c ≤ constant + g − 1). `check` accepts when the last row has only zero coefficients and a
positive constant. `sound`: if `check` accepts, no integer point satisfies every input row.

`run_preserves` is the induction rule a step machine's laws rest on: a property true at the start and preserved by
every step holds after every sequence of steps.
-/

namespace Cert

structure Row where
  coefs : List Int
  const : Int
deriving Repr

def dot : List Int → List Int → Int
  | c :: cs, y :: ys => c * y + dot cs ys
  | _, _ => 0

def eval (r : Row) (x : List Int) : Int := dot r.coefs x + r.const

def addL : List Int → List Int → List Int
  | a :: as, b :: bs => (a + b) :: addL as bs
  | [], bs => bs
  | as, [] => as

def scaleL (m : Int) : List Int → List Int
  | [] => []
  | a :: as => (m * a) :: scaleL m as

theorem dot_nil_right : ∀ (a : List Int), dot a [] = 0
  | [] => rfl
  | _ :: _ => rfl

theorem dot_addL : ∀ (a b x : List Int), dot (addL a b) x = dot a x + dot b x
  | [], b, x => by simp [addL, dot]
  | _ :: _, [], x => by simp [addL, dot]
  | a :: as, b :: bs, [] => by simp [addL, dot]
  | a :: as, b :: bs, y :: ys => by
    simp only [addL, dot, dot_addL as bs ys, Int.add_mul]
    omega

theorem dot_scaleL (m : Int) : ∀ (a x : List Int), dot (scaleL m a) x = m * dot a x
  | [], x => by simp [scaleL, dot]
  | _ :: _, [] => by simp [scaleL, dot]
  | a :: as, y :: ys => by
    simp only [scaleL, dot, dot_scaleL m as ys, Int.mul_add, Int.mul_assoc]

def allZero : List Int → Bool
  | [] => true
  | c :: cs => c == 0 && allZero cs

theorem dot_allZero : ∀ (a x : List Int), allZero a = true → dot a x = 0
  | [], _, _ => by simp [dot]
  | _ :: _, [], _ => rfl
  | c :: cs, y :: ys, h => by
    simp only [allZero, Bool.and_eq_true, beq_iff_eq] at h
    simp [dot, h.1, dot_allZero cs ys h.2]

inductive Step where
  | input (i : Nat)
  | combine (a b : Nat) (ma mb : Int)
  | cut (of : Nat) (g : Int) (q : List Int) (c : Int)
deriving Repr

def combineRow (ma mb : Int) (A B : Row) : Row :=
  ⟨addL (scaleL ma A.coefs) (scaleL mb B.coefs), ma * A.const + mb * B.const⟩

-- Coefficient lists compare up to trailing zeros: a combination keeps the longer list's length, while a certificate
-- may write the cut's quotient without its trailing zeros. Trimming changes no dot product (dot_trimZ).
def trimZ : List Int → List Int
  | [] => []
  | a :: as => match trimZ as with
    | [] => if a = 0 then [] else [a]
    | t => a :: t

theorem dot_trimZ : ∀ (a x : List Int), dot (trimZ a) x = dot a x
  | [], _ => rfl
  | _ :: _, [] => by simp only [dot_nil_right]
  | a :: as, y :: ys => by
    have ih := dot_trimZ as ys
    have key : trimZ (a :: as) = (match trimZ as with | [] => if a = 0 then [] else [a] | t => a :: t) := rfl
    rw [key]
    cases h : trimZ as with
    | nil =>
      rw [h] at ih
      have h0 : dot as ys = 0 := by rw [← ih]; simp [dot]
      by_cases ha : a = 0
      · simp [ha, dot, h0]
      · simp [ha, dot, h0]
    | cons t0 ts =>
      rw [h] at ih
      simp only [dot]
      rw [ih]

def cutOk (A : Row) (g : Int) (q : List Int) (c : Int) : Bool :=
  decide (1 ≤ g) && decide (trimZ A.coefs = trimZ (scaleL g q)) && decide (g * c ≤ A.const + g - 1)

def replay (inputs : List Row) : List Step → List Row → Option (List Row)
  | [], rows => some rows
  | .input i :: ss, rows =>
    match inputs[i]? with
    | some r => replay inputs ss (rows ++ [r])
    | none => none
  | .combine a b ma mb :: ss, rows =>
    match rows[a]?, rows[b]? with
    | some A, some B => if 0 < ma ∧ 0 < mb then replay inputs ss (rows ++ [combineRow ma mb A B]) else none
    | _, _ => none
  | .cut o g q c :: ss, rows =>
    match rows[o]? with
    | some A => if cutOk A g q c then replay inputs ss (rows ++ [⟨q, c⟩]) else none
    | none => none

def check (inputs : List Row) (steps : List Step) : Bool :=
  match replay inputs steps [] with
  | some rows =>
    match rows.getLast? with
    | some r => allZero r.coefs && decide (0 < r.const)
    | none => false
  | none => false

theorem cut_sound (g d c c' : Int) (hg : 1 ≤ g) (h : g * d + c ≤ 0) (hc : g * c' ≤ c + g - 1) : d + c' ≤ 0 := by
  have hd : g * (d + c') = g * d + g * c' := Int.mul_add g d c'
  refine Int.not_lt.mp (fun h1 => ?_)
  have h2 : g * 1 ≤ g * (d + c') := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  omega

-- Every row a replay produces holds wherever the inputs and the rows so far hold.
theorem replay_holds (inputs : List Row) (x : List Int) (hx : ∀ r ∈ inputs, eval r x ≤ 0) :
    ∀ (ss : List Step) (rows out : List Row), (∀ r ∈ rows, eval r x ≤ 0) →
      replay inputs ss rows = some out → ∀ r ∈ out, eval r x ≤ 0 := by
  intro ss
  induction ss with
  | nil =>
    intro rows out hrows h
    simp only [replay, Option.some.injEq] at h
    exact h ▸ hrows
  | cons s ss ih =>
    intro rows out hrows h
    cases s with
    | input i =>
      simp only [replay] at h
      split at h
      · rename_i r hr
        refine ih _ out ?_ h
        intro r' hr'
        rcases List.mem_append.mp hr' with hr' | hr'
        · exact hrows r' hr'
        · simp only [List.mem_singleton] at hr'
          exact hr' ▸ hx r (List.mem_of_getElem? hr)
      · exact absurd h (by simp)
    | combine a b ma mb =>
      simp only [replay] at h
      split at h
      · rename_i A B hA hB
        split at h
        · rename_i hm
          refine ih _ out ?_ h
          intro r' hr'
          rcases List.mem_append.mp hr' with hr' | hr'
          · exact hrows r' hr'
          · simp only [List.mem_singleton] at hr'
            subst hr'
            have eA := hrows A (List.mem_of_getElem? hA)
            have eB := hrows B (List.mem_of_getElem? hB)
            simp only [eval, combineRow, dot_addL, dot_scaleL] at eA eB ⊢
            have h1 : ma * (dot A.coefs x + A.const) ≤ ma * 0 := Int.mul_le_mul_of_nonneg_left eA (by omega)
            have h2 : mb * (dot B.coefs x + B.const) ≤ mb * 0 := Int.mul_le_mul_of_nonneg_left eB (by omega)
            simp only [Int.mul_add, Int.mul_zero] at h1 h2
            omega
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    | cut o g q c =>
      simp only [replay] at h
      split at h
      · rename_i A hA
        split at h
        · rename_i hok
          refine ih _ out ?_ h
          intro r' hr'
          rcases List.mem_append.mp hr' with hr' | hr'
          · exact hrows r' hr'
          · simp only [List.mem_singleton] at hr'
            subst hr'
            simp only [cutOk, Bool.and_eq_true, decide_eq_true_eq] at hok
            obtain ⟨⟨hg, hq⟩, hc⟩ := hok
            have eA := hrows A (List.mem_of_getElem? hA)
            have hdot : dot A.coefs x = g * dot q x := by
              rw [← dot_trimZ A.coefs x, hq, dot_trimZ, dot_scaleL]
            simp only [eval, hdot] at eA
            exact cut_sound g (dot q x) A.const c hg eA hc
        · exact absurd h (by simp)
      · exact absurd h (by simp)

/-- A certificate the checker accepts refutes its inputs: no integer point satisfies them all. -/
theorem sound (inputs : List Row) (steps : List Step) (h : check inputs steps = true) (x : List Int)
    (hx : ∀ r ∈ inputs, eval r x ≤ 0) : False := by
  simp only [check] at h
  split at h
  · rename_i rows hrows
    split at h
    · rename_i r hr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have hall := replay_holds inputs x hx steps [] rows (by simp) hrows
      have := hall r (List.mem_of_getLast? hr)
      simp only [eval, dot_allZero r.coefs x h.1] at this
      omega
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The induction rule: what holds at the start and survives every step holds after any sequence of steps. -/
theorem run_preserves {S I : Type} (step : S → I → S) (P : S → Prop) (start : S)
    (h0 : P start) (hs : ∀ s i, P s → P (step s i)) : ∀ (is : List I), P (is.foldl step start) := by
  intro is
  induction is generalizing start with
  | nil => exact h0
  | cons i is ih => exact ih (step start i) (hs start i h0)

end Cert

/-
Cert: the trusted core of gdp-wired, with its proofs. Lean 4.34.0, core only.

A row `Σ cᵢ·xᵢ + c ≤ 0` over the integers. A certificate is a list of steps that replays into rows: an input row, a
positive combination of two earlier rows, or a cut (an earlier row whose coefficients are all g times q, replaced by q
with a constant c such that g·c ≤ constant + g − 1). `check` accepts when the last row has only zero coefficients and a
positive constant. `sound`: if `check` accepts, no integer point satisfies every input row.

A row holds its nonzero coefficients alone (column, coefficient), in column order, so a step costs a row's nonzeros
rather than the table's width. Any list reads as a sum (`dot`); sorted lists stay sorted and cancel to [] under `addL`.

`run_preserves` is the induction rule a step machine's laws rest on: a property true at the start and preserved by
every step holds after every sequence of steps.
-/

namespace Cert

structure Row where
  coefs : List (Nat × Int)
  const : Int
deriving Repr

def dot : List (Nat × Int) → List Int → Int
  | [], _ => 0
  | p :: rest, x => p.2 * x.getD p.1 0 + dot rest x

def eval (r : Row) (x : List Int) : Int := dot r.coefs x + r.const

-- Two sorted lists merged, coefficients of one column added (a column that cancels dropped). The fuel only bounds the
-- recursion: out of it, the lists are put side by side, which reads the same.
def addF : Nat → List (Nat × Int) → List (Nat × Int) → List (Nat × Int)
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, a, [] => a
  | n + 1, p :: as, q :: bs =>
    if p.1 < q.1 then p :: addF n as (q :: bs)
    else if q.1 < p.1 then q :: addF n (p :: as) bs
    else if p.2 + q.2 = 0 then addF n as bs else (p.1, p.2 + q.2) :: addF n as bs

def addL (a b : List (Nat × Int)) : List (Nat × Int) := addF (a.length + b.length) a b

def scaleL (m : Int) (a : List (Nat × Int)) : List (Nat × Int) := if m = 0 then [] else a.map (fun p => (p.1, m * p.2))

def allZero : List (Nat × Int) → Bool
  | [] => true
  | p :: a => p.2 == 0 && allZero a

theorem dot_app (x : List Int) : ∀ (a b : List (Nat × Int)), dot (a ++ b) x = dot a x + dot b x
  | [], b => by simp [dot]
  | p :: a, b => by simp only [List.cons_append, dot, dot_app x a b]; omega

theorem dot_addF (x : List Int) : ∀ (n : Nat) (a b : List (Nat × Int)), dot (addF n a b) x = dot a x + dot b x
  | 0, a, b => by simp only [addF, dot_app]
  | _ + 1, [], b => by simp [addF, dot]
  | _ + 1, _ :: _, [] => by simp [addF, dot]
  | n + 1, p :: as, q :: bs => by
    simp only [addF]
    split
    · simp only [dot, dot_addF x n as (q :: bs)]; omega
    · split
      · simp only [dot, dot_addF x n (p :: as) bs]; omega
      · have hpq : p.1 = q.1 := by omega
        split
        · rename_i hz
          simp only [dot, dot_addF x n as bs, hpq]
          have : p.2 * x.getD q.1 0 + q.2 * x.getD q.1 0 = 0 := by rw [← Int.add_mul, hz, Int.zero_mul]
          omega
        · simp only [dot, dot_addF x n as bs, hpq, Int.add_mul]; omega

theorem dot_addL (a b : List (Nat × Int)) (x : List Int) : dot (addL a b) x = dot a x + dot b x := dot_addF x _ a b

theorem dot_map (m : Int) (x : List Int) : ∀ (a : List (Nat × Int)), dot (a.map (fun p => (p.1, m * p.2))) x = m * dot a x
  | [] => by simp [dot]
  | p :: a => by simp only [List.map_cons, dot, dot_map m x a, Int.mul_add, Int.mul_assoc]

theorem dot_scaleL (m : Int) (a : List (Nat × Int)) (x : List Int) : dot (scaleL m a) x = m * dot a x := by
  unfold scaleL
  split
  · rename_i h; subst h; simp [dot]
  · exact dot_map m x a

theorem dot_allZero : ∀ (a : List (Nat × Int)) (x : List Int), allZero a = true → dot a x = 0
  | [], _, _ => rfl
  | p :: a, x, h => by
    simp only [allZero, Bool.and_eq_true, beq_iff_eq] at h
    simp [dot, h.1, dot_allZero a x h.2]

inductive Step where
  | input (i : Nat)
  | combine (a b : Nat) (ma mb : Int)
  | cut (of : Nat) (g : Int) (q : List (Nat × Int)) (c : Int)
deriving Repr

def combineRow (ma mb : Int) (A B : Row) : Row :=
  ⟨addL (scaleL ma A.coefs) (scaleL mb B.coefs), ma * A.const + mb * B.const⟩

def cutOk (A : Row) (g : Int) (q : List (Nat × Int)) (c : Int) : Bool :=
  decide (1 ≤ g) && decide (A.coefs = scaleL g q) && decide (g * c ≤ A.const + g - 1)

-- The rows so far kept newest first, with their number (step i's row is at n − 1 − i): a row is put on the front and
-- read where it is, never past a chain of appends.
def replay (inputs : List Row) : List Step → Nat → List Row → Option (List Row)
  | [], _, rows => some rows
  | .input i :: ss, n, rows =>
    match inputs[i]? with
    | some r => replay inputs ss (n + 1) (r :: rows)
    | none => none
  | .combine a b ma mb :: ss, n, rows =>
    match rows[n - 1 - a]?, rows[n - 1 - b]? with
    | some A, some B => if a < n ∧ b < n ∧ 0 < ma ∧ 0 < mb then replay inputs ss (n + 1) (combineRow ma mb A B :: rows) else none
    | _, _ => none
  | .cut o g q c :: ss, n, rows =>
    match rows[n - 1 - o]? with
    | some A => if o < n ∧ cutOk A g q c then replay inputs ss (n + 1) (⟨q, c⟩ :: rows) else none
    | none => none

def check (inputs : List Row) (steps : List Step) : Bool :=
  match replay inputs steps 0 [] with
  | some rows =>
    match rows.head? with
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
    ∀ (ss : List Step) (n : Nat) (rows out : List Row), (∀ r ∈ rows, eval r x ≤ 0) →
      replay inputs ss n rows = some out → ∀ r ∈ out, eval r x ≤ 0 := by
  intro ss
  induction ss with
  | nil =>
    intro n rows out hrows h
    simp only [replay, Option.some.injEq] at h
    exact h ▸ hrows
  | cons s ss ih =>
    intro n rows out hrows h
    cases s with
    | input i =>
      simp only [replay] at h
      split at h
      · rename_i r hr
        refine ih _ _ out ?_ h
        intro r' hr'
        rcases List.mem_cons.mp hr' with hr' | hr'
        · exact hr' ▸ hx r (List.mem_of_getElem? hr)
        · exact hrows r' hr'
      · exact absurd h (by simp)
    | combine a b ma mb =>
      simp only [replay] at h
      split at h
      · rename_i A B hA hB
        split at h
        · rename_i hm
          refine ih _ _ out ?_ h
          intro r' hr'
          rcases List.mem_cons.mp hr' with hr' | hr'
          · subst hr'
            have eA := hrows A (List.mem_of_getElem? hA)
            have eB := hrows B (List.mem_of_getElem? hB)
            simp only [eval, combineRow, dot_addL, dot_scaleL] at eA eB ⊢
            have h1 : ma * (dot A.coefs x + A.const) ≤ ma * 0 := Int.mul_le_mul_of_nonneg_left eA (by omega)
            have h2 : mb * (dot B.coefs x + B.const) ≤ mb * 0 := Int.mul_le_mul_of_nonneg_left eB (by omega)
            simp only [Int.mul_add, Int.mul_zero] at h1 h2
            omega
          · exact hrows r' hr'
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    | cut o g q c =>
      simp only [replay] at h
      split at h
      · rename_i A hA
        split at h
        · rename_i hok
          refine ih _ _ out ?_ h
          intro r' hr'
          rcases List.mem_cons.mp hr' with hr' | hr'
          · subst hr'
            simp only [cutOk, Bool.and_eq_true, decide_eq_true_eq] at hok
            obtain ⟨_, ⟨hg, hq⟩, hc⟩ := hok
            have eA := hrows A (List.mem_of_getElem? hA)
            have hdot : dot A.coefs x = g * dot q x := by rw [hq, dot_scaleL]
            simp only [eval, hdot] at eA
            exact cut_sound g (dot q x) A.const c hg eA hc
          · exact hrows r' hr'
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
      have hall := replay_holds inputs x hx steps 0 [] rows (by simp) hrows
      have hm : r ∈ rows := by
        cases rows with
        | nil => simp at hr
        | cons a as => simp only [List.head?, Option.some.injEq] at hr; subst hr; exact List.mem_cons_self
      have := hall r hm
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

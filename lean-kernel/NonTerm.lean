import Live

/-!
Nontermination: a loop with a run that never ends, the claim `loop_halts_of` refutes.

`NeverEnds l`: for some maps and some params meeting the precondition, a run of turns from the start goes on forever.
It is the negation of `loop_halts_of`'s conclusion, so no loop has both (`halts_not_never_ends`,
`never_ends_refutes_halts`).

The certificate (`Recur`) is a closed recurrent set with its successor given:
- `set`, a condition over the state and the params;
- `wit`, a term per input over the state and the params: the turn taken from a state of the set;
- `start`, the params as values (every other variable 0), and `stem`, each turn's inputs as values, from the start
  into the set; each state on the way is held as its values on `dom`, the variables the run reads and writes.

`checkRecur` evaluates the stem (each turn meeting the guard and the assumption, the state after the last one in the
set), and builds the closure goal: a state in the set whose witnessed turn fails the guard or the assumption, or ends
outside the set. The kernel's tree must refute it (`checkIn`, Sets.lean). Then the run after the stem is the witnessed
turn taken again and again (`witRun`, by recursion on the turn's number): the successor is a term, so no choice is made
and the infinite run is built, not chosen. A lasso is the case where the set is the cycle's states.

`RecurCases` closes the set by cases instead (`never_ends_of_cases`): each case pins some variables to values (a
location) with a condition (the set's part there); one certificate refutes the set with no case holding, and each
case's goal is its condition with the witnessed turn failing, the pins substituted and the constants folded (`simpC`,
which keeps every value: `simpC_evalC`), so a large program's closure is checked a location at a time.
-/

namespace Kern

/-- Some run of the loop never ends: for some maps and some params meeting the precondition, a run of turns from the
start that goes on forever. -/
def NeverEnds (l : Loop) : Prop :=
  ∃ maps : Nat → Nat → Nat, ∃ ρ0 : Nat → Nat, evalC ρ0 maps l.pre = true ∧
    ∃ f : Nat → Nat → Nat, f 0 = applyS l.init ρ0 maps ∧ ∀ n, Turn l maps (f n) (f (n + 1))

/-- No loop both halts (`loop_halts_of`'s conclusion) and has a run that never ends. -/
theorem halts_not_never_ends (l : Loop)
    (h : ∀ maps ρ0, evalC ρ0 maps l.pre = true →
      ¬ ∃ f : Nat → Nat → Nat, f 0 = applyS l.init ρ0 maps ∧ ∀ n, Turn l maps (f n) (f (n + 1))) :
    ¬ NeverEnds l := by
  rintro ⟨maps, ρ0, hp, hf⟩
  exact h maps ρ0 hp hf

/-- So a loop proven to halt by `loop_halts_of` (its premises) never has a nontermination certificate that checks. -/
theorem never_ends_refutes_halts (l : Loop) (lv : Live) (hfrom : lv.from_ = trueC) (hto : lv.to = .not l.guard)
    (hhelps : ∀ h ∈ lv.helps, h.2 = []) (hguard : avoids l.inputs l.guard = true)
    (hlive : ∀ run : SRun l.machine, (∀ h ∈ lv.helps, ∀ n, ∃ m, n ≤ m ∧ ∀ p ∈ h.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) →
      ∀ n, evalC (run.st n).1 (run.st n).2 lv.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 lv.to = true)
    (hn : NeverEnds l) : False :=
  halts_not_never_ends l (loop_halts_of l lv hfrom hto hhelps hguard hlive) hn

/-! The certificate -/

-- Finitely many values: each listed variable its value (the first listed), every other 0.
def valsEnv (vs : List (Nat × Nat)) : Nat → Nat := fun i =>
  match lookup (fun p => p.1 == i) vs with
  | some p => p.2
  | none => 0

-- The maps the run is given: every cell 0 (a loop reads maps only as values it is given; any maps would do).
def noMaps : Nat → Nat → Nat := fun _ _ => 0

structure Recur where
  dom : List Nat                  -- the variables the run reads and writes (each stem state is its values there)
  start : List (Nat × Nat)        -- the params' values (any variable listed; the rest 0)
  stem : List (List (Nat × Nat))  -- each stem turn's inputs
  set : C                         -- the recurrent set, over the state and the params
  wit : List (Nat × E)            -- each input's value at a turn from the set, a term over the state and the params
  cert : Cert                     -- the closure goal's table, the hypotheses it names, and its tree

-- An environment as its values on the domain (valsEnv reads it back where it is 0 off the domain).
def onDom (dom : List Nat) (ρ : Nat → Nat) : List (Nat × Nat) := dom.map fun i => (i, ρ i)

-- The stem from ρ (its values on the domain): each turn's inputs meet the guard and the assumption; the state after the
-- last turn, as values. Each state is read from the values of the one before, so a long stem costs its length.
def stemEnd (l : Loop) (dom : List Nat) : List (Nat × Nat) → List (List (Nat × Nat)) → Option (List (Nat × Nat))
  | ρ, [] => some ρ
  | ρ, ι :: rest =>
    if evalC (withInputs l.inputs (valsEnv ρ) (valsEnv ι)) noMaps l.guard && evalC (withInputs l.inputs (valsEnv ρ) (valsEnv ι)) noMaps l.assume
    then stemEnd l dom (onDom dom (applyS l.body (withInputs l.inputs (valsEnv ρ) (valsEnv ι)) noMaps)) rest
    else none

-- The closure goal: a state in the set where the witnessed turn fails the guard or the assumption, or ends outside the
-- set. Refuted, every state of the set has a turn, the witnessed one, back into the set.
def recurGoal (l : Loop) (r : Recur) : List C :=
  [r.set, .not (.and (substC r.wit l.guard) (.and (substC r.wit l.assume) (substC r.wit (substC l.body r.set))))]

-- The domain holds every variable a turn or the start writes, and the start's.
def domOk (l : Loop) (r : Recur) : Bool :=
  l.inputs.all r.dom.contains && l.init.all (fun p => r.dom.contains p.1) && l.body.all (fun p => r.dom.contains p.1) &&
    r.start.all (fun p => r.dom.contains p.1)

-- The stem's end is in the set.
def stemIn (l : Loop) (r : Recur) : Bool :=
  match stemEnd l r.dom (onDom r.dom (applyS l.init (valsEnv r.start) noMaps)) r.stem with
  | some ρ => evalC (valsEnv ρ) noMaps r.set
  | none => false

-- The witness sets only inputs; the domain holds what is written; the start meets the precondition; the stem reaches
-- the set; the set is closed.
def checkRecur (l : Loop) (r : Recur) : Bool :=
  r.wit.all (fun p => l.inputs.contains p.1) && domOk l r && evalC (valsEnv r.start) noMaps l.pre && stemIn l r &&
    checkIn (recurGoal l r) r.cert

/-! Soundness -/

-- A run that never ends from ρ.
def RunsForever (l : Loop) (maps : Nat → Nat → Nat) (ρ : Nat → Nat) : Prop :=
  ∃ f : Nat → Nat → Nat, f 0 = ρ ∧ ∀ n, Turn l maps (f n) (f (n + 1))

-- The witnessed request: with the witness setting only inputs, the request it names is the state with the terms' values.
theorem withInputs_wit {inputs : List Nat} {wit : List (Nat × E)} (h : wit.all (fun p => inputs.contains p.1) = true)
    (ρ : Nat → Nat) (maps : Nat → Nat → Nat) : withInputs inputs ρ (applyS wit ρ maps) = applyS wit ρ maps := by
  funext i
  simp only [withInputs]
  split
  · rfl
  · rename_i hi
    refine (applyS_other ?_ ρ maps).symm
    intro hm
    obtain ⟨p, hp, hpi⟩ := List.mem_map.mp hm
    simp only [List.all_eq_true] at h
    exact hi (hpi ▸ h p hp)

-- The witnessed turn from ρ.
def witNext (l : Loop) (r : Recur) (maps : Nat → Nat → Nat) (ρ : Nat → Nat) : Nat → Nat :=
  applyS l.body (applyS r.wit ρ maps) maps

-- The closure goal refuted: from every state of the set, the witnessed turn is a turn, and it ends in the set.
theorem recur_step (l : Loop) (r : Recur) (hw : r.wit.all (fun p => l.inputs.contains p.1) = true)
    (hc : checkIn (recurGoal l r) r.cert = true) (maps : Nat → Nat → Nat) (ρ : Nat → Nat)
    (hs : evalC ρ maps r.set = true) :
    Turn l maps ρ (witNext l r maps ρ) ∧ evalC (witNext l r maps ρ) maps r.set = true := by
  have hn := sound_in _ _ hc ρ maps
  have key : evalC ρ maps (.and (substC r.wit l.guard) (.and (substC r.wit l.assume) (substC r.wit (substC l.body r.set)))) = true := by
    apply Decidable.byContradiction
    intro hf
    apply hn
    intro c hc'
    simp only [recurGoal, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl
    · exact hs
    · show (!evalC ρ maps _) = true
      rw [Bool.not_eq_true']
      exact Bool.eq_false_iff.mpr hf
  simp only [evalC, Bool.and_eq_true, subst_evalC] at key
  obtain ⟨hg, ha, hs'⟩ := key
  refine ⟨⟨applyS r.wit ρ maps, ?_, ?_, ?_⟩, hs'⟩
  · rw [withInputs_wit hw]; exact hg
  · rw [withInputs_wit hw]; exact ha
  · rw [withInputs_wit hw]; rfl

-- The run from a state of the set: the witnessed turn, again and again.
def witRun (l : Loop) (r : Recur) (maps : Nat → Nat → Nat) (ρ : Nat → Nat) : Nat → Nat → Nat
  | 0 => ρ
  | n + 1 => witNext l r maps (witRun l r maps ρ n)

theorem witRun_set (l : Loop) (r : Recur) (hw : r.wit.all (fun p => l.inputs.contains p.1) = true)
    (hc : checkIn (recurGoal l r) r.cert = true) (maps : Nat → Nat → Nat) (ρ : Nat → Nat)
    (hs : evalC ρ maps r.set = true) : ∀ n, evalC (witRun l r maps ρ n) maps r.set = true
  | 0 => hs
  | n + 1 => (recur_step l r hw hc maps _ (witRun_set l r hw hc maps ρ hs n)).2

-- From every state of the set, a run that never ends.
theorem forever_of_set (l : Loop) (r : Recur) (hw : r.wit.all (fun p => l.inputs.contains p.1) = true)
    (hc : checkIn (recurGoal l r) r.cert = true) (maps : Nat → Nat → Nat) (ρ : Nat → Nat)
    (hs : evalC ρ maps r.set = true) : RunsForever l maps ρ :=
  ⟨witRun l r maps ρ, rfl, fun n => (recur_step l r hw hc maps _ (witRun_set l r hw hc maps ρ hs n)).1⟩

-- One turn, then a run that never ends.
def consRun (ρ : Nat → Nat) (f : Nat → Nat → Nat) : Nat → Nat → Nat
  | 0 => ρ
  | n + 1 => f n

theorem forever_cons {l : Loop} {maps : Nat → Nat → Nat} {ρ ρ' : Nat → Nat} (ht : Turn l maps ρ ρ')
    (hf : RunsForever l maps ρ') : RunsForever l maps ρ := by
  obtain ⟨f, h0, hf⟩ := hf
  refine ⟨consRun ρ f, rfl, ?_⟩
  intro n
  cases n with
  | zero => show Turn l maps ρ (f 0); rw [h0]; exact ht
  | succ n => exact hf n

-- Values read back: an environment 0 off the domain is the values it has on the domain.
theorem lookup_onDom (ρ : Nat → Nat) (i : Nat) : ∀ dom : List Nat,
    lookup (fun p : Nat × Nat => p.1 == i) (dom.map fun j => (j, ρ j)) = if i ∈ dom then some (i, ρ i) else none
  | [] => by simp [lookup]
  | j :: dom => by
    simp only [List.map_cons, lookup, List.mem_cons]
    by_cases h : j = i
    · subst h; simp
    · have h' : (j == i) = false := by simpa using h
      simp only [h', Bool.false_eq_true, ite_false, lookup_onDom ρ i dom]
      by_cases hi : i ∈ dom
      · simp [hi]
      · simp [hi, Ne.symm h]

theorem valsEnv_onDom {dom : List Nat} {ρ : Nat → Nat} (h0 : ∀ i, i ∉ dom → ρ i = 0) : valsEnv (onDom dom ρ) = ρ := by
  funext i
  simp only [valsEnv, onDom, lookup_onDom]
  by_cases hi : i ∈ dom
  · simp [hi]
  · simp [hi, h0 i hi]

-- Values listed on the domain only are 0 off it.
theorem valsEnv_off {dom : List Nat} {vs : List (Nat × Nat)} (h : vs.all (fun p => dom.contains p.1) = true) :
    ∀ i, i ∉ dom → valsEnv vs i = 0 := by
  intro i hi
  simp only [valsEnv]
  split
  · rename_i p hp
    obtain ⟨hm, hpi⟩ := lookup_some hp
    simp only [List.all_eq_true] at h
    have := h p hm
    simp only [beq_iff_eq] at hpi
    rw [hpi] at this
    exact absurd (List.contains_iff_mem.mp this) hi
  · rfl

theorem onDom_keys (dom : List Nat) (ρ : Nat → Nat) : (onDom dom ρ).all (fun p => dom.contains p.1) = true := by
  simp [onDom, List.all_eq_true]

-- σ writes only on the domain: what was 0 off it stays 0.
theorem applyS_off {dom : List Nat} {σ : List (Nat × E)} (hσ : σ.all (fun p => dom.contains p.1) = true) {ρ : Nat → Nat}
    (h0 : ∀ i, i ∉ dom → ρ i = 0) (maps : Nat → Nat → Nat) : ∀ i, i ∉ dom → applyS σ ρ maps i = 0 := by
  intro i hi
  rw [applyS_other]
  · exact h0 i hi
  · intro hm
    obtain ⟨p, hp, hpi⟩ := List.mem_map.mp hm
    simp only [List.all_eq_true] at hσ
    exact hi (hpi ▸ List.contains_iff_mem.mp (hσ p hp))

theorem withInputs_off {dom inputs : List Nat} (hin : inputs.all dom.contains = true) {ρ : Nat → Nat}
    (h0 : ∀ i, i ∉ dom → ρ i = 0) (ι : Nat → Nat) : ∀ i, i ∉ dom → withInputs inputs ρ ι i = 0 := by
  intro i hi
  rw [withInputs_other]
  · exact h0 i hi
  · intro hm
    simp only [List.all_eq_true] at hin
    exact hi (List.contains_iff_mem.mp (hin i hm))

-- A stem that ends where a run never ends: the run from the stem's start never ends either.
theorem forever_stem (l : Loop) (dom : List Nat) (hin : l.inputs.all dom.contains = true)
    (hb : l.body.all (fun p => dom.contains p.1) = true) : ∀ (stem : List (List (Nat × Nat))) (ρ ρ' : List (Nat × Nat)),
    ρ.all (fun p => dom.contains p.1) = true → stemEnd l dom ρ stem = some ρ' →
    RunsForever l noMaps (valsEnv ρ') → RunsForever l noMaps (valsEnv ρ)
  | [], ρ, ρ', _, h, hf => by
    simp only [stemEnd, Option.some.injEq] at h
    subst h; exact hf
  | ι :: rest, ρ, ρ', hk, h, hf => by
    simp only [stemEnd] at h
    split at h
    · rename_i hok
      simp only [Bool.and_eq_true] at hok
      have hrest := forever_stem l dom hin hb rest _ ρ' (onDom_keys dom _) h hf
      have hoff := applyS_off hb (withInputs_off hin (valsEnv_off hk) (valsEnv ι)) noMaps
      rw [valsEnv_onDom hoff] at hrest
      exact forever_cons ⟨valsEnv ι, hok.1, hok.2, rfl⟩ hrest
    · exact absurd h (by simp)

/-- A checked certificate: the loop has a run that never ends. -/
theorem never_ends_of (l : Loop) (r : Recur) (h : checkRecur l r = true) : NeverEnds l := by
  simp only [checkRecur, domOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hw, ⟨⟨hin, hinit⟩, hb⟩, hst⟩, hpre⟩, hin'⟩, hc⟩ := h
  refine ⟨noMaps, valsEnv r.start, hpre, ?_⟩
  have hoff := applyS_off hinit (valsEnv_off hst) noMaps
  simp only [stemIn] at hin'
  split at hin'
  · rename_i ρ hend
    have := forever_stem l r.dom hin hb r.stem _ ρ (onDom_keys _ _) hend (forever_of_set l r hw hc noMaps _ hin')
    rw [valsEnv_onDom hoff] at this
    exact this
  · exact absurd hin' (by simp)

/-! The closure by cases

A large program's closure goal reads the whole body: every rule's term, with the witness's ifs inside. Read at one
location, most of it is constants. `RecurCases` splits the closure goal into cases: each case pins some variables to
values (a location, say) and names a condition (the part of the set at that location); `cover` refutes the set with no
case holding, and each case's goal, its pins substituted and its constants folded (`simpC`), refutes the case's
condition with the witnessed turn failing. Folding keeps every value (`simpC_evalC`), and the pins hold in the case, so
substituting them keeps every value too: every state of the set has the witnessed turn, back into the set. -/

/-! Constant folding -/

def tC : C := .le (.const 0) (.const 0)
def fC : C := .lt (.const 0) (.const 0)
-- A comparison of two constants that holds, or one that fails.
def isT : C → Bool
  | .le (.const a) (.const b) => decide (a ≤ b)
  | _ => false
def isF : C → Bool
  | .lt (.const a) (.const b) => decide (b ≤ a)
  | .le (.const a) (.const b) => decide (b < a)
  | _ => false

theorem isT_eval {c : C} (h : isT c = true) (ρ : Nat → Nat) (maps : Nat → Nat → Nat) : evalC ρ maps c = true := by
  match c, h with
  | .le (.const a) (.const b), h => simp only [isT, decide_eq_true_eq] at h; simp [evalC, evalE, h]
theorem isF_eval {c : C} (h : isF c = true) (ρ : Nat → Nat) (maps : Nat → Nat → Nat) : evalC ρ maps c = false := by
  match c, h with
  | .lt (.const a) (.const b), h => simp only [isF, decide_eq_true_eq] at h; simp only [evalC, evalE]; exact decide_eq_false (by omega)
  | .le (.const a) (.const b), h => simp only [isF, decide_eq_true_eq] at h; simp only [evalC, evalE]; exact decide_eq_false (by omega)

def foldAdd : E → E → E
  | .const 0, b => b
  | a, .const 0 => a
  | .const x, .const y => .const (x + y)
  | a, b => .add a b
def foldSub : E → E → E
  | a, .const 0 => a
  | .const x, .const y => .const (x - y)
  | a, b => .sub a b
def foldMul (k : Nat) (a : E) : E :=
  if k = 0 then .const 0 else if k = 1 then a else match a with
    | .const x => .const (k * x)
    | a => .mul k a
def foldProd : E → E → E
  | .const x, b => foldMul x b
  | a, .const y => foldMul y a
  | a, b => .prod a b
def foldMin : E → E → E
  | .const x, .const y => .const (min x y)
  | a, b => .min a b
def foldMax : E → E → E
  | .const x, .const y => .const (max x y)
  | a, b => .max a b
def foldLe : E → E → C
  | .const x, .const y => if x ≤ y then tC else fC
  | a, b => .le a b
def foldLt : E → E → C
  | .const x, .const y => if x < y then tC else fC
  | a, b => .lt a b
def foldEq : E → E → C
  | .const x, .const y => if x = y then tC else fC
  | a, b => .eq a b
def foldAnd (a b : C) : C := if isF a || isF b then fC else if isT a then b else if isT b then a else .and a b
def foldOr (a b : C) : C := if isT a || isT b then tC else if isF a then b else if isF b then a else .or a b
def foldNot (a : C) : C := if isT a then fC else if isF a then tC else .not a

-- An if whose condition folds to a constant is its branch (the other branch never read).
mutual
def simpE : E → E
  | .var i => .var i
  | .const n => .const n
  | .add a b => foldAdd (simpE a) (simpE b)
  | .sub a b => foldSub (simpE a) (simpE b)
  | .mul k a => foldMul k (simpE a)
  | .min a b => foldMin (simpE a) (simpE b)
  | .max a b => foldMax (simpE a) (simpE b)
  | .prod a b => foldProd (simpE a) (simpE b)
  | .ite c t f =>
    let c' := simpC c
    if isT c' then simpE t else if isF c' then simpE f else .ite c' (simpE t) (simpE f)
  | .get m key => .get m (simpE key)
def simpC : C → C
  | .le a b => foldLe (simpE a) (simpE b)
  | .lt a b => foldLt (simpE a) (simpE b)
  | .eq a b => foldEq (simpE a) (simpE b)
  | .and a b => foldAnd (simpC a) (simpC b)
  | .or a b => foldOr (simpC a) (simpC b)
  | .not a => foldNot (simpC a)
end

section
variable (ρ : Nat → Nat) (maps : Nat → Nat → Nat)

theorem foldAdd_eval (a b : E) : evalE ρ maps (foldAdd a b) = evalE ρ maps a + evalE ρ maps b := by
  unfold foldAdd; split <;> simp_all [evalE]
theorem foldSub_eval (a b : E) : evalE ρ maps (foldSub a b) = evalE ρ maps a - evalE ρ maps b := by
  unfold foldSub; split <;> simp_all [evalE]
theorem foldMul_eval (k : Nat) (a : E) : evalE ρ maps (foldMul k a) = k * evalE ρ maps a := by
  unfold foldMul
  split
  · simp_all [evalE]
  · split
    · simp_all
    · split <;> simp_all [evalE]
theorem foldProd_eval (a b : E) : evalE ρ maps (foldProd a b) = evalE ρ maps a * evalE ρ maps b := by
  unfold foldProd
  split
  · simp [foldMul_eval, evalE]
  · simp [foldMul_eval, evalE, Nat.mul_comm]
  · simp [evalE]
theorem foldMin_eval (a b : E) : evalE ρ maps (foldMin a b) = min (evalE ρ maps a) (evalE ρ maps b) := by
  unfold foldMin; split <;> simp_all [evalE]
theorem foldMax_eval (a b : E) : evalE ρ maps (foldMax a b) = max (evalE ρ maps a) (evalE ρ maps b) := by
  unfold foldMax; split <;> simp_all [evalE]
theorem foldLe_eval (a b : E) : evalC ρ maps (foldLe a b) = decide (evalE ρ maps a ≤ evalE ρ maps b) := by
  unfold foldLe; split
  · split <;> (rename_i h; simp [tC, fC, evalC, evalE, h])
  · simp [evalC]
theorem foldLt_eval (a b : E) : evalC ρ maps (foldLt a b) = decide (evalE ρ maps a < evalE ρ maps b) := by
  unfold foldLt; split
  · split <;> (rename_i h; simp [tC, fC, evalC, evalE, h])
  · simp [evalC]
theorem foldEq_eval (a b : E) : evalC ρ maps (foldEq a b) = decide (evalE ρ maps a = evalE ρ maps b) := by
  unfold foldEq; split
  · split <;> (rename_i h; simp [tC, fC, evalC, evalE, h])
  · simp [evalC]
theorem foldAnd_eval (a b : C) : evalC ρ maps (foldAnd a b) = (evalC ρ maps a && evalC ρ maps b) := by
  unfold foldAnd
  split
  · rename_i h
    simp only [Bool.or_eq_true] at h
    rcases h with h | h <;> simp [isF_eval h, fC, evalC, evalE]
  · split
    · rename_i _ h; simp [isT_eval h]
    · split
      · rename_i _ _ h; simp [isT_eval h]
      · simp [evalC]
theorem foldOr_eval (a b : C) : evalC ρ maps (foldOr a b) = (evalC ρ maps a || evalC ρ maps b) := by
  unfold foldOr
  split
  · rename_i h
    simp only [Bool.or_eq_true] at h
    rcases h with h | h <;> simp [isT_eval h, tC, evalC, evalE]
  · split
    · rename_i _ h; simp [isF_eval h]
    · split
      · rename_i _ _ h; simp [isF_eval h]
      · simp [evalC]
theorem foldNot_eval (a : C) : evalC ρ maps (foldNot a) = !evalC ρ maps a := by
  unfold foldNot
  split
  · rename_i h; simp [isT_eval h, fC, evalC, evalE]
  · split
    · rename_i _ h; simp [isF_eval h, tC, evalC, evalE]
    · simp [evalC]

mutual
theorem simpE_evalE : (e : E) → evalE ρ maps (simpE e) = evalE ρ maps e
  | .var i => by simp [simpE]
  | .const n => by simp [simpE]
  | .add a b => by simp [simpE, foldAdd_eval, evalE, simpE_evalE a, simpE_evalE b]
  | .sub a b => by simp [simpE, foldSub_eval, evalE, simpE_evalE a, simpE_evalE b]
  | .mul k a => by simp [simpE, foldMul_eval, evalE, simpE_evalE a]
  | .min a b => by simp [simpE, foldMin_eval, evalE, simpE_evalE a, simpE_evalE b]
  | .max a b => by simp [simpE, foldMax_eval, evalE, simpE_evalE a, simpE_evalE b]
  | .prod a b => by simp [simpE, foldProd_eval, evalE, simpE_evalE a, simpE_evalE b]
  | .ite c t f => by
    have hc := simpC_evalC c
    simp only [simpE]
    split
    · rename_i h; rw [isT_eval h] at hc; simp [evalE, ← hc, simpE_evalE t]
    · split
      · rename_i _ h; rw [isF_eval h] at hc; simp [evalE, ← hc, simpE_evalE f]
      · simp [evalE, hc, simpE_evalE t, simpE_evalE f]
  | .get m key => by simp [simpE, evalE, simpE_evalE key]
theorem simpC_evalC : (c : C) → evalC ρ maps (simpC c) = evalC ρ maps c
  | .le a b => by simp [simpC, foldLe_eval, evalC, simpE_evalE a, simpE_evalE b]
  | .lt a b => by simp [simpC, foldLt_eval, evalC, simpE_evalE a, simpE_evalE b]
  | .eq a b => by simp [simpC, foldEq_eval, evalC, simpE_evalE a, simpE_evalE b]
  | .and a b => by simp [simpC, foldAnd_eval, evalC, simpC_evalC a, simpC_evalC b]
  | .or a b => by simp [simpC, foldOr_eval, evalC, simpC_evalC a, simpC_evalC b]
  | .not a => by simp [simpC, foldNot_eval, evalC, simpC_evalC a]
end
end

/-! Pins: variables at values -/

-- The pins as a condition: each variable equal to its value (none: true).
def pinC : List (Nat × Nat) → C
  | [] => tC
  | [p] => .eq (.var p.1) (.const p.2)
  | p :: ps => .and (.eq (.var p.1) (.const p.2)) (pinC ps)
def pinSub (σ : List (Nat × Nat)) : List (Nat × E) := σ.map fun p => (p.1, .const p.2)

theorem pinC_holds (ρ : Nat → Nat) (maps : Nat → Nat → Nat) : ∀ (σ : List (Nat × Nat)), evalC ρ maps (pinC σ) = true → ∀ p ∈ σ, ρ p.1 = p.2
  | [], _ => by simp
  | [q], h => by simp [pinC, evalC, evalE] at h; intro p hp; simp at hp; subst hp; exact of_decide_eq_true h
  | q :: r :: ps, h => by
    simp [pinC, evalC, evalE] at h
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact of_decide_eq_true h.1
    · exact pinC_holds ρ maps (r :: ps) h.2 p hp

-- Where the pins hold, substituting them changes nothing.
theorem applyS_pins (ρ : Nat → Nat) (maps : Nat → Nat → Nat) (σ : List (Nat × Nat)) (h : ∀ p ∈ σ, ρ p.1 = p.2) :
    applyS (pinSub σ) ρ maps = ρ := by
  funext i
  simp only [applyS]
  cases ha : assoc (pinSub σ) i with
  | none => rfl
  | some e =>
    simp only [assoc, Option.map_eq_some_iff] at ha
    obtain ⟨q, hq, rfl⟩ := ha
    obtain ⟨hm, hi⟩ := lookup_some hq
    simp only [beq_iff_eq] at hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    simp only at hi ⊢
    simp only [evalE]
    rw [← hi, h p hp]

/-! The certificate -/

-- The closure goal's second hypothesis: the witnessed turn fails the guard or the assumption, or ends outside the set.
def closeNeg (l : Loop) (set : C) (wit : List (Nat × E)) : C :=
  .not (.and (substC wit l.guard) (.and (substC wit l.assume) (substC wit (substC l.body set))))

structure RecurCases where
  dom : List Nat
  start : List (Nat × Nat)
  stem : List (List (Nat × Nat))
  set : C
  wit : List (Nat × E)
  cover : Cert                               -- refutes the set with no case holding
  cases : List (List (Nat × Nat) × C × Cert) -- each case: its pins, its condition, its goal's certificate

-- The stem and the domain read as a plain certificate's (its tree unused).
def RecurCases.base (r : RecurCases) : Recur := ⟨r.dom, r.start, r.stem, r.set, r.wit, ([], [], .leaf [] [] [] [])⟩

def coverGoal (r : RecurCases) : List C := r.set :: r.cases.map fun c => .not (.and (pinC c.1) c.2.1)
def caseGoal (l : Loop) (r : RecurCases) (σ : List (Nat × Nat)) (cond : C) : List C :=
  [simpC (substC (pinSub σ) cond), simpC (substC (pinSub σ) (closeNeg l r.set r.wit))]

def checkRecurCases (l : Loop) (r : RecurCases) : Bool :=
  r.wit.all (fun p => l.inputs.contains p.1) && domOk l r.base && evalC (valsEnv r.start) noMaps l.pre && stemIn l r.base &&
    checkIn (coverGoal r) r.cover && r.cases.all (fun c => checkIn (caseGoal l r c.1 c.2.1) c.2.2)

/-! Soundness -/

-- Every state of the set has the witnessed turn, back into the set.
theorem cases_close (l : Loop) (r : RecurCases) (hcov : checkIn (coverGoal r) r.cover = true)
    (hcs : r.cases.all (fun c => checkIn (caseGoal l r c.1 c.2.1) c.2.2) = true) (maps : Nat → Nat → Nat) (ρ : Nat → Nat)
    (hs : evalC ρ maps r.set = true) : evalC ρ maps (closeNeg l r.set r.wit) = false := by
  -- some case holds
  have hk : ∃ c ∈ r.cases, evalC ρ maps (.and (pinC c.1) c.2.1) = true := by
    apply Decidable.byContradiction
    intro hn
    apply sound_in _ _ hcov ρ maps
    intro c hc
    simp only [coverGoal, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨k, hk, rfl⟩
    · exact hs
    · simp only [evalC, Bool.not_eq_true']
      exact Bool.eq_false_iff.mpr (fun h => hn ⟨k, hk, h⟩)
  obtain ⟨c, hc, hpc⟩ := hk
  simp only [evalC, Bool.and_eq_true] at hpc
  have hpins := applyS_pins ρ maps c.1 (pinC_holds ρ maps c.1 hpc.1)
  have hck : checkIn (caseGoal l r c.1 c.2.1) c.2.2 = true := by
    simp only [List.all_eq_true] at hcs; exact hcs c hc
  apply Bool.eq_false_iff.mpr
  intro hneg
  apply sound_in _ _ hck ρ maps
  intro d hd
  simp only [caseGoal, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · rw [simpC_evalC, subst_evalC, hpins]; exact hpc.2
  · rw [simpC_evalC, subst_evalC, hpins]; exact hneg

-- The run from a state of the set: the witnessed turn, again and again (as `witRun`, for a closure by cases).
theorem cases_step (l : Loop) (r : RecurCases) (hw : r.wit.all (fun p => l.inputs.contains p.1) = true)
    (hcov : checkIn (coverGoal r) r.cover = true) (hcs : r.cases.all (fun c => checkIn (caseGoal l r c.1 c.2.1) c.2.2) = true)
    (maps : Nat → Nat → Nat) (ρ : Nat → Nat) (hs : evalC ρ maps r.set = true) :
    Turn l maps ρ (witNext l r.base maps ρ) ∧ evalC (witNext l r.base maps ρ) maps r.set = true := by
  have key : evalC ρ maps (.and (substC r.wit l.guard) (.and (substC r.wit l.assume) (substC r.wit (substC l.body r.set)))) = true := by
    have := cases_close l r hcov hcs maps ρ hs
    simp only [closeNeg, evalC, Bool.not_eq_false'] at this
    simpa [evalC] using this
  simp only [evalC, Bool.and_eq_true, subst_evalC] at key
  obtain ⟨hg, ha, hs'⟩ := key
  refine ⟨⟨applyS r.wit ρ maps, ?_, ?_, ?_⟩, hs'⟩
  · rw [withInputs_wit hw]; exact hg
  · rw [withInputs_wit hw]; exact ha
  · rw [withInputs_wit hw]; rfl

theorem cases_run (l : Loop) (r : RecurCases) (hw : r.wit.all (fun p => l.inputs.contains p.1) = true)
    (hcov : checkIn (coverGoal r) r.cover = true) (hcs : r.cases.all (fun c => checkIn (caseGoal l r c.1 c.2.1) c.2.2) = true)
    (maps : Nat → Nat → Nat) (ρ : Nat → Nat) (hs : evalC ρ maps r.set = true) : ∀ n, evalC (witRun l r.base maps ρ n) maps r.set = true
  | 0 => hs
  | n + 1 => (cases_step l r hw hcov hcs maps _ (cases_run l r hw hcov hcs maps ρ hs n)).2

/-- A checked certificate by cases: the loop has a run that never ends. -/
theorem never_ends_of_cases (l : Loop) (r : RecurCases) (h : checkRecurCases l r = true) : NeverEnds l := by
  simp only [checkRecurCases, domOk, RecurCases.base, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hw, ⟨⟨hin, hinit⟩, hb⟩, hst⟩, hpre⟩, hin'⟩, hcov⟩, hcs⟩ := h
  refine ⟨noMaps, valsEnv r.start, hpre, ?_⟩
  have hoff := applyS_off hinit (valsEnv_off hst) noMaps
  have hforever : ∀ ρ, evalC ρ noMaps r.set = true → RunsForever l noMaps ρ := fun ρ hs =>
    ⟨witRun l r.base noMaps ρ, rfl, fun n => (cases_step l r hw hcov hcs noMaps _ (cases_run l r hw hcov hcs noMaps ρ hs n)).1⟩
  simp only [stemIn] at hin'
  split at hin'
  · rename_i ρ hend
    have := forever_stem l r.dom hin hb r.stem _ ρ (onDom_keys _ _) hend (hforever _ hin')
    rw [valsEnv_onDom hoff] at this
    exact this
  · exact absurd hin' (by simp)

end Kern

#print axioms Kern.never_ends_of
#print axioms Kern.never_ends_of_cases
#print axioms Kern.simpC_evalC
#print axioms Kern.halts_not_never_ends
#print axioms Kern.never_ends_refutes_halts

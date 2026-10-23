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

end Kern

#print axioms Kern.never_ends_of
#print axioms Kern.halts_not_never_ends
#print axioms Kern.never_ends_refutes_halts

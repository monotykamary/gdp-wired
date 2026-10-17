import Kernel
/-!
Progress: flags and "some request makes this happen", the two parts of kernel.ts that Kernel.lean left to TypeScript.

Flags. A step may name conditions (kernel.ts's `step.flags`), decided once per step from the request and the state
before it. Step terms read flag f as `.eq (.var f) (.const 1)`; the flag's variable holds 1 when its condition holds
and 0 when it doesn't (`decideFlags`). The exporter passes flags through untouched: Lean inlines them itself (`inlineC`
turns each `.eq (.var f) (.const 1)` into the condition, `inlineE` any other read of f into `ite cond 1 0`, exactly what
kernel.ts's goal builder does) and proves inlining keeps the meaning (`inline_evalE`, `inline_evalC`). A machine with
flags reaches, outside its flag variables, exactly the states its inlined machine reaches (`freach_plain`,
`fmreach_plain`), so the induction rules of Kernel.lean carry over (`fmachine_sound`, `fmmachine_sound`).

Progress. "In every reachable state where `when` holds, some request makes `then` true of its step": the request is
named (a term per input over the state and params), and Lean builds kernel.ts's two goals itself: the request is allowed
(the machine's assumption holds of it), and the step it causes makes `then` hold. `then` reads the state before the step
by plain names and after it by primed names (`prime`, `primeMaps`). `progress_sound`: for every reachable state where
`when` holds, the named request is a step the machine allows, and `then` holds of it.
-/
namespace Kern
open Cert

/-! Flags -/

def flagOf (fl : List (Nat × C)) (i : Nat) : Option C := (lookup (fun p => p.1 == i) fl).map (·.2)
def flagSub (fl : List (Nat × C)) : List (Nat × E) := fl.map fun p => (p.1, .ite p.2 (.const 1) (.const 0))
def flagVars (fl : List (Nat × C)) : List Nat := fl.map (·.1)
-- The state with every flag decided: flag f holds 1 when its condition holds before the step, else 0.
def decideFlags (fl : List (Nat × C)) (ρ : Nat → Nat) (maps : Nat → Nat → Nat) : Nat → Nat := applyS (flagSub fl) ρ maps

-- A read of flag f as a condition becomes the condition itself.
def eqOrFlag (fl : List (Nat × C)) (a b a' b' : E) : C :=
  match a, b with
  | .var i, .const 1 => match flagOf fl i with
    | some c => c
    | none => .eq a' b'
  | _, _ => .eq a' b'

mutual
def inlineE (fl : List (Nat × C)) : E → E
  | .var i => match flagOf fl i with
    | some c => .ite c (.const 1) (.const 0)
    | none => .var i
  | .const n => .const n
  | .add a b => .add (inlineE fl a) (inlineE fl b)
  | .sub a b => .sub (inlineE fl a) (inlineE fl b)
  | .mul k a => .mul k (inlineE fl a)
  | .min a b => .min (inlineE fl a) (inlineE fl b)
  | .max a b => .max (inlineE fl a) (inlineE fl b)
  | .prod a b => .prod (inlineE fl a) (inlineE fl b)
  | .ite c t f => .ite (inlineC fl c) (inlineE fl t) (inlineE fl f)
  | .get m key => .get m (inlineE fl key)
def inlineC (fl : List (Nat × C)) : C → C
  | .le a b => .le (inlineE fl a) (inlineE fl b)
  | .lt a b => .lt (inlineE fl a) (inlineE fl b)
  | .eq a b => eqOrFlag fl a b (inlineE fl a) (inlineE fl b)
  | .and a b => .and (inlineC fl a) (inlineC fl b)
  | .or a b => .or (inlineC fl a) (inlineC fl b)
  | .not a => .not (inlineC fl a)
end

theorem lookup_map_same {α : Type} (p : α → Bool) (g : α → α) (hg : ∀ a, p (g a) = p a) :
    ∀ l : List α, lookup p (l.map g) = (lookup p l).map g
  | [] => rfl
  | a :: as => by
    simp only [List.map_cons, lookup, hg]
    split <;> simp [lookup_map_same p g hg as]

theorem lookup_map_pred {α β : Type} (p : β → Bool) (g : α → β) :
    ∀ l : List α, lookup p (l.map g) = (lookup (fun a => p (g a)) l).map g
  | [] => rfl
  | a :: as => by
    simp only [List.map_cons, lookup]
    split <;> simp [lookup_map_pred p g as]

theorem lookup_map_fst {β γ : Type} (i : Nat) (g : β → γ) :
    ∀ l : List (Nat × β), lookup (fun q => q.1 == i) (l.map fun q => (q.1, g q.2)) = (lookup (fun q => q.1 == i) l).map fun q => (q.1, g q.2)
  | [] => rfl
  | a :: as => by
    simp only [List.map_cons, lookup]
    split <;> simp [lookup_map_fst i g as]

theorem assoc_flagSub (fl : List (Nat × C)) (i : Nat) :
    assoc (flagSub fl) i = (flagOf fl i).map (fun c => .ite c (.const 1) (.const 0)) := by
  simp only [assoc, flagSub, flagOf, lookup_map_pred, Option.map_map]; rfl

theorem assoc_map_snd (σ : List (Nat × E)) (g : E → E) (i : Nat) :
    assoc (σ.map fun p => (p.1, g p.2)) i = (assoc σ i).map g := by
  simp only [assoc, lookup_map_pred, Option.map_map]; rfl

mutual
theorem inline_evalE (fl : List (Nat × C)) (ρ : Nat → Nat) (maps : Nat → Nat → Nat) :
    (e : E) → evalE ρ maps (inlineE fl e) = evalE (decideFlags fl ρ maps) maps e
  | .var i => by
    cases h : flagOf fl i <;> simp [inlineE, h, evalE, decideFlags, applyS, assoc_flagSub]
  | .const n => by simp [inlineE, evalE]
  | .add a b => by simp [inlineE, evalE, inline_evalE fl ρ maps a, inline_evalE fl ρ maps b]
  | .sub a b => by simp [inlineE, evalE, inline_evalE fl ρ maps a, inline_evalE fl ρ maps b]
  | .mul k a => by simp [inlineE, evalE, inline_evalE fl ρ maps a]
  | .min a b => by simp [inlineE, evalE, inline_evalE fl ρ maps a, inline_evalE fl ρ maps b]
  | .max a b => by simp [inlineE, evalE, inline_evalE fl ρ maps a, inline_evalE fl ρ maps b]
  | .prod a b => by simp [inlineE, evalE, inline_evalE fl ρ maps a, inline_evalE fl ρ maps b]
  | .ite c t f => by simp [inlineE, evalE, inline_evalC fl ρ maps c, inline_evalE fl ρ maps t, inline_evalE fl ρ maps f]
  | .get m key => by simp [inlineE, evalE, inline_evalE fl ρ maps key]
theorem inline_evalC (fl : List (Nat × C)) (ρ : Nat → Nat) (maps : Nat → Nat → Nat) :
    (c : C) → evalC ρ maps (inlineC fl c) = evalC (decideFlags fl ρ maps) maps c
  | .le a b => by simp [inlineC, evalC, inline_evalE fl ρ maps a, inline_evalE fl ρ maps b]
  | .lt a b => by simp [inlineC, evalC, inline_evalE fl ρ maps a, inline_evalE fl ρ maps b]
  | .eq a b => by
    have ha := inline_evalE fl ρ maps a
    have hb := inline_evalE fl ρ maps b
    simp only [inlineC, eqOrFlag]
    split
    · rename_i i
      cases h : flagOf fl i with
      | none => simp only [evalC, ha, hb]
      | some c =>
        simp only [evalC, evalE, decideFlags, applyS, assoc_flagSub, h, Option.map_some]
        cases evalC ρ maps c <;> simp
    · simp only [evalC, ha, hb]
  | .and a b => by simp [inlineC, evalC, inline_evalC fl ρ maps a, inline_evalC fl ρ maps b]
  | .or a b => by simp [inlineC, evalC, inline_evalC fl ρ maps a, inline_evalC fl ρ maps b]
  | .not a => by simp [inlineC, evalC, inline_evalC fl ρ maps a]
end

-- Flag conditions read the request and the state, never a flag.
def flagsOk (fl : List (Nat × C)) : Bool := fl.all fun p => avoids (flagVars fl) p.2

-- A term that reads none of these variables.
def avoidsE (vs : List Nat) (e : E) : Bool := vs.all fun i => !occE i e

theorem avoidsE_occ {vs : List Nat} {e : E} (h : avoidsE vs e = true) {i : Nat} (hi : occE i e = true) : i ∉ vs := by
  intro hm
  simp only [avoidsE, List.all_eq_true] at h
  have := h i hm; simp [hi] at this

-- Two states that agree outside some variables.
def Agree (vs : List Nat) (ρ ρ' : Nat → Nat) : Prop := ∀ i, i ∉ vs → ρ i = ρ' i

theorem flagOf_none {fl : List (Nat × C)} {i : Nat} (h : flagOf fl i = none) : i ∉ flagVars fl := by
  intro hm
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  simp only [flagOf, Option.map_eq_none_iff] at h
  have := lookup_none_all h p hp
  simp at this

theorem flagOf_some {fl : List (Nat × C)} {i : Nat} {c : C} (h : flagOf fl i = some c) : ∃ p ∈ fl, p.2 = c := by
  simp only [flagOf, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p, (lookup_some hp).1, rfl⟩

theorem decide_other {fl : List (Nat × C)} {i : Nat} (hi : i ∉ flagVars fl) (ρ : Nat → Nat) (maps : Nat → Nat → Nat) :
    decideFlags fl ρ maps i = ρ i :=
  applyS_other (by simpa [flagSub, flagVars] using hi) ρ maps

-- States that agree outside the flags decide the flags alike, so they agree everywhere once the flags are decided.
theorem decide_agree {fl : List (Nat × C)} (hf : flagsOk fl = true) {X X' : Nat → Nat} (maps : Nat → Nat → Nat)
    (h : Agree (flagVars fl) X X') : decideFlags fl X maps = decideFlags fl X' maps := by
  funext i
  simp only [decideFlags, applyS, assoc_flagSub]
  cases hc : flagOf fl i with
  | none => exact h i (flagOf_none hc)
  | some c =>
    obtain ⟨p, hp, rfl⟩ := flagOf_some hc
    simp only [flagsOk, List.all_eq_true] at hf
    have hav := hf p hp
    simp only [Option.map_some, evalE]
    rw [congrC X X' maps p.2 (fun j hj => h j (avoids_occ hav hj))]

theorem withInputs_agree {vs ins : List Nat} {ρ ρ' : Nat → Nat} (h : Agree vs ρ ρ') (ι : Nat → Nat) :
    Agree vs (withInputs ins ρ ι) (withInputs ins ρ' ι) := by
  intro i hi; simp only [withInputs]; split
  · rfl
  · exact h i hi

/-! Scalar machines with flags -/

structure FMachine where
  m : Machine                 -- step terms and the assumption may read flags
  flags : List (Nat × C)      -- each flag's variable and its condition

def FMachine.plain (f : FMachine) : Machine :=
  { f.m with step := f.m.step.map (fun p => (p.1, inlineE f.flags p.2)), assume := inlineC f.flags f.m.assume }

inductive FReach (f : FMachine) (maps : Nat → Nat → Nat) : (Nat → Nat) → Prop
  | start (ρ : Nat → Nat) : evalC ρ maps f.m.pre = true → FReach f maps (applyS f.m.init ρ maps)
  | step (ρ ι : Nat → Nat) : FReach f maps ρ →
      evalC (decideFlags f.flags (withInputs f.m.inputs ρ ι) maps) maps f.m.assume = true →
      FReach f maps (applyS f.m.step (decideFlags f.flags (withInputs f.m.inputs ρ ι) maps) maps)

def checkFMachine (f : FMachine) (ps : MachineProof) : Bool :=
  flagsOk f.flags && ps.all (fun p => avoids (flagVars f.flags) p.1) && checkMachine f.plain ps

theorem freach_plain (f : FMachine) (hf : flagsOk f.flags = true) (maps : Nat → Nat → Nat) :
    ∀ {ρ}, FReach f maps ρ → ∃ ρ₀, Reach f.plain maps ρ₀ ∧ Agree (flagVars f.flags) ρ ρ₀ := by
  intro ρ hr
  induction hr with
  | start ρ h0 => exact ⟨_, Reach.start (m := f.plain) ρ h0, fun _ _ => rfl⟩
  | step ρ ι _ ha ih =>
    obtain ⟨ρ₀, hr₀, hag⟩ := ih
    have hdec := decide_agree hf maps (withInputs_agree (ins := f.m.inputs) hag ι)
    refine ⟨_, Reach.step (m := f.plain) ρ₀ ι hr₀ ?_, ?_⟩
    · show evalC (withInputs f.m.inputs ρ₀ ι) maps (inlineC f.flags f.m.assume) = true
      rw [inline_evalC, ← hdec]; exact ha
    · intro i hi
      show _ = applyS (f.m.step.map (fun p => (p.1, inlineE f.flags p.2))) (withInputs f.m.inputs ρ₀ ι) maps i
      simp only [applyS, assoc_map_snd]
      cases h : assoc f.m.step i with
      | none =>
        simp only [Option.map_none]
        rw [decide_other hi]; exact withInputs_agree (ins := f.m.inputs) hag ι i hi
      | some e => simp only [Option.map_some, inline_evalE, hdec]

/-- Flags inlined by Lean: every law of an accepted proof of the inlined machine, none reading a flag, holds in every
state the machine with flags reaches. -/
theorem fmachine_sound (f : FMachine) (ps : MachineProof) (h : checkFMachine f ps = true) (maps : Nat → Nat → Nat) :
    ∀ ρ, FReach f maps ρ → ∀ l ∈ ps.map (·.1), evalC ρ maps l = true := by
  simp only [checkFMachine, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hf, hl⟩, hc⟩ := h
  intro ρ hr l hlm
  obtain ⟨ρ₀, hr₀, hag⟩ := freach_plain f hf maps hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hlm
  rw [congrC ρ ρ₀ maps p.1 (fun j hj => hag j (avoids_occ (hl p hp) hj))]
  exact machine_sound f.plain ps hc maps ρ₀ hr₀ p.1 hlm

/-! Machines with maps and flags -/

structure FMMachine where
  m : MMachine
  flags : List (Nat × C)

def inlineW (fl : List (Nat × C)) (ws : List (Nat × E × E)) : List (Nat × E × E) :=
  ws.map fun w => (w.1, inlineE fl w.2.1, inlineE fl w.2.2)

def FMMachine.plain (f : FMMachine) : MMachine :=
  { f.m with
    step := f.m.step.map (fun p => (p.1, inlineE f.flags p.2))
    writes := inlineW f.flags f.m.writes
    assume := inlineC f.flags f.m.assume }

inductive FMReach (f : FMMachine) : (Nat → Nat) → (Nat → Nat → Nat) → Prop
  | start (ρ : Nat → Nat) (M : Nat → Nat → Nat) : StartMaps f.m M → evalC ρ M f.m.pre = true → FMReach f (applyS f.m.init ρ M) M
  | step (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) : FMReach f ρ M →
      evalC (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M f.m.assume = true →
      FMReach f (applyS f.m.step (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M)
        (writeMaps f.m.writes (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M)

def checkFMMachine (f : FMMachine) (ps : List MEntry) : Bool :=
  flagsOk f.flags && avoids (flagVars f.flags) f.m.pre && ps.all (fun e => avoids (flagVars f.flags) e.law.holds)
    && checkMMachine f.plain ps

theorem writeMaps_inline (fl : List (Nat × C)) (ws : List (Nat × E × E)) (X : Nat → Nat) (M : Nat → Nat → Nat) :
    writeMaps (inlineW fl ws) X M = writeMaps ws (decideFlags fl X M) M := by
  funext mp key
  simp only [writeMaps, inlineW, lookup_map_pred]
  cases lookup (fun w : Nat × E × E => w.1 == mp) ws with
  | none => rfl
  | some w => simp only [Option.map_some, inline_evalE]

theorem fmreach_plain (f : FMMachine) (hf : flagsOk f.flags = true) :
    ∀ {ρ M}, FMReach f ρ M → ∃ ρ₀, MReach f.plain ρ₀ M ∧ Agree (flagVars f.flags) ρ ρ₀ := by
  intro ρ M hr
  induction hr with
  | start ρ M hM h0 => exact ⟨_, MReach.start (m := f.plain) ρ M hM h0, fun _ _ => rfl⟩
  | step ρ M ι _ ha ih =>
    obtain ⟨ρ₀, hr₀, hag⟩ := ih
    have hdec := decide_agree hf M (withInputs_agree (ins := f.m.inputs) hag ι)
    have hstep := MReach.step (m := f.plain) ρ₀ M ι hr₀ (by
      show evalC (withInputs f.m.inputs ρ₀ ι) M (inlineC f.flags f.m.assume) = true
      rw [inline_evalC, ← hdec]; exact ha)
    have hw : writeMaps f.plain.writes (withInputs f.plain.inputs ρ₀ ι) M
        = writeMaps f.m.writes (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M := by
      show writeMaps (inlineW f.flags f.m.writes) (withInputs f.m.inputs ρ₀ ι) M = _
      rw [writeMaps_inline, ← hdec]
    rw [hw] at hstep
    refine ⟨_, hstep, ?_⟩
    intro i hi
    show _ = applyS (f.m.step.map (fun p => (p.1, inlineE f.flags p.2))) (withInputs f.m.inputs ρ₀ ι) M i
    simp only [applyS, assoc_map_snd]
    cases h : assoc f.m.step i with
    | none =>
      simp only [Option.map_none]
      rw [decide_other hi]; exact withInputs_agree (ins := f.m.inputs) hag ι i hi
    | some e => simp only [Option.map_some, inline_evalE, hdec]

-- A law that reads no flag holds alike in states that agree outside the flags.
theorem holds_agree {vs : List Nat} (l : MLaw) (hav : avoids vs l.holds = true) {ρ ρ₀ : Nat → Nat} (hag : Agree vs ρ ρ₀)
    (M : Nat → Nat → Nat) : l.Holds ρ₀ M → l.Holds ρ M := by
  unfold MLaw.Holds
  split
  · intro h; rwa [congrC ρ ρ₀ M l.holds (fun j hj => hag j (avoids_occ hav hj))]
  · rename_i kv _
    intro h v
    rw [congrC (upd ρ kv v) (upd ρ₀ kv v) M l.holds (fun j hj => by
      simp only [upd]; split
      · rfl
      · exact hag j (avoids_occ hav hj))]
    exact h v

/-- Flags inlined by Lean, with maps: every law of an accepted proof of the inlined machine holds in every state the
machine with flags reaches. -/
theorem fmmachine_sound (f : FMMachine) (ps : List MEntry) (h : checkFMMachine f ps = true) :
    ∀ ρ M, FMReach f ρ M → ∀ e ∈ ps, e.law.Holds ρ M := by
  simp only [checkFMMachine, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hf, _⟩, hl⟩, hc⟩ := h
  intro ρ M hr e he
  obtain ⟨ρ₀, hr₀, hag⟩ := fmreach_plain f hf hr
  exact holds_agree e.law (hl e he) hag M (mmachine_sound f.plain ps hc ρ₀ M hr₀ e he)

/-! Progress -/

structure Progress where
  when : C
  then_ : C
  req : List (Nat × E)          -- the request: an input and its term over the state and params
  prime : List (Nat × Nat)      -- a state variable, and the name `then` reads its value after the step by
  primeMaps : List (Nat × Nat)  -- a map, and the name `then` reads it after the step by
  insts : List (Nat × E)        -- (law index, key): where the goals assume the laws about every key
  allowed : List VDef × Tree
  causes : List VDef × Tree

-- A term of the step, at the named request: flags inlined, then the request's terms for the inputs.
def nowE (f : FMMachine) (pp : Progress) (e : E) : E := substE pp.req (inlineE f.flags e)
-- What a state variable is after the step: its step term, or itself.
def stepTerm (f : FMMachine) (v : Nat) : E :=
  match assoc f.m.step v with
  | some e => e
  | none => .var v
def primeSub (f : FMMachine) (pp : Progress) : List (Nat × E) := pp.prime.map fun q => (q.2, nowE f pp (stepTerm f q.1))
-- A read of a primed map is the map after the step's write (read-over-write); any other read is the map before.
def rdAfter (f : FMMachine) (pp : Progress) : Nat → E → E := fun mp k =>
  match lookup (fun q => q.2 == mp) pp.primeMaps with
  | some q => match lookup (fun w => w.1 == q.1) f.m.writes with
    | some w => .ite (.eq k (nowE f pp w.2.1)) (nowE f pp w.2.2) (.get q.1 k)
    | none => .get q.1 k
  | none => .get mp k

def progressBefore (f : FMMachine) (laws : List MLaw) (pp : Progress) : List C :=
  [f.m.pre] ++ scalarHyps laws ++ instHyps laws pp.insts ++ [pp.when]
def allowedGoal (f : FMMachine) (laws : List MLaw) (pp : Progress) : List C :=
  progressBefore f laws pp ++ [.not (substC pp.req (inlineC f.flags f.m.assume))]
def causesGoal (f : FMMachine) (laws : List MLaw) (pp : Progress) : List C :=
  progressBefore f laws pp ++ [.not (substRC (pp.req ++ primeSub f pp) (rdAfter f pp) pp.then_)]

-- The request names only inputs, no primed name is an input, and `then` reads no flag.
def checkProgress (f : FMMachine) (ps : List MEntry) (pp : Progress) : Bool :=
  pp.req.all (fun p => f.m.inputs.contains p.1) && pp.prime.all (fun q => !f.m.inputs.contains q.2)
    && avoids (flagVars f.flags) pp.then_
    && checkGoal ⟨pp.allowed.1, allowedGoal f (ps.map (·.law)) pp⟩ pp.allowed.2
    && checkGoal ⟨pp.causes.1, causesGoal f (ps.map (·.law)) pp⟩ pp.causes.2

-- What `then` reads: primed names after the step, the rest before it (with the request's inputs).
def primed (prime : List (Nat × Nat)) (after before : Nat → Nat) : Nat → Nat := fun i =>
  match lookup (fun q => q.2 == i) prime with
  | some q => after q.1
  | none => before i
def primedMaps (pm : List (Nat × Nat)) (after before : Nat → Nat → Nat) : Nat → Nat → Nat := fun mp =>
  match lookup (fun q => q.2 == mp) pm with
  | some q => after q.1
  | none => before mp

theorem lookup_append {α : Type} (p : α → Bool) : ∀ (l1 l2 : List α),
    lookup p (l1 ++ l2) = match lookup p l1 with | some a => some a | none => lookup p l2
  | [], _ => rfl
  | a :: as, l2 => by simp only [List.cons_append, lookup]; split <;> simp [lookup_append p as l2]

theorem assoc_none_of {σ : List (Nat × E)} {i : Nat} (h : i ∉ σ.map (·.1)) : assoc σ i = none := by
  cases ha : assoc σ i with
  | none => rfl
  | some e => exact absurd (assoc_mem ha) h

-- Every hypothesis before the request holds at a reachable state where `when` holds.
theorem before_true (f : FMMachine) (ps : List MEntry) (pp : Progress) (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (hpre : evalC ρ M f.m.pre = true) (hlaws : ∀ e ∈ ps, e.law.Holds ρ M) (hw : evalC ρ M pp.when = true) :
    ∀ c ∈ progressBefore f (ps.map (·.law)) pp, evalC ρ M c = true := by
  intro c hc
  simp only [progressBefore, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ((rfl | hc) | hc) | rfl
  · exact hpre
  · simp only [scalarHyps, List.mem_filterMap] at hc
    obtain ⟨l, hl, hk⟩ := hc
    split at hk
    · rename_i hkey
      simp only [Option.some.injEq] at hk; subst hk
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp hl
      have := hlaws e' he'
      simpa [MLaw.Holds, hkey] using this
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
        have := hlaws e' he'
        simp only [MLaw.Holds, hkey] at this
        rw [subst_evalC]
        rw [congrC _ (upd ρ kv (evalE ρ M p.2)) M e'.law.holds (fun i _ => by
          simp only [applyS, assoc, lookup, upd]
          by_cases hik : i = kv
          · subst hik; simp
          · have hb : (kv == i) = false := by simp; omega
            simp only [hb, Bool.false_eq_true, ite_false, Option.map_none, hik])]
        exact this _
      · simp at hk
    · simp at hk
  · exact hw

/-- Progress: in every reachable state where `when` holds, the named request (its inputs ι, the rest of the state as it
is) is a step the machine allows, and `then` holds of that step: primed names read the state and maps after it, plain
names the state before it with the request's inputs. -/
def ProgressHolds (f : FMMachine) (pp : Progress) : Prop :=
    ∀ ρ M, FMReach f ρ M → evalC ρ M pp.when = true →
      evalC (decideFlags f.flags (withInputs f.m.inputs ρ (applyS pp.req ρ M)) M) M f.m.assume = true ∧
      evalC (primed pp.prime (applyS f.m.step (decideFlags f.flags (withInputs f.m.inputs ρ (applyS pp.req ρ M)) M) M)
          (withInputs f.m.inputs ρ (applyS pp.req ρ M)))
        (primedMaps pp.primeMaps (writeMaps f.m.writes (decideFlags f.flags (withInputs f.m.inputs ρ (applyS pp.req ρ M)) M) M) M)
        pp.then_ = true

theorem progress_sound (f : FMMachine) (ps : List MEntry) (pp : Progress)
    (hl : checkFMMachine f ps = true) (hp : checkProgress f ps pp = true) : ProgressHolds f pp := by
  unfold ProgressHolds
  revert hl hp
  intro hl hp
  show ∀ ρ M, FMReach f ρ M → evalC ρ M pp.when = true →
      evalC (decideFlags f.flags (withInputs f.m.inputs ρ (applyS pp.req ρ M)) M) M f.m.assume = true ∧
      evalC (primed pp.prime (applyS f.m.step (decideFlags f.flags (withInputs f.m.inputs ρ (applyS pp.req ρ M)) M) M)
          (withInputs f.m.inputs ρ (applyS pp.req ρ M)))
        (primedMaps pp.primeMaps (writeMaps f.m.writes (decideFlags f.flags (withInputs f.m.inputs ρ (applyS pp.req ρ M)) M) M) M)
        pp.then_ = true
  have hl0 := hl
  simp only [checkFMMachine, Bool.and_eq_true, List.all_eq_true] at hl
  obtain ⟨⟨⟨hf, hpref⟩, hlf⟩, hc⟩ := hl
  simp only [checkProgress, Bool.and_eq_true, List.all_eq_true] at hp
  obtain ⟨⟨⟨⟨hreq, hprime⟩, _⟩, hal⟩, hca⟩ := hp
  intro ρ M hr hw
  obtain ⟨ρ₀, hr₀, hag⟩ := fmreach_plain f hf hr
  -- The laws and the precondition hold here.
  have hlaws : ∀ e ∈ ps, e.law.Holds ρ M := fmmachine_sound f ps hl0 ρ M hr
  have hcm := hc
  simp only [checkMMachine, Bool.and_eq_true] at hcm
  obtain ⟨⟨hpa, hpr⟩, _⟩ := hcm
  simp only [Bool.not_eq_true'] at hpr
  have hpre : evalC ρ M f.m.pre = true := by
    rw [congrC ρ ρ₀ M f.m.pre (fun j hj => hag j (avoids_occ hpref hj))]
    exact pre_mreach (m := f.plain) hpa hpr hr₀
  have hb := before_true f ps pp ρ M hpre hlaws hw
  -- The request's state: its inputs, the rest as it is.
  have hX : applyS pp.req ρ M = withInputs f.m.inputs ρ (applyS pp.req ρ M) := by
    funext i
    simp only [withInputs]
    split
    · rfl
    · rename_i hi
      exact applyS_other (fun hm => by
        obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hm
        exact hi (by simpa using hreq p hp')) ρ M
  refine ⟨?_, ?_⟩
  · apply Decidable.byContradiction; intro hn
    apply sound _ _ hal ρ M
    intro c hc'
    simp only [allowedGoal, List.mem_append, List.mem_singleton] at hc'
    rcases hc' with hc' | rfl
    · exact hb c hc'
    · simp only [evalC, subst_evalC, inline_evalC]
      rw [← hX] at hn; simpa using hn
  · apply Decidable.byContradiction; intro hn
    apply sound _ _ hca ρ M
    intro c hc'
    simp only [causesGoal, List.mem_append, List.mem_singleton] at hc'
    rcases hc' with hc' | rfl
    · exact hb c hc'
    · let e := decideFlags f.flags (applyS pp.req ρ M) M
      have hnow : ∀ t, evalE ρ M (nowE f pp t) = evalE e M t := by
        intro t; simp only [nowE, subst_evalE, inline_evalE, e]
      have hrd : ∀ mp k, evalE ρ M (rdAfter f pp mp k)
          = primedMaps pp.primeMaps (writeMaps f.m.writes e M) M mp (evalE ρ M k) := by
        intro mp k
        simp only [rdAfter, primedMaps]
        cases hq : lookup (fun q => q.2 == mp) pp.primeMaps with
        | none => simp [evalE]
        | some q =>
          simp only [writeMaps]
          cases hw : lookup (fun w => w.1 == q.1) f.m.writes with
          | none => simp [evalE]
          | some w =>
            simp only [evalE, evalC, hnow]
            by_cases hk : evalE ρ M k = evalE e M w.2.1 <;> simp [hk]
      have henv : applyS (pp.req ++ primeSub f pp) ρ M = primed pp.prime (applyS f.m.step e M) (applyS pp.req ρ M) := by
        funext i
        have hps : lookup (fun p : Nat × E => p.1 == i) (primeSub f pp)
            = (lookup (fun q => q.2 == i) pp.prime).map (fun q => (q.2, nowE f pp (stepTerm f q.1))) := by
          simp only [primeSub, lookup_map_pred]
        simp only [primed, applyS, assoc, lookup_append, hps]
        cases hq : lookup (fun q => q.2 == i) pp.prime with
        | none => cases lookup (fun p => p.1 == i) pp.req <;> rfl
        | some q =>
          have ⟨hqm, hqi⟩ := lookup_some hq
          simp only [beq_iff_eq] at hqi
          have h1 : lookup (fun p => p.1 == i) pp.req = none := by
            cases h1 : lookup (fun p => p.1 == i) pp.req with
            | none => rfl
            | some p =>
              exfalso
              have ⟨hpm, hpi⟩ := lookup_some h1
              simp only [beq_iff_eq] at hpi
              have h3 := hprime q hqm
              have h4 := hreq p hpm
              rw [hpi, ← hqi] at h4
              simp at h3 h4; exact h3 h4
          simp only [h1, Option.map_some]
          rw [hnow]
          simp only [stepTerm]
          cases hs : assoc f.m.step q.1 with
          | none =>
            rw [show Option.map (fun x => x.2) (lookup (fun p => p.1 == q.1) f.m.step) = none from hs]
            simp [evalE, e]
          | some t =>
            rw [show Option.map (fun x => x.2) (lookup (fun p => p.1 == q.1) f.m.step) = some t from hs]
      simp only [evalC, substR_evalC _ _ _ M _ hrd, henv]
      rw [← hX] at hn; simpa [e] using hn

-- The named request is a step the machine takes: the state after it is reachable too.
theorem progress_reach (f : FMMachine) (ps : List MEntry) (pp : Progress)
    (hl : checkFMMachine f ps = true) (hp : checkProgress f ps pp = true) {ρ M} (hr : FMReach f ρ M)
    (hw : evalC ρ M pp.when = true) :
    FMReach f (applyS f.m.step (decideFlags f.flags (withInputs f.m.inputs ρ (applyS pp.req ρ M)) M) M)
      (writeMaps f.m.writes (decideFlags f.flags (withInputs f.m.inputs ρ (applyS pp.req ρ M)) M) M) :=
  FMReach.step ρ M _ hr (progress_sound f ps pp hl hp ρ M hr hw).1

end Kern

#print axioms Kern.inline_evalC
#print axioms Kern.fmachine_sound
#print axioms Kern.fmmachine_sound
#print axioms Kern.progress_sound
#print axioms Kern.progress_reach

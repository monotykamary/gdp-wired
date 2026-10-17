import Steps

/-!
Sets: kernel.ts's machines with sets, proven sound. A set is a map with cells 0 or 1; three things go beyond FMMachine:
a request carries whole maps (`carried`: any maps at each request), a step writes a map at every key at once (`every`:
the value at each key, read with the key bound), and a flag may hold at every key (`qflags`: ∀ key. body, its body
reading no flag). Lean decides a quantified flag classically, which only the meaning needs; the checker never does.

kernel.ts closes each quantified flag ?f in a goal: ?f ≤ 1; ?f = 0 ∨ body(t) at keys t the proof names (`qinsts`); and
?f = 1 ∨ ¬body(w) at a fresh witness w (`wits`). A real step satisfies these with w a failing key when ?f = 0, so a goal
that refutes them refutes the machine. Lean builds the same closed goals.
-/

namespace Kern
open Classical

structure SMachine where
  f : FMMachine
  carried : List Nat               -- maps a request carries
  every : List (Nat × Nat × E)     -- (map, bound key, value): the map at every key
  qflags : List (Nat × Nat × C)    -- (flag variable, bound key, body): 1 when the body holds at every key, else 0
  wits : List (Nat × Nat)          -- (flag variable, its witness variable)

def SMachine.qVars (s : SMachine) : List Nat := s.qflags.map (·.1)
def SMachine.wVars (s : SMachine) : List Nat := s.wits.map (·.2)

/-! The meaning -/

-- The maps a step reads: its own, with the maps the request carries.
def withCarried (s : SMachine) (M κ : Nat → Nat → Nat) : Nat → Nat → Nat := fun mp => if s.carried.contains mp then κ mp else M mp

-- Each quantified flag decided: 1 where its body holds at every key, else 0.
noncomputable def decideQ (s : SMachine) (X : Nat → Nat) (N : Nat → Nat → Nat) : Nat → Nat := fun v =>
  match lookup (fun q => q.1 == v) s.qflags with
  | some q => if ∀ key, holdsC (upd X q.2.1 key) N q.2.2 then 1 else 0
  | none => X v

-- A step's state before its terms: inputs set, quantified flags decided, then the plain flags; and the maps it reads.
noncomputable def sView (s : SMachine) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) : (Nat → Nat) × (Nat → Nat → Nat) :=
  (decideFlags s.f.flags (decideQ s (withInputs s.f.m.inputs ρ ι) (withCarried s M κ)) (withCarried s M κ), withCarried s M κ)

-- The maps after a step: a map written at every key, its value there; any other as kernel.ts's writes leave it.
def everyMaps (s : SMachine) (D : Nat → Nat) (N : Nat → Nat → Nat) : Nat → Nat → Nat := fun mp key =>
  match lookup (fun w => w.1 == mp) s.every with
  | some w => evalE (upd D w.2.1 key) N w.2.2
  | none => writeMaps s.f.m.writes D N mp key

noncomputable def sNext (s : SMachine) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) : (Nat → Nat) × (Nat → Nat → Nat) :=
  (applyS s.f.m.step (sView s ρ M ι κ).1 (sView s ρ M ι κ).2, everyMaps s (sView s ρ M ι κ).1 (sView s ρ M ι κ).2)

inductive SReach (s : SMachine) : (Nat → Nat) → (Nat → Nat → Nat) → Prop
  | start (ρ : Nat → Nat) (M : Nat → Nat → Nat) : StartMaps s.f.m M → evalC ρ M s.f.m.pre = true → SReach s (applyS s.f.m.init ρ M) M
  | step (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) : SReach s ρ M →
      evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume = true → SReach s (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2

/-! The goals -/

-- Each quantified flag closed, at the keys the proof names.
def closingHyps (s : SMachine) (qinsts : List (Nat × E)) : List C :=
  s.qflags.flatMap fun q =>
    [.le (.var q.1) (.const 1)]
      ++ (qinsts.filter (fun p => p.1 == q.1)).map (fun p => .or (.eq (.var q.1) (.const 0)) (substC [(q.2.1, p.2)] q.2.2))
      ++ (match lookup (fun w => w.1 == q.1) s.wits with
          | some w => [.or (.eq (.var q.1) (.const 1)) (.not (substC [(q.2.1, .var w.2)] q.2.2))]
          | none => [])

-- A map written at every key reads, after the step, its value at the key read; any other map as stepRd reads it.
def stepRdS (s : SMachine) (τ : List (Nat × E)) (rd : Nat → E → E) : Nat → E → E := fun mp k =>
  match lookup (fun w => w.1 == mp) s.every with
  | some w => substRE ((w.2.1, k) :: τ) rd (inlineE s.f.flags w.2.2)
  | none => stepRd s.f τ rd mp k

-- A later step reads the maps its request carries by fresh names.
def frameRd (mr : List (Nat × Nat)) (rd : Nat → E → E) : Nat → E → E := fun mp k =>
  match lookup (fun p => p.1 == mp) mr with
  | some p => .get p.2 k
  | none => rd mp k

def sFrameHyps (s : SMachine) (laws : List MLaw) (insts qinsts : List (Nat × E)) (w : C) : List C :=
  scalarHyps laws ++ instHyps laws insts ++ [inlineC s.f.flags s.f.m.assume, w] ++ closingHyps s qinsts

def sRun (s : SMachine) (laws : List MLaw) (insts qinsts : List (Nat × E)) :
    List C → List (List (Nat × Nat)) → List (List (Nat × Nat)) → List (Nat × E) → (Nat → E → E) → List C × List (Nat × E) × (Nat → E → E)
  | w :: ws, r :: rs, mr :: mrs, σ, rd =>
    ((sFrameHyps s laws insts qinsts w).map (substRC (frameSub r σ) (frameRd mr rd))
        ++ (sRun s laws insts qinsts ws rs mrs (stepSub s.f (frameSub r σ) (frameRd mr rd)) (stepRdS s (frameSub r σ) (frameRd mr rd))).1,
      (sRun s laws insts qinsts ws rs mrs (stepSub s.f (frameSub r σ) (frameRd mr rd)) (stepRdS s (frameSub r σ) (frameRd mr rd))).2)
  | _, _, _, σ, rd => ([], σ, rd)

/-! What a step's goal reads it by -/

-- A key where a quantified flag's body fails, when one does.
noncomputable def witnessKey (X : Nat → Nat) (N : Nat → Nat → Nat) (q : Nat × Nat × C) : Nat :=
  if h : ∃ key, ¬ holdsC (upd X q.2.1 key) N q.2.2 then Classical.choose h else 0

def SMachine.extVars (s : SMachine) : List Nat := s.f.m.inputs ++ s.qVars ++ s.wVars

-- A step's request as its goal reads it: the inputs, each quantified flag's value, each witness.
noncomputable def sReq (s : SMachine) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) : Nat → Nat := fun v =>
  if s.f.m.inputs.contains v then ι v
  else match lookup (fun q => q.1 == v) s.qflags with
    | some _ => decideQ s (withInputs s.f.m.inputs ρ ι) (withCarried s M κ) v
    | none => match lookup (fun w => w.2 == v) s.wits with
      | some w => match lookup (fun q => q.1 == w.1) s.qflags with
        | some q => witnessKey (withInputs s.f.m.inputs ρ ι) (withCarried s M κ) q
        | none => 0
      | none => 0

def withExt (s : SMachine) (ρ e : Nat → Nat) : Nat → Nat := fun v => if s.extVars.contains v then e v else ρ v

-- The maps later requests carry, at their fresh names.
def renMaps : List (List (Nat × Nat)) → List (Nat → Nat → Nat) → (Nat → Nat → Nat) → Nat → Nat → Nat
  | r :: rs, κ :: κs, b => fun mp => match lookup (fun p => p.2 == mp) r with
    | some p => κ p.1
    | none => renMaps rs κs b mp
  | _, _, b => b

/-! The checks -/

def distinctPairs (ws : List (Nat × Nat)) : Bool := distinct (ws.map (·.1)) && distinct (ws.map (·.2))

-- The machine's own side conditions: inputs, flags, quantified flags and witnesses are distinct variables; a body reads no flag, quantified flag or witness, and its key is none of them; every
-- quantified flag has a witness; the plain flags and the step read no witness.
def sOk (s : SMachine) : Bool :=
  flagsOk s.f.flags && distinct s.qVars && distinctPairs s.wits
    && s.qflags.all (fun q => s.wits.any (·.1 == q.1))
    && distinct (s.extVars ++ flagVars s.f.flags)
    && s.qflags.all (fun q => avoids (s.qVars ++ s.wVars ++ flagVars s.f.flags) q.2.2 && !(s.extVars ++ flagVars s.f.flags).contains q.2.1)
    && s.f.flags.all (fun p => avoids s.wVars p.2)
    && avoids (s.wVars ++ s.qVars) s.f.m.pre
    && s.f.m.step.all (fun p => avoidsE s.wVars (inlineE s.f.flags p.2))
    && s.f.m.writes.all (fun w => avoidsE s.wVars (inlineE s.f.flags w.2.1) && avoidsE s.wVars (inlineE s.f.flags w.2.2))
    && s.every.all (fun w => avoidsE s.wVars (inlineE s.f.flags w.2.2) && !(s.extVars ++ flagVars s.f.flags).contains w.2.1
        && !(s.f.m.writes.map (·.1)).contains w.1 && !s.carried.contains w.1)
    && avoids s.wVars s.f.m.assume

/-! One step's view -/

theorem lookup_unique {p : Nat × Nat × C} {l : List (Nat × Nat × C)} (hd : distinct (l.map (·.1)) = true) (hp : p ∈ l) :
    lookup (fun q => q.1 == p.1) l = some p := by
  induction l with
  | nil => simp at hp
  | cons a as ih =>
    simp only [List.map_cons] at hd
    obtain ⟨hna, hd'⟩ := distinct_cons hd
    simp only [lookup]
    rcases List.mem_cons.mp hp with rfl | hp'
    · simp
    · have hne : (a.1 == p.1) = false := by
        simp only [beq_eq_false_iff_ne]; intro he; exact hna (by rw [he]; exact List.mem_map_of_mem hp')
      simp only [hne, Bool.false_eq_true, ite_false]; exact ih hd' hp'

theorem lookup_unique2 {p : Nat × Nat} {l : List (Nat × Nat)} (hd : distinct (l.map (·.2)) = true) (hp : p ∈ l) :
    lookup (fun q => q.2 == p.2) l = some p := lookup_ren hd p hp

theorem lookup_unique1 {p : Nat × Nat} {l : List (Nat × Nat)} (hd : distinct (l.map (·.1)) = true) (hp : p ∈ l) :
    lookup (fun q => q.1 == p.1) l = some p := by
  induction l with
  | nil => simp at hp
  | cons a as ih =>
    simp only [List.map_cons] at hd
    obtain ⟨hna, hd'⟩ := distinct_cons hd
    simp only [lookup]
    rcases List.mem_cons.mp hp with rfl | hp'
    · simp
    · have hne : (a.1 == p.1) = false := by
        simp only [beq_eq_false_iff_ne]; intro he; exact hna (by rw [he]; exact List.mem_map_of_mem hp')
      simp only [hne, Bool.false_eq_true, ite_false]; exact ih hd' hp'

theorem applyS_single (k : Nat) (t : E) (W : Nat → Nat) (M : Nat → Nat → Nat) : applyS [(k, t)] W M = upd W k (evalE W M t) := by
  funext i; simp only [applyS, assoc, lookup, upd]
  by_cases h : i = k
  · subst h; simp
  · have hb : (k == i) = false := by simp; omega
    simp [hb, h]

-- Agreeing states decide the plain flags alike, wherever the flag conditions don't read where they differ.
theorem decide_agree_on {fl : List (Nat × C)} {V : List Nat} (hav : ∀ p ∈ fl, avoids V p.2 = true) {X X' : Nat → Nat}
    (N : Nat → Nat → Nat) (h : Agree V X X') : Agree V (decideFlags fl X N) (decideFlags fl X' N) := by
  intro i hi
  simp only [decideFlags, applyS, assoc_flagSub]
  cases hc : flagOf fl i with
  | none => exact h i hi
  | some c =>
    obtain ⟨p, hp, rfl⟩ := flagOf_some hc
    simp only [Option.map_some, evalE]
    rw [congrC X X' N p.2 (fun j hj => h j (avoids_occ (hav p hp) hj))]

section view
variable (s : SMachine) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat)

theorem sOk_parts (hs : sOk s = true) :
    flagsOk s.f.flags = true ∧ distinct s.qVars = true ∧ distinctPairs s.wits = true ∧ (∀ q ∈ s.qflags, ∃ w ∈ s.wits, w.1 = q.1)
      ∧ distinct (s.extVars ++ flagVars s.f.flags) = true
      ∧ (∀ q ∈ s.qflags, avoids (s.qVars ++ s.wVars ++ flagVars s.f.flags) q.2.2 = true ∧ q.2.1 ∉ s.extVars ++ flagVars s.f.flags)
      ∧ (∀ p ∈ s.f.flags, avoids s.wVars p.2 = true) := by
  simp only [sOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq, Bool.not_eq_true'] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hf, hq⟩, hw⟩, hcov⟩, hd⟩, hb⟩, hfl⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hs
  refine ⟨hf, hq, hw, fun q hq' => hcov q hq', hd, fun q hq' => ⟨(hb q hq').1, fun hm => ?_⟩, hfl⟩
  have h2 := (hb q hq').2
  exact absurd hm (by simpa using h2)

-- The extended variables are apart: an input is no quantified flag or witness, and so on.
theorem ext_apart (hs : sOk s = true) :
    (∀ v ∈ s.f.m.inputs, v ∉ s.qVars ∧ v ∉ s.wVars) ∧ (∀ v ∈ s.qVars, v ∉ s.wVars) := by
  obtain ⟨_, _, _, _, hd, _, _⟩ := sOk_parts s hs
  obtain ⟨hd1, _, _⟩ := distinct_append hd
  simp only [SMachine.extVars, List.append_assoc] at hd1
  obtain ⟨_, hd2, hi⟩ := distinct_append hd1
  obtain ⟨_, _, hqw⟩ := distinct_append hd2
  exact ⟨fun v hv => ⟨fun h => hi v hv (List.mem_append_left _ h), fun h => hi v hv (List.mem_append_right _ h)⟩, hqw⟩

-- (F1) The goal's view and the decided quantified flags agree outside the witnesses.
theorem view_agree (hs : sOk s = true) :
    Agree s.wVars (decideQ s (withInputs s.f.m.inputs ρ ι) (withCarried s M κ)) (withExt s ρ (sReq s ρ M ι κ)) := by
  obtain ⟨hin, hqw⟩ := ext_apart s hs
  intro v hvw
  simp only [withExt, sReq]
  by_cases hvi : v ∈ s.f.m.inputs
  · have hvq : v ∉ s.qVars := (hin v hvi).1
    have hl : lookup (fun q => q.1 == v) s.qflags = none := lookup_none (fun q hq => by
      simp only [beq_eq_false_iff_ne]; intro he; exact hvq (by rw [← he]; exact List.mem_map_of_mem hq))
    simp only [SMachine.extVars, List.contains_iff_mem, List.mem_append, hvi, true_or, ite_true, decideQ, hl, withInputs]
  · by_cases hvq : v ∈ s.qVars
    · simp only [SMachine.extVars, List.contains_iff_mem, List.mem_append, hvi, hvq, or_true, true_or, ite_true, false_or, ite_false]
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hvq
      have hl : lookup (fun q' => q'.1 == q.1) s.qflags = some q := lookup_unique (sOk_parts s hs).2.1 hq
      simp only [hl]
    · have hl : lookup (fun q => q.1 == v) s.qflags = none := lookup_none (fun q hq => by
        simp only [beq_eq_false_iff_ne]; intro he; exact hvq (by rw [← he]; exact List.mem_map_of_mem hq))
      simp only [SMachine.extVars, List.contains_iff_mem, List.mem_append, hvi, hvq, hvw, or_false, ite_false, decideQ, hl, withInputs, List.contains_iff_mem]

-- (F2) Every closing hypothesis holds of the real step, read in the goal's view.
theorem closing_true (hs : sOk s = true) (qinsts : List (Nat × E)) :
    ∀ c ∈ closingHyps s qinsts, evalC (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ) c = true := by
  obtain ⟨_, hqd, hwd, hcov, _, hbody, _⟩ := sOk_parts s hs
  obtain ⟨hin, hqw⟩ := ext_apart s hs
  have hag := view_agree s ρ M ι κ hs
  intro c hc
  simp only [closingHyps, List.mem_flatMap, List.mem_append, List.mem_singleton, List.mem_map, List.mem_filter] at hc
  obtain ⟨q, hq, hc⟩ := hc
  have hqv : q.1 ∈ s.qVars := List.mem_map_of_mem hq
  -- The flag's value: 1 exactly when the body holds at every key (read in either view: they agree on the body).
  have hY : withExt s ρ (sReq s ρ M ι κ) q.1 = if ∀ key, holdsC (upd (withInputs s.f.m.inputs ρ ι) q.2.1 key) (withCarried s M κ) q.2.2 then 1 else 0 := by
    rw [← hag q.1 (hqw _ hqv)]; simp only [decideQ, lookup_unique hqd hq]
  have hbodyY : ∀ key, holdsC (upd (withExt s ρ (sReq s ρ M ι κ)) q.2.1 key) (withCarried s M κ) q.2.2
      ↔ holdsC (upd (withInputs s.f.m.inputs ρ ι) q.2.1 key) (withCarried s M κ) q.2.2 := by
    intro key
    rw [← evalC_iff, ← evalC_iff, congrC _ (upd (withInputs s.f.m.inputs ρ ι) q.2.1 key) (withCarried s M κ) q.2.2 (fun j hj => by
      simp only [upd]; split
      · rfl
      · have hjq : j ∉ s.qVars := fun h => avoids_occ (hbody q hq).1 hj (List.mem_append_left _ (List.mem_append_left _ h))
        have hjw : j ∉ s.wVars := fun h => avoids_occ (hbody q hq).1 hj (List.mem_append_left _ (List.mem_append_right _ h))
        rw [← hag j hjw]; simp only [decideQ]
        rw [lookup_none (fun q' hq' => by simp only [beq_eq_false_iff_ne]; intro he; exact hjq (by rw [← he]; exact List.mem_map_of_mem hq'))])]
  rcases hc with ((rfl | ⟨p, ⟨_, hpq⟩, rfl⟩) | hc)
  · simp only [evalC, evalE, hY]; split <;> simp
  · simp only [beq_iff_eq] at hpq
    simp only [evalC, evalE, Bool.or_eq_true, decide_eq_true_eq]
    by_cases h1 : ∀ key, holdsC (upd (withInputs s.f.m.inputs ρ ι) q.2.1 key) (withCarried s M κ) q.2.2
    · right; rw [subst_evalC, applyS_single, evalC_iff]; exact (hbodyY _).mpr (h1 _)
    · left; simp [hY, h1]
  · obtain ⟨w, hw, hwq⟩ := hcov q hq
    have hlw : lookup (fun w' => w'.1 == q.1) s.wits = some w := by
      rw [← hwq]; exact lookup_unique1 (by simp only [distinctPairs, Bool.and_eq_true] at hwd; exact hwd.1) hw
    simp only [hlw, List.mem_singleton] at hc; subst hc
    simp only [evalC, evalE, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    by_cases h1 : ∀ key, holdsC (upd (withInputs s.f.m.inputs ρ ι) q.2.1 key) (withCarried s M κ) q.2.2
    · left; simp [hY, h1]
    · right
      -- The witness reads a failing key.
      have hwv : w.2 ∈ s.wVars := List.mem_map_of_mem hw
      have hYw : withExt s ρ (sReq s ρ M ι κ) w.2 = witnessKey (withInputs s.f.m.inputs ρ ι) (withCarried s M κ) q := by
        have hwi : w.2 ∉ s.f.m.inputs := fun h => (hin _ h).2 hwv
        have hwq' : w.2 ∉ s.qVars := fun h => hqw _ h hwv
        have hext : s.extVars.contains w.2 = true := by
          simp only [SMachine.extVars, List.contains_iff_mem, List.mem_append]; exact Or.inr hwv
        have hni : s.f.m.inputs.contains w.2 = false := by simpa [List.contains_iff_mem] using hwi
        simp only [withExt, hext, ite_true, sReq, hni, Bool.false_eq_true, ite_false]
        rw [lookup_none (fun q' hq' => by
          simp only [beq_eq_false_iff_ne]; intro he; exact hwq' (by rw [← he]; exact List.mem_map_of_mem hq')),
          lookup_unique2 (by simp only [distinctPairs, Bool.and_eq_true] at hwd; exact hwd.2) hw]
        simp only [hwq, lookup_unique hqd hq]
      have hex : ∃ key, ¬ holdsC (upd (withInputs s.f.m.inputs ρ ι) q.2.1 key) (withCarried s M κ) q.2.2 := by simpa using h1
      have hfail : ¬ holdsC (upd (withInputs s.f.m.inputs ρ ι) q.2.1 (witnessKey (withInputs s.f.m.inputs ρ ι) (withCarried s M κ) q)) (withCarried s M κ) q.2.2 := by
        simp only [witnessKey, dif_pos hex]; exact Classical.choose_spec hex
      rw [subst_evalC, applyS_single]
      simp only [evalE, hYw]
      cases hb : evalC (upd (withExt s ρ (sReq s ρ M ι κ)) q.2.1 (witnessKey (withInputs s.f.m.inputs ρ ι) (withCarried s M κ) q)) (withCarried s M κ) q.2.2
      · rfl
      · exact absurd ((hbodyY _).mp ((evalC_iff _ _ _).mp hb)) hfail
end view

/-! Which maps a term reads -/

mutual
def occME (mp : Nat) : E → Bool
  | .var _ => false
  | .const _ => false
  | .add a b => occME mp a || occME mp b
  | .sub a b => occME mp a || occME mp b
  | .mul _ a => occME mp a
  | .min a b => occME mp a || occME mp b
  | .max a b => occME mp a || occME mp b
  | .prod a b => occME mp a || occME mp b
  | .ite c t f => occMC mp c || occME mp t || occME mp f
  | .get m key => m == mp || occME mp key
def occMC (mp : Nat) : C → Bool
  | .le a b => occME mp a || occME mp b
  | .lt a b => occME mp a || occME mp b
  | .eq a b => occME mp a || occME mp b
  | .and a b => occMC mp a || occMC mp b
  | .or a b => occMC mp a || occMC mp b
  | .not a => occMC mp a
end

def avoidsMaps (ms : List Nat) (c : C) : Bool := ms.all fun mp => !occMC mp c
def avoidsMapsE (ms : List Nat) (e : E) : Bool := ms.all fun mp => !occME mp e

-- Maps that agree on every map a term reads give it the same value.
mutual
theorem congrME (ρ : Nat → Nat) (M M' : Nat → Nat → Nat) :
    (e : E) → (∀ mp, occME mp e = true → M mp = M' mp) → evalE ρ M e = evalE ρ M' e
  | .var _, _ => rfl
  | .const _, _ => rfl
  | .add a b, h => by simp only [evalE, congrME ρ M M' a (fun mp hm => h mp (by simp [occME, hm])), congrME ρ M M' b (fun mp hm => h mp (by simp [occME, hm]))]
  | .sub a b, h => by simp only [evalE, congrME ρ M M' a (fun mp hm => h mp (by simp [occME, hm])), congrME ρ M M' b (fun mp hm => h mp (by simp [occME, hm]))]
  | .mul k a, h => by simp only [evalE, congrME ρ M M' a (fun mp hm => h mp (by simp [occME, hm]))]
  | .min a b, h => by simp only [evalE, congrME ρ M M' a (fun mp hm => h mp (by simp [occME, hm])), congrME ρ M M' b (fun mp hm => h mp (by simp [occME, hm]))]
  | .max a b, h => by simp only [evalE, congrME ρ M M' a (fun mp hm => h mp (by simp [occME, hm])), congrME ρ M M' b (fun mp hm => h mp (by simp [occME, hm]))]
  | .prod a b, h => by simp only [evalE, congrME ρ M M' a (fun mp hm => h mp (by simp [occME, hm])), congrME ρ M M' b (fun mp hm => h mp (by simp [occME, hm]))]
  | .ite c t f, h => by
    simp only [evalE, congrMC ρ M M' c (fun mp hm => h mp (by simp [occME, hm])), congrME ρ M M' t (fun mp hm => h mp (by simp [occME, hm])),
      congrME ρ M M' f (fun mp hm => h mp (by simp [occME, hm]))]
  | .get m key, h => by
    simp only [evalE, congrME ρ M M' key (fun mp hm => h mp (by simp [occME, hm])), h m (by simp [occME])]
theorem congrMC (ρ : Nat → Nat) (M M' : Nat → Nat → Nat) :
    (c : C) → (∀ mp, occMC mp c = true → M mp = M' mp) → evalC ρ M c = evalC ρ M' c
  | .le a b, h => by simp only [evalC, congrME ρ M M' a (fun mp hm => h mp (by simp [occMC, hm])), congrME ρ M M' b (fun mp hm => h mp (by simp [occMC, hm]))]
  | .lt a b, h => by simp only [evalC, congrME ρ M M' a (fun mp hm => h mp (by simp [occMC, hm])), congrME ρ M M' b (fun mp hm => h mp (by simp [occMC, hm]))]
  | .eq a b, h => by simp only [evalC, congrME ρ M M' a (fun mp hm => h mp (by simp [occMC, hm])), congrME ρ M M' b (fun mp hm => h mp (by simp [occMC, hm]))]
  | .and a b, h => by simp only [evalC, congrMC ρ M M' a (fun mp hm => h mp (by simp [occMC, hm])), congrMC ρ M M' b (fun mp hm => h mp (by simp [occMC, hm]))]
  | .or a b, h => by simp only [evalC, congrMC ρ M M' a (fun mp hm => h mp (by simp [occMC, hm])), congrMC ρ M M' b (fun mp hm => h mp (by simp [occMC, hm]))]
  | .not a, h => by simp only [evalC, congrMC ρ M M' a (fun mp hm => h mp (by simp [occMC, hm]))]
end

theorem avoidsMapsE_occ {ms : List Nat} {e : E} (h : avoidsMapsE ms e = true) {mp : Nat} (hm : occME mp e = true) : mp ∉ ms := by
  intro hmem; simp only [avoidsMapsE, List.all_eq_true] at h; have := h mp hmem; simp [hm] at this

-- A term avoiding some maps: so does each of its parts.
theorem amE {ms : List Nat} {e a : E} (h : avoidsMapsE ms e = true) (hs : ∀ mp, occME mp a = true → occME mp e = true) : avoidsMapsE ms a = true := by
  simp only [avoidsMapsE, List.all_eq_true, Bool.not_eq_true'] at h ⊢
  intro mp hm; specialize h mp hm; cases hq : occME mp a
  · rfl
  · simp [hs mp hq] at h
theorem amEC {ms : List Nat} {e : E} {c : C} (h : avoidsMapsE ms e = true) (hs : ∀ mp, occMC mp c = true → occME mp e = true) : avoidsMaps ms c = true := by
  simp only [avoidsMapsE, avoidsMaps, List.all_eq_true, Bool.not_eq_true'] at h ⊢
  intro mp hm; specialize h mp hm; cases hq : occMC mp c
  · rfl
  · simp [hs mp hq] at h
theorem amCE {ms : List Nat} {c : C} {a : E} (h : avoidsMaps ms c = true) (hs : ∀ mp, occME mp a = true → occMC mp c = true) : avoidsMapsE ms a = true := by
  simp only [avoidsMapsE, avoidsMaps, List.all_eq_true, Bool.not_eq_true'] at h ⊢
  intro mp hm; specialize h mp hm; cases hq : occME mp a
  · rfl
  · simp [hs mp hq] at h
theorem amC {ms : List Nat} {c d : C} (h : avoidsMaps ms c = true) (hs : ∀ mp, occMC mp d = true → occMC mp c = true) : avoidsMaps ms d = true := by
  simp only [avoidsMaps, List.all_eq_true, Bool.not_eq_true'] at h ⊢
  intro mp hm; specialize h mp hm; cases hq : occMC mp d
  · rfl
  · simp [hs mp hq] at h

-- substR_evalE for a term avoiding the maps rd doesn't read as M' does.
section
variable (σ : List (Nat × E)) (rd : Nat → E → E) (W : Nat → Nat) (M M' : Nat → Nat → Nat) (X : List Nat)
  (hrd : ∀ m k, m ∉ X → evalE W M (rd m k) = M' m (evalE W M k))
include hrd
mutual
theorem substR_evalE_on : (e : E) → avoidsMapsE X e = true → evalE W M (substRE σ rd e) = evalE (applyS σ W M) M' e
  | .var i, _ => by
    simp only [substRE]
    cases h : assoc σ i <;> simp [evalE, applyS, h]
  | .const n, _ => by simp [substRE, evalE]
  | .add a b, h => by simp [substRE, evalE, substR_evalE_on a (amE h (fun mp hm => by simp [occME, hm])), substR_evalE_on b (amE h (fun mp hm => by simp [occME, hm]))]
  | .sub a b, h => by simp [substRE, evalE, substR_evalE_on a (amE h (fun mp hm => by simp [occME, hm])), substR_evalE_on b (amE h (fun mp hm => by simp [occME, hm]))]
  | .mul k a, h => by simp [substRE, evalE, substR_evalE_on a (amE h (fun mp hm => by simp [occME, hm]))]
  | .min a b, h => by simp [substRE, evalE, substR_evalE_on a (amE h (fun mp hm => by simp [occME, hm])), substR_evalE_on b (amE h (fun mp hm => by simp [occME, hm]))]
  | .max a b, h => by simp [substRE, evalE, substR_evalE_on a (amE h (fun mp hm => by simp [occME, hm])), substR_evalE_on b (amE h (fun mp hm => by simp [occME, hm]))]
  | .prod a b, h => by simp [substRE, evalE, substR_evalE_on a (amE h (fun mp hm => by simp [occME, hm])), substR_evalE_on b (amE h (fun mp hm => by simp [occME, hm]))]
  | .ite c t f, h => by
    simp [substRE, evalE, substR_evalC_on c (amEC h (fun mp hm => by simp [occME, hm])), substR_evalE_on t (amE h (fun mp hm => by simp [occME, hm])),
      substR_evalE_on f (amE h (fun mp hm => by simp [occME, hm]))]
  | .get m key, h => by
    have hmz : m ∉ X := avoidsMapsE_occ h (by simp [occME])
    simp only [substRE, evalE]
    rw [hrd m _ hmz, substR_evalE_on key (amE h (fun mp hm => by simp [occME, hm]))]
theorem substR_evalC_on : (c : C) → avoidsMaps X c = true → evalC W M (substRC σ rd c) = evalC (applyS σ W M) M' c
  | .le a b, h => by simp [substRC, evalC, substR_evalE_on a (amCE h (fun mp hm => by simp [occMC, hm])), substR_evalE_on b (amCE h (fun mp hm => by simp [occMC, hm]))]
  | .lt a b, h => by simp [substRC, evalC, substR_evalE_on a (amCE h (fun mp hm => by simp [occMC, hm])), substR_evalE_on b (amCE h (fun mp hm => by simp [occMC, hm]))]
  | .eq a b, h => by simp [substRC, evalC, substR_evalE_on a (amCE h (fun mp hm => by simp [occMC, hm])), substR_evalE_on b (amCE h (fun mp hm => by simp [occMC, hm]))]
  | .and a b, h => by simp [substRC, evalC, substR_evalC_on a (amC h (fun mp hm => by simp [occMC, hm])), substR_evalC_on b (amC h (fun mp hm => by simp [occMC, hm]))]
  | .or a b, h => by simp [substRC, evalC, substR_evalC_on a (amC h (fun mp hm => by simp [occMC, hm])), substR_evalC_on b (amC h (fun mp hm => by simp [occMC, hm]))]
  | .not a, h => by simp [substRC, evalC, substR_evalC_on a (amC h (fun mp hm => by simp [occMC, hm]))]
end
end

theorem substR_var (σ : List (Nat × E)) (rd : Nat → E → E) (W : Nat → Nat) (M : Nat → Nat → Nat) (i : Nat) :
    evalE W M (substRE σ rd (.var i)) = applyS σ W M i := by
  simp only [substRE]; cases h : assoc σ i <;> simp [evalE, applyS, h]

theorem avoidsMaps_occ {ms : List Nat} {c : C} (h : avoidsMaps ms c = true) {mp : Nat} (hm : occMC mp c = true) : mp ∉ ms := by
  intro hin; simp only [avoidsMaps, List.all_eq_true] at h; have := h mp hin; simp [hm] at this

theorem applyS_cons (k : Nat) (t : E) (τ : List (Nat × E)) (W : Nat → Nat) (M : Nat → Nat → Nat) :
    applyS ((k, t) :: τ) W M = upd (applyS τ W M) k (evalE W M t) := by
  funext i; simp only [applyS, assoc, lookup, upd]
  by_cases h : i = k
  · subst h; simp
  · have hb : (k == i) = false := by simp; omega
    simp [hb, h]

-- Setting a variable no flag condition reads commutes with deciding the flags.
theorem decide_upd {fl : List (Nat × C)} {k : Nat} (hk : k ∉ flagVars fl) (hav : ∀ p ∈ fl, occC k p.2 = false)
    (X : Nat → Nat) (N : Nat → Nat → Nat) (v : Nat) : decideFlags fl (upd X k v) N = upd (decideFlags fl X N) k v := by
  funext i
  simp only [decideFlags, applyS, assoc_flagSub, upd]
  by_cases hi : i = k
  · subst hi
    have hn : flagOf fl i = none := by
      simp only [flagOf, Option.map_eq_none_iff]
      exact lookup_none (fun p hp => by
        simp only [beq_eq_false_iff_ne]; intro he
        exact hk (by simp only [flagVars]; rw [← he]; exact List.mem_map_of_mem hp))
    simp [hn]
  · simp only [hi, ite_false]
    cases hc : flagOf fl i with
    | none => simp
    | some c =>
      obtain ⟨p, hp, rfl⟩ := flagOf_some hc
      simp only [Option.map_some, evalE]
      rw [congrC (upd X k v) X N p.2 (fun j hj => by
        simp only [upd]
        split
        · rename_i hjk; subst hjk; have h0 := hav p hp; rw [h0] at hj; exact absurd hj (by decide)
        · rfl)]

/-! Laws read where a frame is read -/

-- The scalar laws and every-key laws at their instances hold wherever the laws do.
theorem laws_hyps_true (laws : List MLaw) (insts : List (Nat × E)) (Y : Nat → Nat) (N : Nat → Nat → Nat)
    (hl : ∀ l ∈ laws, l.Holds Y N) : ∀ c ∈ scalarHyps laws ++ instHyps laws insts, evalC Y N c = true := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · simp only [scalarHyps, List.mem_filterMap] at hc
    obtain ⟨l, hlm, hk⟩ := hc
    split at hk
    · rename_i hkey
      simp only [Option.some.injEq] at hk; subst hk
      have := hl l hlm
      simpa [MLaw.Holds, hkey] using this
    · simp at hk
  · simp only [instHyps, List.mem_filterMap] at hc
    obtain ⟨p, _, hk⟩ := hc
    split at hk
    · rename_i l hlg
      split at hk
      · rename_i kv hkey
        simp only [Option.some.injEq] at hk; subst hk
        have := hl l (List.mem_of_getElem? hlg)
        simp only [MLaw.Holds, hkey] at this
        rw [subst_evalC, applyS_single]
        exact this _
      · simp at hk
    · simp at hk

-- A law reading neither the variables nor the maps two states differ at holds in both alike.
theorem holds_transfer {V MS : List Nat} (l : MLaw) (hv : avoids V l.holds = true) (hm : avoidsMaps MS l.holds = true)
    {ρ ρ' : Nat → Nat} {M M' : Nat → Nat → Nat} (hag : Agree V ρ ρ') (hmag : ∀ mp, mp ∉ MS → M mp = M' mp) :
    l.Holds ρ' M' → l.Holds ρ M := by
  have cong : ∀ X X' : Nat → Nat, Agree V X X' → evalC X' M' l.holds = true → evalC X M l.holds = true := by
    intro X X' ha h
    rw [congrMC X M M' l.holds (fun mp hmp => hmag mp (avoidsMaps_occ hm hmp)), congrC X X' M' l.holds (fun i hi => ha i (avoids_occ hv hi))]
    exact h
  unfold MLaw.Holds
  split
  · exact cong ρ ρ' hag
  · rename_i kv _
    intro h v
    have ha : Agree V (upd ρ kv v) (upd ρ' kv v) := by
      intro i hi; simp only [upd]; split
      · rfl
      · exact hag i hi
    exact cong _ _ ha (h v)

/-! Frames of a run of a machine with sets -/

-- The frame σ, rd denotes the state ρ, M: every variable outside the extended request's and the zone Z, and every map
-- read but those the requests carry and the zone MZ (the names later requests' maps are read by).
def SDenotes (s : SMachine) (Z MZ : List Nat) (W : Nat → Nat) (M0 : Nat → Nat → Nat) (σ : List (Nat × E)) (rd : Nat → E → E)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) : Prop :=
  (∀ v, v ∉ s.extVars → v ∉ Z → applyS σ W M0 v = ρ v) ∧ (∀ mp k, mp ∉ s.carried → mp ∉ MZ → evalE W M0 (rd mp k) = M mp (evalE W M0 k))

-- The frame a step reads (its request set) agrees with the state and request outside the zone, and reads the maps the
-- step reads.
def SHead (s : SMachine) (Z MZ : List Nat) (W : Nat → Nat) (M0 : Nat → Nat → Nat) (σ : List (Nat × E)) (rd : Nat → E → E)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (r mr : List (Nat × Nat)) (ι : Nat → Nat) (κ : Nat → Nat → Nat) : Prop :=
  Agree Z (applyS (frameSub r σ) W M0) (withExt s ρ (sReq s ρ M ι κ))
    ∧ ∀ mp k, mp ∉ MZ → evalE W M0 (frameRd mr rd mp k) = withCarried s M κ mp (evalE W M0 k)

section frame
variable (s : SMachine) (Z MZ : List Nat) (W : Nat → Nat) (M0 : Nat → Nat → Nat)

-- A term of the step read at the frame is its value at the real step (flags decided), away from the zone and witnesses.
theorem sframe_term (hs : sOk s = true) (hfz : ∀ v ∈ flagVars s.f.flags, v ∈ Z) (hfav : ∀ p ∈ s.f.flags, avoids Z p.2 = true)
    {σ : List (Nat × E)} {rd : Nat → E → E} {ρ : Nat → Nat} {M : Nat → Nat → Nat} {r mr : List (Nat × Nat)} {ι : Nat → Nat} {κ : Nat → Nat → Nat}
    (hH : SHead s Z MZ W M0 σ rd ρ M r mr ι κ) (e : E) (he : avoidsE (Z ++ s.wVars) (inlineE s.f.flags e) = true)
    (hem : avoidsMapsE MZ (inlineE s.f.flags e) = true) :
    evalE W M0 (substRE (frameSub r σ) (frameRd mr rd) (inlineE s.f.flags e)) = evalE (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 e := by
  obtain ⟨hX, hrd⟩ := hH
  have hwfl := (sOk_parts s hs).2.2.2.2.2.2
  rw [substR_evalE_on (frameSub r σ) (frameRd mr rd) W M0 (withCarried s M κ) MZ hrd _ hem,
    congrE _ (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ) _ (fun i hi => hX i (fun h => avoidsE_occ he hi (List.mem_append_left _ h))),
    inline_evalE]
  show evalE (decideFlags s.f.flags (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ)) (withCarried s M κ) e
    = evalE (decideFlags s.f.flags (decideQ s (withInputs s.f.m.inputs ρ ι) (withCarried s M κ)) (withCarried s M κ)) (withCarried s M κ) e
  rw [← inline_evalE, ← inline_evalE]
  exact congrE _ _ _ _ (fun i hi => (view_agree s ρ M ι κ hs i (fun h => avoidsE_occ he hi (List.mem_append_right _ h))).symm)
end frame

section frame2
variable (s : SMachine) (Z MZ : List Nat) (W : Nat → Nat) (M0 : Nat → Nat → Nat)

-- Every hypothesis of a frame holds where the frame is read, given the laws and the precondition at its state.
theorem sframe_hyps (hs : sOk s = true) (laws : List MLaw) (insts qinsts : List (Nat × E))
    {σ : List (Nat × E)} {rd : Nat → E → E} {ρ : Nat → Nat} {M : Nat → Nat → Nat} {r mr : List (Nat × Nat)} {ι : Nat → Nat} {κ : Nat → Nat → Nat} {w : C}
    (hlaws : ∀ l ∈ laws, l.Holds ρ M) (hlav : ∀ l ∈ laws, avoids s.extVars l.holds = true ∧ avoidsMaps s.carried l.holds = true)
    (hH : SHead s Z MZ W M0 σ rd ρ M r mr ι κ)
    (hav : ∀ c ∈ sFrameHyps s laws insts qinsts w, avoids Z c = true)
    (havm : ∀ c ∈ sFrameHyps s laws insts qinsts w, avoidsMaps MZ c = true)
    (hA : evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume = true)
    (hW : evalC (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ) w = true) :
    ∀ c ∈ sFrameHyps s laws insts qinsts w, evalC W M0 (substRC (frameSub r σ) (frameRd mr rd) c) = true := by
  obtain ⟨hX, hrd⟩ := hH
  intro c hc
  rw [substR_evalC_on (frameSub r σ) (frameRd mr rd) W M0 (withCarried s M κ) MZ hrd c (havm c hc),
    congrC _ (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ) c (fun i hi => hX i (avoids_occ (hav c hc) hi))]
  -- The laws hold in the goal's view: it agrees with the state outside the request, and reads the state's maps.
  have hlY : ∀ l ∈ laws, l.Holds (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ) := fun l hl =>
    holds_transfer l (hlav l hl).1 (hlav l hl).2 (fun i hi => by simp only [withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hi)])
      (fun mp hmp => by simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmp)]) (hlaws l hl)
  simp only [sFrameHyps, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ((hc | rfl | rfl) | hc)
  · exact laws_hyps_true laws insts _ _ hlY c (List.mem_append.mpr hc)
  · -- The assumption, inlined: the view decides the plain flags as the step does, away from the witnesses.
    rw [inline_evalC]
    have hagD := decide_agree_on (sOk_parts s hs).2.2.2.2.2.2 (withCarried s M κ) (view_agree s ρ M ι κ hs)
    rw [congrC _ (decideFlags s.f.flags (decideQ s (withInputs s.f.m.inputs ρ ι) (withCarried s M κ)) (withCarried s M κ)) _ s.f.m.assume
      (fun i hi => (hagD i (fun h => by
        have hpa : avoids s.wVars s.f.m.assume = true := by simp only [sOk, Bool.and_eq_true] at hs; exact hs.2
        exact avoids_occ hpa hi h)).symm)]
    exact hA
  · exact hW
  · exact closing_true s ρ M ι κ hs qinsts c hc

-- One step keeps the frame denoting the state: each variable its step term, each map its writes.
theorem sstep_denotes (hs : sOk s = true) (hfz : ∀ v ∈ flagVars s.f.flags, v ∈ Z) (hfav : ∀ p ∈ s.f.flags, avoids Z p.2 = true)
    {σ : List (Nat × E)} {rd : Nat → E → E} {ρ : Nat → Nat} {M : Nat → Nat → Nat} (r mr : List (Nat × Nat)) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (hD : SDenotes s Z MZ W M0 σ rd ρ M) (hH : SHead s Z MZ W M0 σ rd ρ M r mr ι κ)
    (hrk : ∀ p ∈ r, p.1 ∈ s.extVars)
    (hst : ∀ p ∈ s.f.m.step, avoidsE (Z ++ s.wVars) (inlineE s.f.flags p.2) = true)
    (hwr : ∀ w ∈ s.f.m.writes, avoidsE (Z ++ s.wVars) (inlineE s.f.flags w.2.1) = true ∧ avoidsE (Z ++ s.wVars) (inlineE s.f.flags w.2.2) = true)
    (hev : ∀ w ∈ s.every, avoidsE (Z ++ s.wVars) (inlineE s.f.flags w.2.2) = true ∧ w.2.1 ∉ Z ∧ w.2.1 ∉ flagVars s.f.flags
      ∧ (∀ p ∈ s.f.flags, occC w.2.1 p.2 = false) ∧ w.1 ∉ s.carried ∧ w.1 ∉ s.f.m.writes.map (·.1))
    (hstm : ∀ p ∈ s.f.m.step, avoidsMapsE MZ (inlineE s.f.flags p.2) = true)
    (hwrm : ∀ w ∈ s.f.m.writes, avoidsMapsE MZ (inlineE s.f.flags w.2.1) = true ∧ avoidsMapsE MZ (inlineE s.f.flags w.2.2) = true)
    (hevm : ∀ w ∈ s.every, avoidsMapsE MZ (inlineE s.f.flags w.2.2) = true) :
    SDenotes s Z MZ W M0 (stepSub s.f (frameSub r σ) (frameRd mr rd)) (stepRdS s (frameSub r σ) (frameRd mr rd)) (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2 := by
  obtain ⟨hv, hrdM⟩ := hD
  have hH' := hH
  obtain ⟨hX, hrd⟩ := hH
  refine ⟨fun v hve hvz => ?_, fun mp k hmp hmz => ?_⟩
  · simp only [sNext, applyS, stepSub, assoc_append_or, assoc_stepSub]
    cases h : assoc s.f.m.step v with
    | some e =>
      have hm : (v, e) ∈ s.f.m.step := by
        simp only [assoc, Option.map_eq_some_iff] at h
        obtain ⟨q, hq, rfl⟩ := h
        obtain ⟨hqm, hqv⟩ := lookup_some hq
        simp only [beq_iff_eq] at hqv
        rw [← hqv]; exact hqm
      simp only [Option.map_some, Option.some_or]
      exact sframe_term s Z MZ W M0 hs hfz hfav hH' e (hst (v, e) hm) (hstm (v, e) hm)
    | none =>
      simp only [Option.map_none, Option.none_or]
      have hvf : v ∉ flagVars s.f.flags := fun h' => hvz (hfz v h')
      have hvq : v ∉ s.qVars := fun h' => hve (by simp only [SMachine.extVars, List.mem_append]; exact Or.inl (Or.inr h'))
      have hvi : v ∉ s.f.m.inputs := fun h' => hve (by simp only [SMachine.extVars, List.mem_append]; exact Or.inl (Or.inl h'))
      show applyS (frameSub r σ) W M0 v = decideFlags s.f.flags (decideQ s (withInputs s.f.m.inputs ρ ι) (withCarried s M κ)) (withCarried s M κ) v
      rw [decide_other hvf, hX v hvz]
      simp only [withExt, decideQ, sReq]
      rw [if_neg (by simpa [List.contains_iff_mem] using hve)]
      rw [lookup_none (fun q hq => by simp only [beq_eq_false_iff_ne]; intro he; exact hvq (by rw [← he]; exact List.mem_map_of_mem hq))]
      exact (withInputs_other hvi ρ ι).symm
  · simp only [stepRdS, sNext, everyMaps]
    cases he : lookup (fun w => w.1 == mp) s.every with
    | some w =>
      obtain ⟨hval, _, hkf, hkfl, _, _⟩ := hev w (lookup_some he).1
      simp only
      rw [substR_evalE_on ((w.2.1, k) :: frameSub r σ) (frameRd mr rd) W M0 (withCarried s M κ) MZ hrd _ (hevm w (lookup_some he).1), applyS_cons]
      show evalE (upd (applyS (frameSub r σ) W M0) w.2.1 (evalE W M0 k)) (withCarried s M κ) (inlineE s.f.flags w.2.2)
        = evalE (upd (decideFlags s.f.flags (decideQ s (withInputs s.f.m.inputs ρ ι) (withCarried s M κ)) (withCarried s M κ)) w.2.1 (evalE W M0 k)) (withCarried s M κ) w.2.2
      rw [← decide_upd hkf (fun p hp => hkfl p hp), ← inline_evalE]
      -- The frame and the step read the inlined value alike: they agree away from the zone and the witnesses.
      exact congrE _ _ _ _ (fun i hi => by
        simp only [upd]; split
        · rfl
        · have hiz : i ∉ Z := fun h => avoidsE_occ hval hi (List.mem_append_left _ h)
          have hiw : i ∉ s.wVars := fun h => avoidsE_occ hval hi (List.mem_append_right _ h)
          rw [hX i hiz]; exact (view_agree s ρ M ι κ hs i hiw).symm)
    | none =>
      simp only [stepRd, writeMaps]
      cases hw : lookup (fun w : Nat × E × E => w.1 == mp) s.f.m.writes with
      | none => exact hrd mp k hmz
      | some w =>
        have hm := (lookup_some hw).1
        simp only [evalE, evalC, sframe_term s Z MZ W M0 hs hfz hfav hH' w.2.1 (hwr w hm).1 (hwrm w hm).1,
          sframe_term s Z MZ W M0 hs hfz hfav hH' w.2.2 (hwr w hm).2 (hwrm w hm).2, fun k => hrd mp k hmz]
        simp only [sView]
        by_cases hk : evalE W M0 k = evalE (decideFlags s.f.flags (decideQ s (withInputs s.f.m.inputs ρ ι) (withCarried s M κ)) (withCarried s M κ)) (withCarried s M κ) w.2.1 <;> simp [hk]
end frame2

/-! Laws: the induction rule for machines with sets -/

structure SEntry where
  law : MLaw
  sk : Nat                    -- the skolem variable
  insts : List (Nat × E)      -- (law index, key): where the step goal assumes the laws about every key
  qinsts : List (Nat × E)     -- (quantified flag, key): where the step goal closes it
  start : List VDef × Tree
  step : List VDef × Tree

def trueC : C := .le (.const 0) (.const 0)
def sStartGoal (s : SMachine) (e : SEntry) : List C := [s.f.m.pre, .not (substRC s.f.m.init (rdStart s.f.m) (goalOf e.law e.sk))]
def sStepGoal (s : SMachine) (laws : List MLaw) (e : SEntry) : List C :=
  [s.f.m.pre] ++ (sFrameHyps s laws e.insts e.qinsts trueC).map (substRC (frameSub [] []) (frameRd [] getRd))
    ++ [.not (substRC (stepSub s.f (frameSub [] []) (frameRd [] getRd)) (stepRdS s (frameSub [] []) (frameRd [] getRd)) (goalOf e.law e.sk))]

-- The machine's terms and the zone a frame keeps apart (the flags, and here the skolem).
def sTermsOk (s : SMachine) (Z : List Nat) : Bool :=
  s.f.flags.all (fun p => avoids Z p.2)
    && s.f.m.step.all (fun p => avoidsE (Z ++ s.wVars) (inlineE s.f.flags p.2))
    && s.f.m.writes.all (fun w => avoidsE (Z ++ s.wVars) (inlineE s.f.flags w.2.1) && avoidsE (Z ++ s.wVars) (inlineE s.f.flags w.2.2) && !s.carried.contains w.1)
    && s.every.all (fun w => avoidsE (Z ++ s.wVars) (inlineE s.f.flags w.2.2) && !Z.contains w.2.1 && !(flagVars s.f.flags).contains w.2.1
        && s.f.flags.all (fun p => !occC w.2.1 p.2) && !s.carried.contains w.1 && !(s.f.m.writes.map (·.1)).contains w.1)

-- The skolem is fresh for the machine: no flag, body, assumption, term or write reads it, nor binds it.
def skFresh (s : SMachine) (sk : Nat) : Bool :=
  s.f.flags.all (fun p => !occC sk p.2) && s.qflags.all (fun q => !occC sk q.2.2) && !occC sk s.f.m.assume
    && s.f.m.step.all (fun p => !occE sk p.2) && s.f.m.writes.all (fun w => !occE sk w.2.1 && !occE sk w.2.2)
    && s.every.all (fun w => !occE sk w.2.2 && w.2.1 != sk)

def checkSMachine (s : SMachine) (ps : List SEntry) : Bool :=
  sOk s && avoids (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)) s.f.m.pre && !readsC s.f.m.pre
    && sTermsOk s (flagVars s.f.flags)
    && ps.all fun e =>
      avoids (s.extVars ++ flagVars s.f.flags) e.law.holds && avoidsMaps s.carried e.law.holds
        && !(s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains e.sk
        && ps.all (fun e' => !occC e.sk e'.law.holds) && !occC e.sk s.f.m.pre && s.f.m.init.all (fun p => !occE e.sk p.2)
        && skFresh s e.sk
        && checkGoal ⟨e.start.1, sStartGoal s e⟩ e.start.2
        && checkGoal ⟨e.step.1, sStepGoal s (ps.map (·.law)) e⟩ e.step.2

theorem skFresh_parts {s : SMachine} {sk : Nat} (h : skFresh s sk = true) :
    (∀ p ∈ s.f.flags, occC sk p.2 = false) ∧ (∀ q ∈ s.qflags, occC sk q.2.2 = false) ∧ occC sk s.f.m.assume = false
      ∧ (∀ p ∈ s.f.m.step, occE sk p.2 = false) ∧ (∀ w ∈ s.f.m.writes, occE sk w.2.1 = false ∧ occE sk w.2.2 = false)
      ∧ (∀ w ∈ s.every, occE sk w.2.2 = false ∧ w.2.1 ≠ sk) := by
  simp only [skFresh, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-! A variable no step reads or writes: setting it commutes with a step -/

theorem withInputs_upd {ins : List Nat} {x : Nat} (hx : x ∉ ins) (ρ ι : Nat → Nat) (v : Nat) :
    withInputs ins (upd ρ x v) ι = upd (withInputs ins ρ ι) x v := by
  funext i
  simp only [withInputs, upd]
  by_cases hi : i = x
  · subst hi; simp [List.contains_iff_mem, hx]
  · simp [hi]

theorem decideQ_upd {s : SMachine} {x : Nat} (hq : x ∉ s.qVars) (hb : ∀ q ∈ s.qflags, occC x q.2.2 = false)
    (X : Nat → Nat) (N : Nat → Nat → Nat) (v : Nat) : decideQ s (upd X x v) N = upd (decideQ s X N) x v := by
  funext u
  by_cases hux : u = x
  · subst hux
    have hl : lookup (fun q => q.1 == u) s.qflags = none := lookup_none (fun q hq' => by
      simp only [beq_eq_false_iff_ne]; intro he; exact hq (by rw [← he]; exact List.mem_map_of_mem hq'))
    simp only [decideQ, hl, upd, ite_true]
  · simp only [upd, hux, ite_false]
    simp only [decideQ]
    cases hl : lookup (fun q => q.1 == u) s.qflags with
    | none => simp [upd, hux]
    | some q =>
      have hbq := hb q (lookup_some hl).1
      have hiff : ∀ key, holdsC (upd (upd X x v) q.2.1 key) N q.2.2 ↔ holdsC (upd X q.2.1 key) N q.2.2 := fun key => by
        rw [← evalC_iff, ← evalC_iff, congrC _ (upd X q.2.1 key) N q.2.2 (fun i hi => by
          have hix : i ≠ x := fun h => by rw [h, hbq] at hi; cases hi
          simp only [upd]
          by_cases hik : i = q.2.1
          · simp [hik]
          · simp [hik, hix])]
      simp only [hiff]

theorem sView_upd {s : SMachine} {x : Nat} (hxi : x ∉ s.f.m.inputs) (hxq : x ∉ s.qVars) (hxf : x ∉ flagVars s.f.flags)
    (hb : ∀ q ∈ s.qflags, occC x q.2.2 = false) (hfl : ∀ p ∈ s.f.flags, occC x p.2 = false)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) (v : Nat) :
    sView s (upd ρ x v) M ι κ = (upd (sView s ρ M ι κ).1 x v, (sView s ρ M ι κ).2) := by
  simp only [sView, withInputs_upd hxi, decideQ_upd hxq hb, decide_upd hxf hfl]

theorem sNext_upd {s : SMachine} {x : Nat} (hxi : x ∉ s.f.m.inputs) (hxq : x ∉ s.qVars) (hxf : x ∉ flagVars s.f.flags)
    (hb : ∀ q ∈ s.qflags, occC x q.2.2 = false) (hfl : ∀ p ∈ s.f.flags, occC x p.2 = false)
    (hxs : x ∉ s.f.m.step.map (·.1)) (hst : ∀ p ∈ s.f.m.step, occE x p.2 = false)
    (hwr : ∀ w ∈ s.f.m.writes, occE x w.2.1 = false ∧ occE x w.2.2 = false) (hev : ∀ w ∈ s.every, occE x w.2.2 = false ∧ w.2.1 ≠ x)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) (v : Nat) :
    sNext s (upd ρ x v) M ι κ = (upd (sNext s ρ M ι κ).1 x v, (sNext s ρ M ι κ).2) := by
  simp only [sNext, sView_upd hxi hxq hxf hb hfl]
  rw [applyS_upd hxs (by simpa [List.all_eq_true] using hst)]
  congr 1
  funext mp key
  simp only [everyMaps]
  cases he : lookup (fun w => w.1 == mp) s.every with
  | some w =>
    obtain ⟨hv, hk⟩ := hev w (lookup_some he).1
    exact congrE _ _ _ _ (fun i hi => by
      have hix : i ≠ x := fun h => by rw [h, hv] at hi; cases hi
      simp only [upd]
      by_cases h1 : i = w.2.1
      · simp [h1]
      · simp [h1, hix])
  | none =>
    simp only [writeMaps]
    cases hw : lookup (fun w : Nat × E × E => w.1 == mp) s.f.m.writes with
    | none => rfl
    | some w =>
      obtain ⟨h1, h2⟩ := hwr w (lookup_some hw).1
      have e1 : evalE (upd (sView s ρ M ι κ).1 x v) (sView s ρ M ι κ).2 w.2.1 = evalE (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 w.2.1 :=
        congrE _ _ _ _ (fun i hi => by have hix : i ≠ x := (fun h => by rw [h, h1] at hi; cases hi); simp [upd, hix])
      have e2 : evalE (upd (sView s ρ M ι κ).1 x v) (sView s ρ M ι κ).2 w.2.2 = evalE (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 w.2.2 :=
        congrE _ _ _ _ (fun i hi => by have hix : i ≠ x := (fun h => by rw [h, h2] at hi; cases hi); simp [upd, hix])
      simp only [e1, e2]

theorem sTermsOk_parts {s : SMachine} {Z : List Nat} (h : sTermsOk s Z = true) :
    (∀ p ∈ s.f.flags, avoids Z p.2 = true)
      ∧ (∀ p ∈ s.f.m.step, avoidsE (Z ++ s.wVars) (inlineE s.f.flags p.2) = true)
      ∧ (∀ w ∈ s.f.m.writes, (avoidsE (Z ++ s.wVars) (inlineE s.f.flags w.2.1) = true ∧ avoidsE (Z ++ s.wVars) (inlineE s.f.flags w.2.2) = true) ∧ w.1 ∉ s.carried)
      ∧ (∀ w ∈ s.every, avoidsE (Z ++ s.wVars) (inlineE s.f.flags w.2.2) = true ∧ w.2.1 ∉ Z ∧ w.2.1 ∉ flagVars s.f.flags
          ∧ (∀ p ∈ s.f.flags, occC w.2.1 p.2 = false) ∧ w.1 ∉ s.carried ∧ w.1 ∉ s.f.m.writes.map (·.1)) := by
  simp only [sTermsOk, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hf, hst⟩, hwr⟩, hev⟩ := h
  refine ⟨hf, hst, fun w hw => ⟨⟨(hwr w hw).1.1, (hwr w hw).1.2⟩, by simpa using (hwr w hw).2⟩, fun w hw => ?_⟩
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hev w hw
  exact ⟨h1, by simpa using h2, by simpa using h3, fun p hp => by simpa using h4 p hp, by simpa using h5, by simpa using h6⟩

-- The precondition holds in every reachable state: it reads the params alone.
theorem pre_sreach (s : SMachine) (hp : avoids (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)) s.f.m.pre = true)
    (hr : readsC s.f.m.pre = false) : ∀ {ρ M}, SReach s ρ M → evalC ρ M s.f.m.pre = true := by
  intro ρ M h
  induction h with
  | start ρ M _ h0 =>
    rw [evalC_avoids hp M (ρ' := ρ) (fun i hi => applyS_other (fun h => hi (by simp [h])) ρ M)]; exact h0
  | step ρ M ι κ _ _ ih =>
    rw [noReadsC _ _ M s.f.m.pre hr]
    rw [evalC_avoids hp M (ρ' := ρ) (fun i hi => by
      simp only [sNext, sView]
      rw [applyS_other (fun h => hi (by simp [h])), decide_other (fun h => hi (by simp [h]))]
      simp only [decideQ]
      rw [lookup_none (fun q hq => by
        simp only [beq_eq_false_iff_ne]; intro he
        exact hi (by simp only [SMachine.extVars, SMachine.qVars, List.mem_append, List.mem_map]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, he⟩))))))]
      exact withInputs_other (fun h => hi (by simp only [SMachine.extVars, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))) ρ ι)]
    exact ih

-- Two environments that agree on what a law reads and at the skolem read its goal alike.
theorem goalOf_agree (l : MLaw) (sk : Nat) (N : Nat → Nat → Nat) {X X' : Nat → Nat} (hsk : X sk = X' sk)
    (h : ∀ i, occC i l.holds = true → X i = X' i) : evalC X N (goalOf l sk) = evalC X' N (goalOf l sk) := by
  unfold goalOf
  split
  · exact congrC _ _ N _ h
  · rename_i kv _
    rw [subst_evalC, subst_evalC, applyS_single, applyS_single]
    exact congrC _ _ N _ (fun i hi => by
      simp only [upd, evalE]; split
      · exact hsk
      · exact h i hi)

/-- The induction rule with sets: for params that meet the precondition and maps that start as declared, every law of
an accepted proof holds in every reachable state, whatever maps each request carries. -/
theorem smachine_sound (s : SMachine) (ps : List SEntry) (h : checkSMachine s ps = true) :
    ∀ ρ M, SReach s ρ M → ∀ e ∈ ps, e.law.Holds ρ M := by
  simp only [checkSMachine, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hs, hpre⟩, hrp⟩, hterms⟩, h⟩ := h
  obtain ⟨hfav, hstp, hwr, hev⟩ := sTermsOk_parts hterms
  intro ρ M hr
  induction hr with
  | start ρ M hM h0 =>
    intro e he
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hfresh⟩, hslaw⟩, hspre⟩, hsinit⟩, _⟩, hst⟩, _⟩ := h e he
    refine goalOf_holds e.law (hslaw e he) _ M (fun v => ?_)
    apply Decidable.byContradiction; intro hn
    apply sound _ _ hst (upd ρ e.sk v) M
    intro c hc
    simp only [sStartGoal, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rw [congrC _ ρ M s.f.m.pre (fun i hi => by
        simp only [upd]; split
        · rename_i hik; subst hik; simp [hspre] at hi
        · rfl)]
      exact h0
    · have hrd : ∀ mp k, evalE (upd ρ e.sk v) M (rdStart s.f.m mp k) = M mp (evalE (upd ρ e.sk v) M k) := by
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
  | step ρ M ι κ hr ha ih =>
    intro e he
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hlx, hlm⟩, hfresh⟩, hslaw⟩, hspre⟩, _⟩, hskf⟩, _⟩, hst⟩ := h e he
    obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6⟩ := skFresh_parts hskf
    have hnot : e.sk ∉ s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1) := fun hm => by
      rw [List.contains_iff_mem.mpr hm] at hfresh; cases hfresh
    have hskE : e.sk ∉ s.extVars := fun hm => hnot (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hm)))
    have hskF : e.sk ∉ flagVars s.f.flags := fun hm => hnot (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hm)))
    have hskS : e.sk ∉ s.f.m.step.map (·.1) := fun hm => hnot (List.mem_append_right _ hm)
    have hski : e.sk ∉ s.f.m.inputs := fun hm => hskE (by simp only [SMachine.extVars, List.mem_append]; exact Or.inl (Or.inl hm))
    have hskq : e.sk ∉ s.qVars := fun hm => hskE (by simp only [SMachine.extVars, List.mem_append]; exact Or.inl (Or.inr hm))
    have hlav : ∀ l ∈ ps.map (·.law), avoids s.extVars l.holds = true ∧ avoidsMaps s.carried l.holds = true := by
      intro l hl
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp hl
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h e' he'
      refine ⟨?_, h2⟩
      simp only [avoids, List.all_append, Bool.and_eq_true] at h1 ⊢; exact h1.1
    -- The law at the next state with the carried maps in place reads as at the next state: it reads none of them.
    refine holds_transfer (V := []) (MS := s.carried) (ρ' := (sNext s ρ M ι κ).1) (M' := withCarried s (sNext s ρ M ι κ).2 κ) e.law (by simp [avoids]) hlm (fun i _ => rfl)
      (fun mp hmp => by simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmp)]) ?_
    refine goalOf_holds e.law (hslaw e he) _ _ (fun v => ?_)
    apply Decidable.byContradiction; intro hn
    -- The frame runs from the state with the skolem set to v: the machine reads it nowhere, so the step is the same.
    have hNext := sNext_upd hski hskq hskF hf2 hf1 hskS hf4 hf5 hf6 ρ M ι κ v
    have hView := sView_upd hski hskq hskF hf2 hf1 ρ M ι κ v
    let W := withExt s (upd ρ e.sk v) (sReq s (upd ρ e.sk v) M ι κ)
    let M0 := withCarried s M κ
    have hH : ∀ Z, SHead s Z [] W M0 [] getRd (upd ρ e.sk v) M [] [] ι κ := fun Z => by
      refine ⟨fun i _ => ?_, fun mp k _ => ?_⟩
      · show applyS (frameSub [] []) W M0 i = W i
        simp only [frameSub, List.map_nil, List.append_nil, applyS_nil']
      · simp [frameRd, getRd, lookup, evalE, M0]
    have hD : SDenotes s (flagVars s.f.flags) [] W M0 [] getRd (upd ρ e.sk v) M := by
      refine ⟨fun i hie _ => ?_, fun mp k hmp _ => ?_⟩
      · rw [applyS_nil']; simp only [W, withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hie)]
      · simp only [getRd, evalE, M0, withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmp)]
    have hD' := sstep_denotes s (flagVars s.f.flags) [] W M0 hs (fun v hv => hv) hfav [] [] ι κ hD (hH _) (fun p hp => by simp at hp)
      hstp (fun w hw => (hwr w hw).1) hev (fun _ _ => by simp [avoidsMapsE]) (fun _ _ => by simp [avoidsMapsE]) (fun _ _ => by simp [avoidsMapsE])
    apply sound _ _ hst W M0
    intro c hc
    simp only [sStepGoal, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, List.mem_map] at hc
    rcases hc with (rfl | ⟨c', hc', rfl⟩) | rfl
    · -- The precondition: it reads no map, no request and not the skolem.
      rw [noReadsC W M0 M s.f.m.pre hrp, congrC W ρ M s.f.m.pre (fun i hi => ?_)]
      · exact pre_sreach s hpre hrp hr
      · have hi1 := avoids_occ hpre hi
        have hik : i ≠ e.sk := fun h' => by rw [h'] at hi; simp [hspre] at hi
        simp only [W, withExt]
        rw [if_neg (fun h' => hi1 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.contains_iff_mem.mp h')))))]
        simp only [upd, if_neg hik]
    · -- The laws hold at the state with the skolem set (they don't read it); the assumption reads it nowhere either.
      have hA : evalC (sView s (upd ρ e.sk v) M ι κ).1 (sView s (upd ρ e.sk v) M ι κ).2 s.f.m.assume = true := by
        rw [hView]; dsimp only
        rw [congrC _ (sView s ρ M ι κ).1 _ _ (fun i hi => by
          have hik : i ≠ e.sk := fun h' => by rw [h', hf3] at hi; cases hi
          simp only [upd, if_neg hik])]
        exact ha
      exact sframe_hyps s [] [] W M0 hs (ps.map (·.law)) e.insts e.qinsts
        (fun l hl => by
          obtain ⟨e', he', rfl⟩ := List.mem_map.mp hl
          exact holds_transfer (V := [e.sk]) (MS := []) e'.law (by simp [avoids, hslaw e' he']) (by simp [avoidsMaps])
            (fun i hi => by simp only [upd]; rw [if_neg (by simpa using hi)]) (fun _ _ => rfl) (ih e' he'))
        hlav (hH []) (fun _ _ => by simp [avoids]) (fun _ _ => by simp [avoidsMaps]) hA (by simp [trueC, evalC, evalE]) c' hc'
    · -- The goal, read across the step: the maps a request carries read as carried, the rest as the step leaves them.
      have hrd' : ∀ mp k, evalE W M0 (stepRdS s (frameSub [] []) (frameRd [] getRd) mp k) = withCarried s (sNext s ρ M ι κ).2 κ mp (evalE W M0 k) := by
        intro mp k
        by_cases hmp : mp ∈ s.carried
        · have hne : lookup (fun w => w.1 == mp) s.every = none := lookup_none (fun w hw => by
            simp only [beq_eq_false_iff_ne]; intro h'; exact (hev w hw).2.2.2.2.1 (by rw [h']; exact hmp))
          have hnw : lookup (fun w : Nat × E × E => w.1 == mp) s.f.m.writes = none := lookup_none (fun w hw => by
            simp only [beq_eq_false_iff_ne]; intro h'; exact (hwr w hw).2 (by rw [h']; exact hmp))
          simp only [stepRdS, hne, stepRd, hnw]
          simp [frameRd, getRd, lookup, evalE, M0, withCarried, List.contains_iff_mem, hmp]
        · rw [hD'.2 mp k hmp (by simp), hNext]; simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmp)]
      simp only [evalC]
      rw [substR_evalC _ _ W M0 _ hrd', goalOf_agree e.law e.sk _ (X' := upd (sNext s ρ M ι κ).1 e.sk v)
        (by rw [hD'.1 e.sk hskE hskF, hNext]) (fun i hi => ?_)]
      · simpa using hn
      · have hi1 := avoids_occ hlx hi
        rw [hD'.1 i (fun h' => hi1 (List.mem_append_left _ h')) (fun h' => hi1 (List.mem_append_right _ h')), hNext]

/-! k-step laws over sets -/

structure SKStep where
  k : KStep                        -- whens (flags inlined), then, ren (each later step: every extended request variable), primes, insts, proof
  mren : List (List (Nat × Nat))   -- per step: (carried map, the name the goal reads it by there); [] for the first step
  qinsts : List (Nat × E)          -- (quantified flag, key): where each frame closes it

def sKOut (s : SMachine) (laws : List MLaw) (sl : SKStep) := sRun s laws sl.k.insts sl.qinsts sl.k.whens sl.k.ren sl.mren [] getRd
def sKGoal (s : SMachine) (laws : List MLaw) (sl : SKStep) : List C :=
  [s.f.m.pre] ++ (sKOut s laws sl).1
    ++ [.not (substRC (kEndSub sl.k (sKOut s laws sl).2.1 (sKOut s laws sl).2.2) (kEndRd sl.k (sKOut s laws sl).2.2) sl.k.then_)]

-- The step's terms, flags inlined, read none of the names later requests' maps are read by.
def sMapsOk (s : SMachine) (MZ : List Nat) : Bool :=
  s.f.m.step.all (fun p => avoidsMapsE MZ (inlineE s.f.flags p.2))
    && s.f.m.writes.all (fun w => avoidsMapsE MZ (inlineE s.f.flags w.2.1) && avoidsMapsE MZ (inlineE s.f.flags w.2.2))
    && s.every.all (fun w => avoidsMapsE MZ (inlineE s.f.flags w.2.2))

def szone (s : SMachine) (sl : SKStep) : List Nat := tgts sl.k.ren ++ flagVars s.f.flags

def checkSKStep (s : SMachine) (ps : List SEntry) (sl : SKStep) : Bool :=
  sl.k.whens.length == sl.k.ren.length && sl.mren.length == sl.k.ren.length && sl.k.ren.head? == some [] && sl.mren.head? == some []
    && distinct (tgts sl.k.ren) && distinct (tgts sl.mren)
    && sl.k.ren.all (fun r => r.all fun p => s.extVars.contains p.1)
    && sl.k.ren.tail.all (fun r => s.extVars.all fun i => r.any (·.1 == i))
    && sl.mren.all (fun r => r.all fun p => s.carried.contains p.1)
    && sl.mren.tail.all (fun r => s.carried.all fun mp => r.any (·.1 == mp))
    && sl.k.prime.all (fun q => !s.extVars.contains q.1 && !(szone s sl).contains q.1)
    && sl.k.primeMaps.all (fun q => !s.carried.contains q.1 && !(tgts sl.mren).contains q.1)
    && avoids (szone s sl) s.f.m.pre
    && sl.k.whens.all (fun w => (sFrameHyps s (ps.map (·.law)) sl.k.insts sl.qinsts w).all fun c => avoids (szone s sl) c && avoidsMaps (tgts sl.mren) c)
    && sTermsOk s (szone s sl) && sMapsOk s (tgts sl.mren)
    && checkGoal ⟨sl.k.proof.1, sKGoal s (ps.map (·.law)) sl⟩ sl.k.proof.2

/-! What a k-step law over sets claims -/

abbrev SRequest := (Nat → Nat) × (Nat → Nat → Nat)   -- a request's inputs, and the maps it carries

noncomputable def sEnd (s : SMachine) : (Nat → Nat) → (Nat → Nat → Nat) → List SRequest → (Nat → Nat) × (Nat → Nat → Nat)
  | ρ, M, [] => (ρ, M)
  | ρ, M, q :: qs => sEnd s (sNext s ρ M q.1 q.2).1 (sNext s ρ M q.1 q.2).2 qs

-- Each step's extended request (inputs, quantified flags, witnesses), as its goal reads it.
noncomputable def sExts (s : SMachine) : (Nat → Nat) → (Nat → Nat → Nat) → List SRequest → List (Nat → Nat)
  | _, _, [] => []
  | ρ, M, q :: qs => sReq s ρ M q.1 q.2 :: sExts s (sNext s ρ M q.1 q.2).1 (sNext s ρ M q.1 q.2).2 qs

-- Each request allowed (the assumption, flags decided) and meeting its step's `when`.
def SAllowed (s : SMachine) : List C → (Nat → Nat) → (Nat → Nat → Nat) → List SRequest → Prop
  | w :: ws, ρ, M, q :: qs =>
    evalC (sView s ρ M q.1 q.2).1 (sView s ρ M q.1 q.2).2 s.f.m.assume = true
      ∧ evalC (withExt s ρ (sReq s ρ M q.1 q.2)) (withCarried s M q.2) w = true
      ∧ SAllowed s ws (sNext s ρ M q.1 q.2).1 (sNext s ρ M q.1 q.2).2 qs
  | _, _, _, _ => True

/-- A k-step law over sets: from every reachable state, every k requests in a row the machine allows end in a state
where `then` holds: primed names read the last state and maps, plain names the first state with the first request,
each later request read by its fresh variables and the maps it carries by their fresh names. -/
def SKStepHolds (s : SMachine) (sl : SKStep) : Prop :=
  ∀ ρ M, SReach s ρ M → ∀ q₁ qs, qs.length + 1 = sl.k.whens.length → SAllowed s sl.k.whens ρ M (q₁ :: qs) →
    evalC (primed sl.k.prime (sEnd s ρ M (q₁ :: qs)).1 (renEnv sl.k.ren (sExts s ρ M (q₁ :: qs)) (withExt s ρ (sReq s ρ M q₁.1 q₁.2))))
      (primedMaps sl.k.primeMaps (sEnd s ρ M (q₁ :: qs)).2 (renMaps sl.mren ((q₁ :: qs).map (·.2)) (withCarried s M q₁.2))) sl.k.then_ = true

/-! The proof -/

theorem sOk_of {s : SMachine} {ps : List SEntry} (hl : checkSMachine s ps = true) : sOk s = true := by
  simp only [checkSMachine, Bool.and_eq_true] at hl; exact hl.1.1.1.1

theorem spre_parts {s : SMachine} {ps : List SEntry} (hl : checkSMachine s ps = true) :
    avoids (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)) s.f.m.pre = true ∧ readsC s.f.m.pre = false := by
  simp only [checkSMachine, Bool.and_eq_true] at hl; exact ⟨hl.1.1.1.2, by simpa using hl.1.1.2⟩

theorem slaws_avoid {s : SMachine} {ps : List SEntry} (hl : checkSMachine s ps = true) :
    ∀ l ∈ ps.map (·.law), avoids s.extVars l.holds = true ∧ avoidsMaps s.carried l.holds = true := by
  simp only [checkSMachine, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hl
  intro l hl'
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp hl'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hl.2 e' he'
  refine ⟨?_, h2⟩
  simp only [avoids, List.all_append, Bool.and_eq_true] at h1 ⊢; exact h1.1

theorem sMapsOk_parts {s : SMachine} {MZ : List Nat} (h : sMapsOk s MZ = true) :
    (∀ p ∈ s.f.m.step, avoidsMapsE MZ (inlineE s.f.flags p.2) = true)
      ∧ (∀ w ∈ s.f.m.writes, avoidsMapsE MZ (inlineE s.f.flags w.2.1) = true ∧ avoidsMapsE MZ (inlineE s.f.flags w.2.2) = true)
      ∧ (∀ w ∈ s.every, avoidsMapsE MZ (inlineE s.f.flags w.2.2) = true) := by
  simp only [sMapsOk, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem renMaps_other : ∀ (rs : List (List (Nat × Nat))) (κs : List (Nat → Nat → Nat)) (b : Nat → Nat → Nat) (mp : Nat),
    mp ∉ tgts rs → renMaps rs κs b mp = b mp
  | [], κs, b, mp, _ => by cases κs <;> rfl
  | r :: rs, [], b, mp, _ => rfl
  | r :: rs, κ :: κs, b, mp, hv => by
    simp only [tgts, List.mem_append, not_or] at hv
    have hn : lookup (fun p : Nat × Nat => p.2 == mp) r = none := lookup_none (fun p hp => by
      simp only [beq_eq_false_iff_ne]; intro he; exact hv.1 (by rw [← he]; exact List.mem_map_of_mem hp))
    simp only [renMaps, hn]
    exact renMaps_other rs κs b mp hv.2

-- Each step's fresh map names hold the maps its request carries.
def MRenOK (M0 : Nat → Nat → Nat) : List (List (Nat × Nat)) → List (Nat → Nat → Nat) → Prop
  | r :: rs, κ :: κs => (∀ p ∈ r, M0 p.2 = κ p.1) ∧ MRenOK M0 rs κs
  | _, _ => True

theorem mrenOK_congr {M0 M0' : Nat → Nat → Nat} : ∀ (rs : List (List (Nat × Nat))) (κs : List (Nat → Nat → Nat)),
    (∀ v ∈ tgts rs, M0 v = M0' v) → MRenOK M0' rs κs → MRenOK M0 rs κs
  | [], _, _, _ => trivial
  | _ :: _, [], _, _ => trivial
  | r :: rs, κ :: κs, hag, ⟨hh, ht⟩ => by
    refine ⟨fun p hp => ?_, mrenOK_congr rs κs (fun v hv => hag v (by simp [tgts, hv])) ht⟩
    rw [hag p.2 (by simp only [tgts, List.mem_append]; exact Or.inl (List.mem_map_of_mem hp))]; exact hh p hp

theorem renMaps_ok : ∀ (rs : List (List (Nat × Nat))) (κs : List (Nat → Nat → Nat)) (b : Nat → Nat → Nat),
    distinct (tgts rs) = true → MRenOK (renMaps rs κs b) rs κs
  | [], _, _, _ => trivial
  | _ :: _, [], _, _ => trivial
  | r :: rs, κ :: κs, b, hd => by
    simp only [tgts] at hd
    obtain ⟨hr, hrs, hdis⟩ := distinct_append hd
    refine ⟨fun p hp => ?_, mrenOK_congr rs κs (fun v hv => ?_) (renMaps_ok rs κs b hrs)⟩
    · simp only [renMaps, lookup_ren hr p hp]
    · have hn : lookup (fun p : Nat × Nat => p.2 == v) r = none := lookup_none (fun p hp => by
        simp only [beq_eq_false_iff_ne]; intro he; exact hdis v (by rw [← he]; exact List.mem_map_of_mem hp) hv)
      simp only [renMaps, hn]

def SHeadL (s : SMachine) (Z MZ : List Nat) (W : Nat → Nat) (M0 : Nat → Nat → Nat) (σ : List (Nat × E)) (rd : Nat → E → E)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) : List (List (Nat × Nat)) → List (List (Nat × Nat)) → List SRequest → Prop
  | r :: _, mr :: _, q :: _ => SHead s Z MZ W M0 σ rd ρ M r mr q.1 q.2
  | _, _, _ => True

theorem skrun_sound (s : SMachine) (ps : List SEntry) (hl : checkSMachine s ps = true) (Z MZ : List Nat) (insts qinsts : List (Nat × E))
    (W : Nat → Nat) (M0 : Nat → Nat → Nat)
    (hfz : ∀ v ∈ flagVars s.f.flags, v ∈ Z) (hterms : sTermsOk s Z = true) (hmaps : sMapsOk s MZ = true) :
    ∀ (ws : List C) (rs mrs : List (List (Nat × Nat))) (qs : List SRequest) (σ : List (Nat × E)) (rd : Nat → E → E)
      (ρ : Nat → Nat) (M : Nat → Nat → Nat),
      ws.length = rs.length → ws.length = mrs.length → ws.length = qs.length →
      (∀ w ∈ ws, ∀ c ∈ sFrameHyps s (ps.map (·.law)) insts qinsts w, avoids Z c = true ∧ avoidsMaps MZ c = true) →
      (∀ r ∈ rs, ∀ p ∈ r, p.1 ∈ s.extVars) →
      (∀ r ∈ rs.tail, ∀ i ∈ s.extVars, ∃ p ∈ r, p.1 = i) →
      (∀ r ∈ mrs, ∀ p ∈ r, p.1 ∈ s.carried) →
      (∀ r ∈ mrs.tail, ∀ mp ∈ s.carried, ∃ p ∈ r, p.1 = mp) →
      RenOK W rs.tail (sExts s ρ M qs).tail → MRenOK M0 mrs.tail (qs.map (·.2)).tail →
      SReach s ρ M → SDenotes s Z MZ W M0 σ rd ρ M → SHeadL s Z MZ W M0 σ rd ρ M rs mrs qs → SAllowed s ws ρ M qs →
      (∀ c ∈ (sRun s (ps.map (·.law)) insts qinsts ws rs mrs σ rd).1, evalC W M0 c = true)
        ∧ SDenotes s Z MZ W M0 (sRun s (ps.map (·.law)) insts qinsts ws rs mrs σ rd).2.1 (sRun s (ps.map (·.law)) insts qinsts ws rs mrs σ rd).2.2
            (sEnd s ρ M qs).1 (sEnd s ρ M qs).2
  | [], rs, mrs, qs, σ, rd, ρ, M, hl1, hl2, hl3, _, _, _, _, _, _, _, _, hD, _, _ => by
    cases rs with
    | cons _ _ => simp at hl1
    | nil =>
      cases mrs with
      | cons _ _ => simp at hl2
      | nil =>
        cases qs with
        | cons _ _ => simp at hl3
        | nil => exact ⟨fun c hc => by simp [sRun] at hc, hD⟩
  | w :: ws, rs, mrs, qs, σ, rd, ρ, M, hl1, hl2, hl3, hav, hkeys, hcov, hmkeys, hmcov, hren, hmren, hr, hD, hH, hK => by
    rcases rs with _ | ⟨r, rs⟩
    · simp at hl1
    rcases mrs with _ | ⟨mr, mrs⟩
    · simp at hl2
    rcases qs with _ | ⟨q, qs⟩
    · simp at hl3
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl1 hl2 hl3
    simp only [List.tail_cons] at hcov hmcov
    have hren1 : RenOK W rs (sExts s (sNext s ρ M q.1 q.2).1 (sNext s ρ M q.1 q.2).2 qs) := hren
    have hmren1 : MRenOK M0 mrs (qs.map (·.2)) := hmren
    obtain ⟨hA, hW, hK'⟩ := hK
    have hH1 : SHead s Z MZ W M0 σ rd ρ M r mr q.1 q.2 := hH
    obtain ⟨hfav, hstp, hwr, hev⟩ := sTermsOk_parts hterms
    obtain ⟨hstm, hwrm, hevm⟩ := sMapsOk_parts hmaps
    have hD' := sstep_denotes s Z MZ W M0 (sOk_of hl) hfz hfav r mr q.1 q.2 hD hH1 (hkeys r List.mem_cons_self) hstp
      (fun w hw => (hwr w hw).1) hev hstm hwrm hevm
    have hr' : SReach s (sNext s ρ M q.1 q.2).1 (sNext s ρ M q.1 q.2).2 := SReach.step ρ M q.1 q.2 hr hA
    -- The next step's frame, its request set and its maps read, agrees with the next state and request.
    have hH' : SHeadL s Z MZ W M0 (stepSub s.f (frameSub r σ) (frameRd mr rd)) (stepRdS s (frameSub r σ) (frameRd mr rd))
        (sNext s ρ M q.1 q.2).1 (sNext s ρ M q.1 q.2).2 rs mrs qs := by
      rcases rs with _ | ⟨r', rs'⟩
      · exact trivial
      rcases mrs with _ | ⟨mr', mrs'⟩
      · exact trivial
      rcases qs with _ | ⟨q', qs'⟩
      · exact trivial
      have hr1 : ∀ p ∈ r', W p.2 = sReq s (sNext s ρ M q.1 q.2).1 (sNext s ρ M q.1 q.2).2 q'.1 q'.2 p.1 := hren1.1
      have hm1 : ∀ p ∈ mr', M0 p.2 = q'.2 p.1 := hmren1.1
      refine ⟨fun v hvz => ?_, fun mp k hmz => ?_⟩
      · by_cases hve : v ∈ s.extVars
        · rw [applyS_frame_in (hcov r' List.mem_cons_self v hve) hr1]
          simp only [withExt]; rw [if_pos (List.contains_iff_mem.mpr hve)]
        · rw [applyS_frame_out (fun p hp he => hve (by rw [← he]; exact hkeys r' (List.mem_cons_of_mem _ List.mem_cons_self) p hp)),
            hD'.1 v hve hvz]
          simp only [withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hve)]
      · by_cases hmc : mp ∈ s.carried
        · cases hlk : lookup (fun p : Nat × Nat => p.1 == mp) mr' with
          | none =>
            obtain ⟨p, hp, hp1⟩ := hmcov mr' List.mem_cons_self mp hmc
            have := lookup_none_all hlk p hp
            simp [hp1] at this
          | some p0 =>
            have hp0 := lookup_some hlk
            simp only [beq_iff_eq] at hp0
            simp only [frameRd, hlk, evalE]
            rw [hm1 p0 hp0.1, hp0.2]; simp only [withCarried]; rw [if_pos (List.contains_iff_mem.mpr hmc)]
        · have hlk : lookup (fun p : Nat × Nat => p.1 == mp) mr' = none := lookup_none (fun p hp => by
            simp only [beq_eq_false_iff_ne]; intro he
            exact hmc (by rw [← he]; exact hmkeys mr' (List.mem_cons_of_mem _ List.mem_cons_self) p hp))
          simp only [frameRd, hlk]
          rw [hD'.2 mp k hmc hmz]; simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmc)]
    have hren' : RenOK W rs.tail (sExts s (sNext s ρ M q.1 q.2).1 (sNext s ρ M q.1 q.2).2 qs).tail := by
      rcases rs with _ | ⟨r', rs'⟩
      · exact trivial
      rcases qs with _ | ⟨q', qs'⟩
      · cases rs' <;> exact trivial
      exact hren1.2
    have hmren' : MRenOK M0 mrs.tail (qs.map (·.2)).tail := by
      rcases mrs with _ | ⟨mr', mrs'⟩
      · exact trivial
      rcases qs with _ | ⟨q', qs'⟩
      · cases mrs' <;> exact trivial
      exact hmren1.2
    obtain ⟨ih1, ih2⟩ := skrun_sound s ps hl Z MZ insts qinsts W M0 hfz hterms hmaps ws rs mrs qs _ _ _ _ hl1 hl2 hl3
      (fun w' hw' => hav w' (List.mem_cons_of_mem _ hw'))
      (fun r' hr'' => hkeys r' (List.mem_cons_of_mem _ hr''))
      (fun r' hr'' => hcov r' (List.mem_of_mem_tail hr''))
      (fun r' hr'' => hmkeys r' (List.mem_cons_of_mem _ hr''))
      (fun r' hr'' => hmcov r' (List.mem_of_mem_tail hr''))
      hren' hmren' hr' hD' hH' hK'
    refine ⟨fun c hc => ?_, ih2⟩
    simp only [sRun, List.mem_append, List.mem_map] at hc
    rcases hc with ⟨c', hc', rfl⟩ | hc
    · exact sframe_hyps s Z MZ W M0 (sOk_of hl) (ps.map (·.law)) insts qinsts
        (fun l hl' => by obtain ⟨e', he', rfl⟩ := List.mem_map.mp hl'; exact smachine_sound s ps hl ρ M hr e' he')
        (slaws_avoid hl) hH1 (fun c hc => (hav w List.mem_cons_self c hc).1) (fun c hc => (hav w List.mem_cons_self c hc).2) hA hW c' hc'
    · exact ih1 c hc

/-- The k-step rule over sets: an accepted k-step goal makes its law hold. -/
theorem skstep_sound (s : SMachine) (ps : List SEntry) (sl : SKStep)
    (hl : checkSMachine s ps = true) (hc : checkSKStep s ps sl = true) : SKStepHolds s sl := by
  intro ρ M hr q₁ qs hlen hK
  simp only [checkSKStep, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlw, hlm⟩, hhead⟩, hmhead⟩, hdist⟩, hmdist⟩, hkeys⟩, hcov⟩, hmkeys⟩, hmcov⟩, hpr⟩, hpm⟩, hpre⟩, hws⟩, hterms⟩, hmaps⟩, hgoal⟩ := hc
  obtain ⟨hpreS, hrp⟩ := spre_parts hl
  have hflags : ∀ v ∈ flagVars s.f.flags, v ∈ szone s sl := fun v hv => List.mem_append_right _ hv
  obtain ⟨rs, hrs⟩ : ∃ rs, sl.k.ren = [] :: rs := by
    cases h : sl.k.ren with
    | nil => rw [h] at hhead; simp at hhead
    | cons r rs => rw [h] at hhead; simp only [List.head?_cons, Option.some.injEq] at hhead; exact ⟨rs, by rw [hhead]⟩
  obtain ⟨mrs, hmrs⟩ : ∃ mrs, sl.mren = [] :: mrs := by
    cases h : sl.mren with
    | nil => rw [h] at hmhead; simp at hmhead
    | cons r rs => rw [h] at hmhead; simp only [List.head?_cons, Option.some.injEq] at hmhead; exact ⟨rs, by rw [hmhead]⟩
  let W := renEnv sl.k.ren (sExts s ρ M (q₁ :: qs)) (withExt s ρ (sReq s ρ M q₁.1 q₁.2))
  let M0 := renMaps sl.mren ((q₁ :: qs).map (·.2)) (withCarried s M q₁.2)
  have hWo : ∀ v, v ∉ szone s sl → W v = withExt s ρ (sReq s ρ M q₁.1 q₁.2) v := fun v hv =>
    renEnv_other _ _ _ v (fun h => hv (List.mem_append_left _ h))
  have hMo : ∀ mp, mp ∉ tgts sl.mren → M0 mp = withCarried s M q₁.2 mp := fun mp hmp => renMaps_other _ _ _ mp hmp
  have hD0 : SDenotes s (szone s sl) (tgts sl.mren) W M0 [] getRd ρ M := by
    refine ⟨fun v hve hvz => ?_, fun mp k hmc hmz => ?_⟩
    · rw [applyS_nil', hWo v hvz]; simp only [withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hve)]
    · simp only [getRd, evalE]; rw [hMo mp hmz]; simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmc)]
  have hH0 : SHeadL s (szone s sl) (tgts sl.mren) W M0 [] getRd ρ M sl.k.ren sl.mren (q₁ :: qs) := by
    rw [hrs, hmrs]
    show SHead s (szone s sl) (tgts ([] :: mrs)) W M0 [] getRd ρ M [] [] q₁.1 q₁.2
    refine ⟨fun v hvz => ?_, fun mp k hmz => ?_⟩
    · simp only [frameSub, List.map_nil, List.append_nil, applyS_nil']; exact hWo v hvz
    · simp only [frameRd, lookup, getRd, evalE]; rw [hMo mp (by rw [hmrs]; exact hmz)]
  have hren0 : RenOK W sl.k.ren.tail (sExts s ρ M (q₁ :: qs)).tail := by
    have h : RenOK W sl.k.ren (sExts s ρ M (q₁ :: qs)) := renEnv_ok sl.k.ren _ _ hdist
    rw [hrs] at h ⊢; exact h.2
  have hmren0 : MRenOK M0 sl.mren.tail ((q₁ :: qs).map (·.2)).tail := by
    have h : MRenOK M0 sl.mren ((q₁ :: qs).map (·.2)) := renMaps_ok sl.mren _ _ hmdist
    rw [hmrs] at h ⊢; exact h.2
  obtain ⟨hh, hfin⟩ := skrun_sound s ps hl (szone s sl) (tgts sl.mren) sl.k.insts sl.qinsts W M0 hflags hterms hmaps
    sl.k.whens sl.k.ren sl.mren (q₁ :: qs) [] getRd ρ M hlw (by omega) (by simp only [List.length_cons]; omega)
    hws (fun r hr p hp => List.contains_iff_mem.mp (hkeys r hr p hp))
    (fun r hr i hi => by have := hcov r hr i hi; simpa only [List.any_eq_true, beq_iff_eq] using this)
    (fun r hr p hp => List.contains_iff_mem.mp (hmkeys r hr p hp))
    (fun r hr i hi => by have := hmcov r hr i hi; simpa only [List.any_eq_true, beq_iff_eq] using this)
    hren0 hmren0 hr hD0 hH0 hK
  have hfin' : SDenotes s (szone s sl) (tgts sl.mren) W M0 (sKOut s (ps.map (·.law)) sl).2.1 (sKOut s (ps.map (·.law)) sl).2.2
      (sEnd s ρ M (q₁ :: qs)).1 (sEnd s ρ M (q₁ :: qs)).2 := hfin
  apply Decidable.byContradiction; intro hn
  have hn' : ¬ evalC (primed sl.k.prime (sEnd s ρ M (q₁ :: qs)).1 W) (primedMaps sl.k.primeMaps (sEnd s ρ M (q₁ :: qs)).2 M0) sl.k.then_ = true := hn
  apply sound _ _ hgoal W M0
  intro c hc
  simp only [sKGoal, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | hc) | rfl
  · -- The precondition: at the first state (it reads no map, no request and no fresh variable).
    rw [noReadsC W M0 M s.f.m.pre hrp, congrC W ρ M s.f.m.pre (fun j hj => ?_)]
    · exact pre_sreach s hpreS hrp hr
    · rw [hWo j (avoids_occ hpre hj)]; simp only [withExt]
      rw [if_neg (fun h' => avoids_occ hpreS hj (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.contains_iff_mem.mp h')))))]
  · exact hh c hc
  · -- `then`, read across the run, is what SKStepHolds reads.
    have hrdE : ∀ mp k, evalE W M0 (kEndRd sl.k (sKOut s (ps.map (·.law)) sl).2.2 mp k)
        = primedMaps sl.k.primeMaps (sEnd s ρ M (q₁ :: qs)).2 M0 mp (evalE W M0 k) := by
      intro mp k
      simp only [kEndRd, primedMaps]
      cases hq : lookup (fun q => q.2 == mp) sl.k.primeMaps with
      | none => simp [evalE]
      | some q =>
        have hq1 := hpm q (lookup_some hq).1
        simp only [Bool.not_eq_true'] at hq1
        exact hfin'.2 q.1 k (by simpa using hq1.1) (by simpa using hq1.2)
    have henv : applyS (kEndSub sl.k (sKOut s (ps.map (·.law)) sl).2.1 (sKOut s (ps.map (·.law)) sl).2.2) W M0
        = primed sl.k.prime (sEnd s ρ M (q₁ :: qs)).1 W := by
      funext i
      rw [kEndSub, applyS_primes]
      simp only [primed]
      cases hq : lookup (fun q => q.2 == i) sl.k.prime with
      | none => rfl
      | some q =>
        have hq1 := hpr q (lookup_some hq).1
        simp only [Bool.not_eq_true'] at hq1
        have hqi : q.1 ∉ s.extVars := by simpa using hq1.1
        have hqz : q.1 ∉ szone s sl := by simpa using hq1.2
        show evalE W M0 (substRE (sKOut s (ps.map (·.law)) sl).2.1 (sKOut s (ps.map (·.law)) sl).2.2 (.var q.1)) = (sEnd s ρ M (q₁ :: qs)).1 q.1
        rw [substR_var]; exact hfin'.1 q.1 hqi hqz
    simp only [evalC, substR_evalC _ _ W M0 _ hrdE, henv]
    simpa using hn'

end Kern

#print axioms Kern.smachine_sound
#print axioms Kern.skstep_sound

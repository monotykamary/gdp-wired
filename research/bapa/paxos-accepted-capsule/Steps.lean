import StepLaw

/-!
Steps: kernel.ts's k-step laws, "every k requests in a row that the machine allows, each meeting its `when`, take a
reachable state to one where `then` holds", proven sound.

The goal is a symbolic run, as kernel.ts builds it: a frame is a substitution (each state variable a term over the
first state) and a read of each map (a term over the first state's maps); a step composes the machine's step terms
(flags inlined) after the frame, and a map read after it is read-over-write. Before each step the laws, the assumption
and that step's `when` are read at the frame; the first step reads its request's inputs by their own names, the j-th
(j ≥ 2) by fresh variables (`ren`). `then` reads the first state by plain names and the last by primed ones.

One invariant carries the proof (`Denotes`, kept by `step_denotes`): the frame denotes the real state after j steps
(outside the inputs, the fresh variables and the flags) and the real maps. So every hypothesis holds at the first state
with the fresh variables set to the later requests (`krun_sound`), and a refuted goal leaves `then` no way to fail
(`kstep_sound`). Lean builds the goal itself; only the tree comes from TypeScript.
-/

namespace Kern

structure KStep where
  whens : List C                 -- one per step, flags inlined (0 ≤ 0 for a step with none); k is the length
  then_ : C
  ren : List (List (Nat × Nat))  -- per step: (input, the variable the goal reads it by there); [] for the first step
  prime : List (Nat × Nat)       -- a state variable, and the name `then` reads its value after the last step by
  primeMaps : List (Nat × Nat)   -- a map, and the name `then` reads it after the last step by
  insts : List (Nat × E)         -- (law index, key): where each frame assumes the laws about every key
  proof : List VDef × Tree

def frameSub (r : List (Nat × Nat)) (σ : List (Nat × E)) : List (Nat × E) := r.map (fun p => (p.1, .var p.2)) ++ σ
def stepSub (f : FMMachine) (τ : List (Nat × E)) (rd : Nat → E → E) : List (Nat × E) :=
  f.m.step.map (fun p => (p.1, substRE τ rd (inlineE f.flags p.2))) ++ τ
def stepRd (f : FMMachine) (τ : List (Nat × E)) (rd : Nat → E → E) : Nat → E → E := fun mp k =>
  match lookup (fun w => w.1 == mp) f.m.writes with
  | some w => .ite (.eq k (substRE τ rd (inlineE f.flags w.2.1))) (substRE τ rd (inlineE f.flags w.2.2)) (rd mp k)
  | none => rd mp k
def frameHyps (f : FMMachine) (laws : List MLaw) (insts : List (Nat × E)) (w : C) : List C :=
  scalarHyps laws ++ instHyps laws insts ++ [inlineC f.flags f.m.assume, w]

-- The hypotheses along the steps, and the frame after them.
def kRun (f : FMMachine) (laws : List MLaw) (insts : List (Nat × E)) :
    List C → List (List (Nat × Nat)) → List (Nat × E) → (Nat → E → E) → List C × List (Nat × E) × (Nat → E → E)
  | w :: ws, r :: rs, σ, rd =>
    ((frameHyps f laws insts w).map (substRC (frameSub r σ) rd) ++ (kRun f laws insts ws rs (stepSub f (frameSub r σ) rd) (stepRd f (frameSub r σ) rd)).1,
      (kRun f laws insts ws rs (stepSub f (frameSub r σ) rd) (stepRd f (frameSub r σ) rd)).2)
  | _, _, σ, rd => ([], σ, rd)

def getRd : Nat → E → E := fun mp k => .get mp k
def kEndSub (sl : KStep) (σ : List (Nat × E)) (rd : Nat → E → E) : List (Nat × E) :=
  sl.prime.map fun q => (q.2, substRE σ rd (.var q.1))
def kEndRd (sl : KStep) (rd : Nat → E → E) : Nat → E → E := fun mp k =>
  match lookup (fun q => q.2 == mp) sl.primeMaps with
  | some q => rd q.1 k
  | none => .get mp k

def kOut (f : FMMachine) (laws : List MLaw) (sl : KStep) := kRun f laws sl.insts sl.whens sl.ren [] getRd
def kGoal (f : FMMachine) (laws : List MLaw) (sl : KStep) : List C :=
  [f.m.pre] ++ (kOut f laws sl).1 ++ [.not (substRC (kEndSub sl (kOut f laws sl).2.1 (kOut f laws sl).2.2) (kEndRd sl (kOut f laws sl).2.2) sl.then_)]

def distinct : List Nat → Bool
  | [] => true
  | a :: as => !as.contains a && distinct as

def tgts : List (List (Nat × Nat)) → List Nat
  | [] => []
  | r :: rs => r.map (·.2) ++ tgts rs
def zone (f : FMMachine) (sl : KStep) : List Nat := tgts sl.ren ++ flagVars f.flags

def checkKStep (f : FMMachine) (ps : List MEntry) (sl : KStep) : Bool :=
  sl.whens.length == sl.ren.length && sl.ren.head? == some [] && distinct (tgts sl.ren)
    && sl.ren.all (fun r => r.all fun p => f.m.inputs.contains p.1)
    && sl.ren.tail.all (fun r => f.m.inputs.all fun i => r.any (·.1 == i))
    && (tgts sl.ren).all (fun v => !f.m.inputs.contains v)
    && sl.prime.all (fun q => !f.m.inputs.contains q.1 && !(zone f sl).contains q.1)
    && avoids (zone f sl) f.m.pre
    && sl.whens.all (fun w => (frameHyps f (ps.map (·.law)) sl.insts w).all (avoids (zone f sl)))
    && f.m.step.all (fun p => avoidsE (zone f sl) (inlineE f.flags p.2))
    && f.m.writes.all (fun w => avoidsE (zone f sl) (inlineE f.flags w.2.1) && avoidsE (zone f sl) (inlineE f.flags w.2.2))
    && avoids (flagVars f.flags) sl.then_
    && checkGoal ⟨sl.proof.1, kGoal f (ps.map (·.law)) sl⟩ sl.proof.2

/-! What a k-step law claims -/

-- One step from ρ, M with request ι: flags decided, then the step's terms and writes.
def kNext (f : FMMachine) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) : (Nat → Nat) × (Nat → Nat → Nat) :=
  (applyS f.m.step (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M,
   writeMaps f.m.writes (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M)

def kEnd (f : FMMachine) : (Nat → Nat) → (Nat → Nat → Nat) → List (Nat → Nat) → (Nat → Nat) × (Nat → Nat → Nat)
  | ρ, M, [] => (ρ, M)
  | ρ, M, ι :: ιs => kEnd f (kNext f ρ M ι).1 (kNext f ρ M ι).2 ιs

-- Each request allowed (the assumption, flags decided) and meeting its step's `when`.
def KAllowed (f : FMMachine) : List C → (Nat → Nat) → (Nat → Nat → Nat) → List (Nat → Nat) → Prop
  | w :: ws, ρ, M, ι :: ιs =>
    evalC (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M f.m.assume = true
      ∧ evalC (withInputs f.m.inputs ρ ι) M w = true ∧ KAllowed f ws (kNext f ρ M ι).1 (kNext f ρ M ι).2 ιs
  | _, _, _, _ => True

-- What `then`'s plain names read: the first state with the first request, each later request at its fresh variables.
def renEnv : List (List (Nat × Nat)) → List (Nat → Nat) → (Nat → Nat) → Nat → Nat
  | r :: rs, ι :: ιs, b => fun v => match lookup (fun p => p.2 == v) r with
    | some p => ι p.1
    | none => renEnv rs ιs b v
  | _, _, b => b

/-- A k-step law: from every reachable state, every k requests in a row the machine allows (each with its flags
decided, each meeting its `when`) end in a state where `then` holds: primed names read the last state and maps, plain
names the first state with the first request, and each later request's inputs are read by their fresh variables. -/
def KStepHolds (f : FMMachine) (sl : KStep) : Prop :=
  ∀ ρ M, FMReach f ρ M → ∀ ι₁ ιs, ιs.length + 1 = sl.whens.length → KAllowed f sl.whens ρ M (ι₁ :: ιs) →
    evalC (primed sl.prime (kEnd f ρ M (ι₁ :: ιs)).1 (renEnv sl.ren (ι₁ :: ιs) (withInputs f.m.inputs ρ ι₁)))
      (primedMaps sl.primeMaps (kEnd f ρ M (ι₁ :: ιs)).2 M) sl.then_ = true

/-! Lists -/

theorem distinct_cons {a : Nat} {as : List Nat} (h : distinct (a :: as) = true) : a ∉ as ∧ distinct as = true := by
  simp only [distinct, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun hm => ?_, h.2⟩
  have h1 := h.1
  simp at h1
  exact h1 hm

theorem distinct_append : ∀ {l1 l2 : List Nat}, distinct (l1 ++ l2) = true →
    distinct l1 = true ∧ distinct l2 = true ∧ ∀ a ∈ l1, a ∉ l2
  | [], l2, h => ⟨rfl, h, fun _ ha => by simp at ha⟩
  | a :: as, l2, h => by
    rw [List.cons_append] at h
    obtain ⟨hn, hd⟩ := distinct_cons h
    obtain ⟨h1, h2, h3⟩ := distinct_append hd
    refine ⟨by simp only [distinct, h1, Bool.and_true, Bool.not_eq_true']; simpa using fun h' => hn (List.mem_append_left l2 h'), h2, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact fun h' => hn (List.mem_append_right _ h')
    · exact h3 x hx'

theorem assoc_append_or (l1 l2 : List (Nat × E)) (i : Nat) : assoc (l1 ++ l2) i = (assoc l1 i).or (assoc l2 i) := by
  simp only [assoc, lookup_append]
  cases lookup (fun p : Nat × E => p.1 == i) l1 <;> rfl

theorem applyS_nil' (W : Nat → Nat) (M : Nat → Nat → Nat) : applyS [] W M = W := by
  funext i; simp [applyS, assoc, lookup]

theorem assoc_stepSub (f : FMMachine) (τ : List (Nat × E)) (rd : Nat → E → E) (v : Nat) :
    assoc (f.m.step.map (fun p => (p.1, substRE τ rd (inlineE f.flags p.2)))) v = (assoc f.m.step v).map (fun e => substRE τ rd (inlineE f.flags e)) :=
  assoc_map_snd f.m.step (fun e => substRE τ rd (inlineE f.flags e)) v

-- Reading `then`'s primed names: each the frame's term for its state variable, the rest as they are.
theorem applyS_primes (σ : List (Nat × E)) (rd : Nat → E → E) (W : Nat → Nat) (M : Nat → Nat → Nat) (i : Nat) :
    ∀ l : List (Nat × Nat), applyS (l.map fun q => (q.2, substRE σ rd (.var q.1))) W M i
      = match lookup (fun q => q.2 == i) l with
        | some q => evalE W M (substRE σ rd (.var q.1))
        | none => W i
  | [] => by simp [applyS, assoc, lookup]
  | a :: as => by
    have ih := applyS_primes σ rd W M i as
    simp only [applyS, assoc, List.map_cons, lookup] at ih ⊢
    by_cases h : a.2 = i
    · simp [h]
    · have hb : (a.2 == i) = false := by simpa using h
      simp only [hb, Bool.false_eq_true, ite_false]; exact ih

-- A fresh variable of one step reads its request.
theorem lookup_ren : ∀ {r : List (Nat × Nat)}, distinct (r.map (·.2)) = true → ∀ p ∈ r, lookup (fun q => q.2 == p.2) r = some p
  | [], _, p, hp => by simp at hp
  | a :: as, hd, p, hp => by
    simp only [List.map_cons] at hd
    obtain ⟨hna, hd'⟩ := distinct_cons hd
    simp only [lookup]
    rcases List.mem_cons.mp hp with rfl | hp'
    · simp
    · have hne : (a.2 == p.2) = false := by
        simp only [beq_eq_false_iff_ne]; intro he; exact hna (by rw [he]; exact List.mem_map_of_mem hp')
      simp only [hne, Bool.false_eq_true, ite_false]; exact lookup_ren hd' p hp'

theorem renEnv_other : ∀ (rs : List (List (Nat × Nat))) (ιs : List (Nat → Nat)) (b : Nat → Nat) (v : Nat),
    v ∉ tgts rs → renEnv rs ιs b v = b v
  | [], ιs, b, v, _ => by cases ιs <;> rfl
  | r :: rs, [], b, v, _ => rfl
  | r :: rs, ι :: ιs, b, v, hv => by
    simp only [tgts, List.mem_append, not_or] at hv
    have hn : lookup (fun p : Nat × Nat => p.2 == v) r = none := lookup_none (fun p hp => by
      simp only [beq_eq_false_iff_ne]; intro he; exact hv.1 (by rw [← he]; exact List.mem_map_of_mem hp))
    simp only [renEnv, hn]
    exact renEnv_other rs ιs b v hv.2

-- Each step's fresh variables hold its request's inputs.
def RenOK (W : Nat → Nat) : List (List (Nat × Nat)) → List (Nat → Nat) → Prop
  | r :: rs, ι :: ιs => (∀ p ∈ r, W p.2 = ι p.1) ∧ RenOK W rs ιs
  | _, _ => True

theorem renOK_congr {W W' : Nat → Nat} : ∀ (rs : List (List (Nat × Nat))) (ιs : List (Nat → Nat)),
    (∀ v ∈ tgts rs, W v = W' v) → RenOK W' rs ιs → RenOK W rs ιs
  | [], _, _, _ => trivial
  | _ :: _, [], _, _ => trivial
  | r :: rs, ι :: ιs, hag, ⟨hh, ht⟩ => by
    refine ⟨fun p hp => ?_, renOK_congr rs ιs (fun v hv => hag v (by simp [tgts, hv])) ht⟩
    rw [hag p.2 (by simp only [tgts, List.mem_append]; exact Or.inl (List.mem_map_of_mem hp))]; exact hh p hp

theorem renEnv_ok : ∀ (rs : List (List (Nat × Nat))) (ιs : List (Nat → Nat)) (b : Nat → Nat),
    distinct (tgts rs) = true → RenOK (renEnv rs ιs b) rs ιs
  | [], _, _, _ => trivial
  | _ :: _, [], _, _ => trivial
  | r :: rs, ι :: ιs, b, hd => by
    simp only [tgts] at hd
    obtain ⟨hr, hrs, hdis⟩ := distinct_append hd
    refine ⟨fun p hp => ?_, renOK_congr rs ιs (fun v hv => ?_) (renEnv_ok rs ιs b hrs)⟩
    · simp only [renEnv, lookup_ren hr p hp]
    · have hn : lookup (fun p : Nat × Nat => p.2 == v) r = none := lookup_none (fun p hp => by
        simp only [beq_eq_false_iff_ne]; intro he; exact hdis v (by rw [← he]; exact List.mem_map_of_mem hp) hv)
      simp only [renEnv, hn]

/-! Frames -/

-- A step's input, read at a frame whose fresh variables hold the request.
theorem applyS_frame_in {r : List (Nat × Nat)} {σ : List (Nat × E)} {W : Nat → Nat} {M0 : Nat → Nat → Nat} {ι : Nat → Nat} {i : Nat}
    (hcov : ∃ p ∈ r, p.1 = i) (hval : ∀ p ∈ r, W p.2 = ι p.1) : applyS (frameSub r σ) W M0 i = ι i := by
  simp only [applyS, frameSub, assoc_append_or]
  cases h : assoc (r.map fun p => (p.1, E.var p.2)) i with
  | none =>
    obtain ⟨p, hp, rfl⟩ := hcov
    simp only [assoc, Option.map_eq_none_iff] at h
    have := lookup_none_all h (p.1, .var p.2) (List.mem_map_of_mem hp)
    simp at this
  | some e =>
    simp only [assoc, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, rfl⟩ := h
    obtain ⟨hqm, hqi⟩ := lookup_some hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hqm
    simp at hqi
    simp only [Option.some_or, evalE, hval p hp, hqi]

-- Any other variable reads through to the frame.
theorem applyS_frame_out {r : List (Nat × Nat)} {σ : List (Nat × E)} {W : Nat → Nat} {M0 : Nat → Nat → Nat} {i : Nat}
    (hi : ∀ p ∈ r, p.1 ≠ i) : applyS (frameSub r σ) W M0 i = applyS σ W M0 i := by
  have hn : assoc (r.map fun p => (p.1, E.var p.2)) i = none := by
    simp only [assoc, Option.map_eq_none_iff]
    exact lookup_none (fun a ha => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      simp only [beq_eq_false_iff_ne]; exact hi p hp)
  simp only [applyS, frameSub, assoc_append_or, hn, Option.none_or]

-- The frame σ, rd denotes the state ρ, M (read from the first state W, M0): every variable outside the inputs and
-- the zone, and every map read.
def Denotes (f : FMMachine) (Z : List Nat) (W : Nat → Nat) (M0 : Nat → Nat → Nat) (σ : List (Nat × E)) (rd : Nat → E → E)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) : Prop :=
  (∀ v, v ∉ f.m.inputs → v ∉ Z → applyS σ W M0 v = ρ v) ∧ (∀ mp k, evalE W M0 (rd mp k) = M mp (evalE W M0 k))

-- The frame a step reads (its inputs set) agrees with the state and request outside the zone.
def HeadAgree (f : FMMachine) (Z : List Nat) (W : Nat → Nat) (M0 : Nat → Nat → Nat) (σ : List (Nat × E)) (ρ : Nat → Nat) :
    List (List (Nat × Nat)) → List (Nat → Nat) → Prop
  | r :: _, ι :: _ => Agree Z (applyS (frameSub r σ) W M0) (withInputs f.m.inputs ρ ι)
  | _, _ => True

section
variable (f : FMMachine) (Z : List Nat) (W : Nat → Nat) (M0 : Nat → Nat → Nat)

-- A term of the step read at the frame is its value at the real state, flags decided.
theorem frame_term {σ : List (Nat × E)} {rd : Nat → E → E} {ρ : Nat → Nat} {M : Nat → Nat → Nat} {r : List (Nat × Nat)} {ι : Nat → Nat}
    (hrd : ∀ mp k, evalE W M0 (rd mp k) = M mp (evalE W M0 k))
    (hX : Agree Z (applyS (frameSub r σ) W M0) (withInputs f.m.inputs ρ ι)) (e : E) (he : avoidsE Z (inlineE f.flags e) = true) :
    evalE W M0 (substRE (frameSub r σ) rd (inlineE f.flags e)) = evalE (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M e := by
  rw [substR_evalE (frameSub r σ) rd W M0 M hrd,
    congrE _ (withInputs f.m.inputs ρ ι) M _ (fun i hi => hX i (avoidsE_occ he hi)), inline_evalE]

theorem step_denotes {σ : List (Nat × E)} {rd : Nat → E → E} {ρ : Nat → Nat} {M : Nat → Nat → Nat} (r : List (Nat × Nat)) (ι : Nat → Nat)
    (hD : Denotes f Z W M0 σ rd ρ M)
    (hX : Agree Z (applyS (frameSub r σ) W M0) (withInputs f.m.inputs ρ ι))
    (hfz : ∀ v ∈ flagVars f.flags, v ∈ Z)
    (hst : ∀ p ∈ f.m.step, avoidsE Z (inlineE f.flags p.2) = true)
    (hwr : ∀ w ∈ f.m.writes, avoidsE Z (inlineE f.flags w.2.1) = true ∧ avoidsE Z (inlineE f.flags w.2.2) = true) :
    Denotes f Z W M0 (stepSub f (frameSub r σ) rd) (stepRd f (frameSub r σ) rd) (kNext f ρ M ι).1 (kNext f ρ M ι).2 := by
  obtain ⟨_, hrd⟩ := hD
  refine ⟨fun v hvi hvz => ?_, fun mp k => ?_⟩
  · simp only [kNext, applyS, stepSub, assoc_append_or, assoc_stepSub]
    cases h : assoc f.m.step v with
    | some e =>
      have hm : (v, e) ∈ f.m.step := by
        simp only [assoc, Option.map_eq_some_iff] at h
        obtain ⟨q, hq, rfl⟩ := h
        obtain ⟨hqm, hqv⟩ := lookup_some hq
        simp only [beq_iff_eq] at hqv
        rw [← hqv]; exact hqm
      simp only [Option.map_some, Option.some_or]
      exact frame_term f Z W M0 hrd hX e (hst (v, e) hm)
    | none =>
      simp only [Option.map_none, Option.none_or]
      have hvf : v ∉ flagVars f.flags := fun h' => hvz (hfz v h')
      rw [decide_other hvf, withInputs_other hvi]
      show applyS (frameSub r σ) W M0 v = ρ v
      rw [hX v hvz, withInputs_other hvi]
  · simp only [kNext, stepRd, writeMaps]
    cases hw : lookup (fun w : Nat × E × E => w.1 == mp) f.m.writes with
    | none => simp only [hrd]
    | some w =>
      have hm := (lookup_some hw).1
      simp only [evalE, evalC, frame_term f Z W M0 hrd hX w.2.1 (hwr w hm).1, frame_term f Z W M0 hrd hX w.2.2 (hwr w hm).2, hrd]
      by_cases hk : evalE W M0 k = evalE (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M w.2.1 <;> simp [hk]
end

-- The laws and the precondition hold at a reachable state with any request's inputs (neither reads an input).
theorem reach_facts (f : FMMachine) (ps : List MEntry) (hl : checkFMMachine f ps = true) {ρ : Nat → Nat} {M : Nat → Nat → Nat}
    (hr : FMReach f ρ M) (ι : Nat → Nat) :
    evalC (withInputs f.m.inputs ρ ι) M f.m.pre = true ∧ ∀ e ∈ ps, e.law.Holds (withInputs f.m.inputs ρ ι) M := by
  have hl0 := hl
  simp only [checkFMMachine, Bool.and_eq_true, List.all_eq_true] at hl
  obtain ⟨⟨⟨hf, hpref⟩, _⟩, hc⟩ := hl
  obtain ⟨ρ₀, hr₀, hag⟩ := fmreach_plain f hf hr
  have hlaws : ∀ e ∈ ps, e.law.Holds ρ M := fmmachine_sound f ps hl0 ρ M hr
  have hcm := hc
  simp only [checkMMachine, Bool.and_eq_true, List.all_eq_true] at hcm
  obtain ⟨⟨hpa, hpr⟩, hent⟩ := hcm
  try simp only [Bool.not_eq_true'] at hpr
  have hpre : evalC ρ M f.m.pre = true := by
    rw [congrC ρ ρ₀ M f.m.pre (fun j hj => hag j (avoids_occ hpref hj))]
    exact pre_mreach (m := f.plain) hpa hpr hr₀
  have hagX : Agree f.m.inputs (withInputs f.m.inputs ρ ι) ρ := fun i hi => withInputs_other hi ρ ι
  refine ⟨?_, fun e he => holds_agree e.law (hent e he).1.1.1 hagX M (hlaws e he)⟩
  rw [congrC (withInputs f.m.inputs ρ ι) ρ M f.m.pre (fun j hj => hagX j (fun h =>
    avoids_occ hpa hj (List.mem_append_left _ (List.mem_append_left _ h))))]
  exact hpre

-- Every hypothesis of a frame holds where the frame is read.
theorem frame_hyps (f : FMMachine) (ps : List MEntry) (hl : checkFMMachine f ps = true) (Z : List Nat) (insts : List (Nat × E))
    {W : Nat → Nat} {M0 : Nat → Nat → Nat} {σ : List (Nat × E)} {rd : Nat → E → E} {ρ : Nat → Nat} {M : Nat → Nat → Nat}
    {r : List (Nat × Nat)} {ι : Nat → Nat} {w : C}
    (hr : FMReach f ρ M) (hrd : ∀ mp k, evalE W M0 (rd mp k) = M mp (evalE W M0 k))
    (hX : Agree Z (applyS (frameSub r σ) W M0) (withInputs f.m.inputs ρ ι))
    (hav : ∀ c ∈ frameHyps f (ps.map (·.law)) insts w, avoids Z c = true)
    (hA : evalC (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M f.m.assume = true)
    (hW : evalC (withInputs f.m.inputs ρ ι) M w = true) :
    ∀ c ∈ frameHyps f (ps.map (·.law)) insts w, evalC W M0 (substRC (frameSub r σ) rd c) = true := by
  intro c hc
  obtain ⟨hpre, hlaws⟩ := reach_facts f ps hl hr ι
  have hb := before_true f ps ⟨w, w, [], [], [], insts, ([], .leaf [] [] [] []), ([], .leaf [] [] [] [])⟩ _ M hpre hlaws hW
  have hY : evalC (withInputs f.m.inputs ρ ι) M c = true := by
    simp only [frameHyps, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (hc | hc) | rfl | rfl
    · exact hb c (by simp only [progressBefore, List.mem_append]; exact Or.inl (Or.inl (Or.inr hc)))
    · exact hb c (by simp only [progressBefore, List.mem_append]; exact Or.inl (Or.inr hc))
    · rw [inline_evalC]; exact hA
    · exact hW
  rw [substR_evalC (frameSub r σ) rd W M0 M hrd, congrC _ (withInputs f.m.inputs ρ ι) M c (fun i hi => hX i (avoids_occ (hav c hc) hi))]
  exact hY

theorem krun_sound (f : FMMachine) (ps : List MEntry) (hl : checkFMMachine f ps = true) (Z : List Nat) (insts : List (Nat × E))
    (W : Nat → Nat) (M0 : Nat → Nat → Nat)
    (hfz : ∀ v ∈ flagVars f.flags, v ∈ Z)
    (hst : ∀ p ∈ f.m.step, avoidsE Z (inlineE f.flags p.2) = true)
    (hwr : ∀ w ∈ f.m.writes, avoidsE Z (inlineE f.flags w.2.1) = true ∧ avoidsE Z (inlineE f.flags w.2.2) = true) :
    ∀ (ws : List C) (rs : List (List (Nat × Nat))) (ιs : List (Nat → Nat)) (σ : List (Nat × E)) (rd : Nat → E → E)
      (ρ : Nat → Nat) (M : Nat → Nat → Nat),
      ws.length = rs.length → ws.length = ιs.length →
      (∀ w ∈ ws, ∀ c ∈ frameHyps f (ps.map (·.law)) insts w, avoids Z c = true) →
      (∀ r ∈ rs, ∀ p ∈ r, p.1 ∈ f.m.inputs) →
      (∀ r ∈ rs.tail, ∀ i ∈ f.m.inputs, ∃ p ∈ r, p.1 = i) →
      RenOK W rs.tail ιs.tail →
      FMReach f ρ M → Denotes f Z W M0 σ rd ρ M → HeadAgree f Z W M0 σ ρ rs ιs → KAllowed f ws ρ M ιs →
      (∀ c ∈ (kRun f (ps.map (·.law)) insts ws rs σ rd).1, evalC W M0 c = true)
        ∧ Denotes f Z W M0 (kRun f (ps.map (·.law)) insts ws rs σ rd).2.1 (kRun f (ps.map (·.law)) insts ws rs σ rd).2.2
            (kEnd f ρ M ιs).1 (kEnd f ρ M ιs).2
  | [], rs, ιs, σ, rd, ρ, M, hl1, hl2, _, _, _, _, _, hD, _, _ => by
    cases rs with
    | cons _ _ => simp at hl1
    | nil =>
      cases ιs with
      | cons _ _ => simp at hl2
      | nil => exact ⟨fun c hc => by simp [kRun] at hc, hD⟩
  | w :: ws, rs, ιs, σ, rd, ρ, M, hl1, hl2, hav, hkeys, hcov, hren, hr, hD, hH, hK => by
    rcases rs with _ | ⟨r, rs⟩
    · simp at hl1
    rcases ιs with _ | ⟨ι, ιs⟩
    · simp at hl2
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl1 hl2
    simp only [List.tail_cons] at hcov hren
    obtain ⟨hA, hW, hK'⟩ := hK
    have hX : Agree Z (applyS (frameSub r σ) W M0) (withInputs f.m.inputs ρ ι) := hH
    have hD' := step_denotes f Z W M0 r ι hD hX hfz hst hwr
    have hr' : FMReach f (kNext f ρ M ι).1 (kNext f ρ M ι).2 := FMReach.step ρ M ι hr hA
    -- The next step's frame, its inputs set, agrees with the next state and request.
    have hH' : HeadAgree f Z W M0 (stepSub f (frameSub r σ) rd) (kNext f ρ M ι).1 rs ιs := by
      rcases rs with _ | ⟨r', rs'⟩
      · exact trivial
      rcases ιs with _ | ⟨ι', ιs'⟩
      · exact trivial
      intro v hvz
      by_cases hvi : v ∈ f.m.inputs
      · show applyS (frameSub r' (stepSub f (frameSub r σ) rd)) W M0 v = withInputs f.m.inputs (kNext f ρ M ι).1 ι' v
        rw [applyS_frame_in (hcov r' List.mem_cons_self v hvi) hren.1]
        simp only [withInputs, List.contains_iff_mem, hvi, ite_true]
      · show applyS (frameSub r' (stepSub f (frameSub r σ) rd)) W M0 v = withInputs f.m.inputs (kNext f ρ M ι).1 ι' v
        rw [applyS_frame_out (fun p hp he => hvi (by rw [← he]; exact hkeys r' (List.mem_cons_of_mem _ List.mem_cons_self) p hp)),
          hD'.1 v hvi hvz, withInputs_other hvi]
    have hren' : RenOK W rs.tail ιs.tail := by
      rcases rs with _ | ⟨r', rs'⟩
      · exact trivial
      rcases ιs with _ | ⟨ι', ιs'⟩
      · cases rs' <;> exact trivial
      exact hren.2
    obtain ⟨ih1, ih2⟩ := krun_sound f ps hl Z insts W M0 hfz hst hwr ws rs ιs _ _ _ _ hl1 hl2
      (fun w' hw' => hav w' (List.mem_cons_of_mem _ hw'))
      (fun r' hr'' => hkeys r' (List.mem_cons_of_mem _ hr''))
      (fun r' hr'' => hcov r' (List.mem_of_mem_tail hr''))
      hren' hr' hD' hH' hK'
    refine ⟨fun c hc => ?_, ih2⟩
    simp only [kRun, List.mem_append, List.mem_map] at hc
    rcases hc with ⟨c', hc', rfl⟩ | hc
    · exact frame_hyps f ps hl Z insts hr hD.2 hX (hav w List.mem_cons_self) hA hW c' hc'
    · exact ih1 c hc

theorem kstep_sound (f : FMMachine) (ps : List MEntry) (sl : KStep)
    (hl : checkFMMachine f ps = true) (hs : checkKStep f ps sl = true) : KStepHolds f sl := by
  intro ρ M hr ι₁ ιs hlen hK
  simp only [checkKStep, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlw, hhead⟩, hdist⟩, hkeys⟩, hcov⟩, hrv⟩, hpr⟩, hpre⟩, hws⟩, hst⟩, hwr⟩, hthen⟩, hgoal⟩ := hs
  have hflags : ∀ v ∈ flagVars f.flags, v ∈ zone f sl := fun v hv => List.mem_append_right _ hv
  obtain ⟨rs, hrs⟩ : ∃ rs, sl.ren = [] :: rs := by
    cases h : sl.ren with
    | nil => rw [h] at hhead; simp at hhead
    | cons r rs => rw [h] at hhead; simp only [List.head?_cons, Option.some.injEq] at hhead; exact ⟨rs, by rw [hhead]⟩
  let W := renEnv sl.ren (ι₁ :: ιs) (withInputs f.m.inputs ρ ι₁)
  have hWo : ∀ v, v ∉ zone f sl → W v = withInputs f.m.inputs ρ ι₁ v := fun v hv =>
    renEnv_other _ _ _ v (fun h => hv (List.mem_append_left _ h))
  have hD0 : Denotes f (zone f sl) W M [] getRd ρ M :=
    ⟨fun v hvi hvz => by rw [applyS_nil', hWo v hvz, withInputs_other hvi], fun mp k => by simp [getRd, evalE]⟩
  have hH0 : HeadAgree f (zone f sl) W M [] ρ sl.ren (ι₁ :: ιs) := by
    rw [hrs]
    show Agree _ (applyS (frameSub [] []) W M) (withInputs f.m.inputs ρ ι₁)
    intro v hvz
    simp only [frameSub, List.map_nil, List.append_nil, applyS_nil']; exact hWo v hvz
  have hren0 : RenOK W sl.ren.tail (ι₁ :: ιs).tail := by
    have h : RenOK W sl.ren (ι₁ :: ιs) := renEnv_ok sl.ren (ι₁ :: ιs) (withInputs f.m.inputs ρ ι₁) hdist
    rw [hrs] at h ⊢; exact h.2
  obtain ⟨hh, hfin⟩ := krun_sound f ps hl (zone f sl) sl.insts W M hflags
    hst hwr
    sl.whens sl.ren (ι₁ :: ιs) [] getRd ρ M hlw (by simp only [List.length_cons]; omega)
    hws (fun r hr p hp => List.contains_iff_mem.mp (hkeys r hr p hp))
    (fun r hr i hi => by have := hcov r hr i hi; simpa only [List.any_eq_true, beq_iff_eq] using this)
    hren0 hr hD0 hH0 hK
  apply Decidable.byContradiction; intro hn
  apply sound _ _ hgoal W M
  intro c hc
  simp only [kGoal, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | hc) | rfl
  · -- The precondition: at the first state (it reads no input and no fresh variable).
    obtain ⟨hpX, _⟩ := reach_facts f ps hl hr ι₁
    rw [congrC W (withInputs f.m.inputs ρ ι₁) M f.m.pre (fun j hj => hWo j (avoids_occ hpre hj))]; exact hpX
  · exact hh c hc
  · -- `then`, read across the run, is what KStepHolds reads.
    have hrdE : ∀ mp k, evalE W M (kEndRd sl (kOut f (ps.map (·.law)) sl).2.2 mp k)
        = primedMaps sl.primeMaps (kEnd f ρ M (ι₁ :: ιs)).2 M mp (evalE W M k) := by
      intro mp k
      simp only [kEndRd, primedMaps]
      cases hq : lookup (fun q => q.2 == mp) sl.primeMaps with
      | none => simp [evalE]
      | some q => exact hfin.2 q.1 k
    have henv : applyS (kEndSub sl (kOut f (ps.map (·.law)) sl).2.1 (kOut f (ps.map (·.law)) sl).2.2) W M
        = primed sl.prime (kEnd f ρ M (ι₁ :: ιs)).1 W := by
      funext i
      rw [kEndSub, applyS_primes]
      simp only [primed]
      cases hq : lookup (fun q => q.2 == i) sl.prime with
      | none => rfl
      | some q =>
        have hq1 := hpr q (lookup_some hq).1
        simp only [Bool.not_eq_true'] at hq1
        have hqi : q.1 ∉ f.m.inputs := by simpa using hq1.1
        have hqz : q.1 ∉ zone f sl := by simpa using hq1.2
        show evalE W M (substRE (kOut f (ps.map (·.law)) sl).2.1 (kOut f (ps.map (·.law)) sl).2.2 (.var q.1)) = (kEnd f ρ M (ι₁ :: ιs)).1 q.1
        have hfin' : Denotes f (zone f sl) W M (kOut f (ps.map fun e : MEntry => e.law) sl).2.1 (kOut f (ps.map fun e : MEntry => e.law) sl).2.2
            (kEnd f ρ M (ι₁ :: ιs)).1 (kEnd f ρ M (ι₁ :: ιs)).2 := hfin
        exact (substR_evalE (kOut f (ps.map fun e : MEntry => e.law) sl).2.1 _ W M _ hfin'.2 (.var q.1)).trans (hfin'.1 q.1 hqi hqz)
    simp only [evalC, substR_evalC _ _ W M _ hrdE, henv]
    simpa using hn

end Kern

#print axioms Kern.kstep_sound

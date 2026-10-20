import Steps

/-!
Sets: kernel.ts's machines with sets, proven sound. A set is a map with cells 0 or 1; three things go beyond FMMachine:
a request carries whole maps (`carried`: any maps at each request), a step writes a map at every key at once (`every`:
the value at each key, read with the key bound), and a flag may hold at every key (`qflags`: ∀ key. body, its body
reading no flag), or at every tuple of keys (∀ k₁ … kₙ. body). Lean decides a quantified flag classically, which only the meaning needs; the checker never does.

Functions from outside the rule are maps no step writes (and no request carries); `facts` are laws about the params and
those maps alone, given rather than proven: a run starts where they hold, so they hold at every state, and every goal may
assume them at the keys its proof names (`finsts`). A fact about several keys (`pfacts`: a function of several
arguments, a law between two points) is given at every value of its further keys, as a law about several keys holds,
and a goal assumes it at the tuples its proof names (`pfinsts`).

kernel.ts closes each quantified flag ?f in a goal: ?f ≤ 1; ?f = 0 ∨ body(t) at keys t the proof names (`qinsts`, a
tuple of terms over several keys); and ?f = 1 ∨ ¬body(w) at fresh witnesses w, one per key (`wits`). A real step
satisfies these with w failing keys when ?f = 0, so a goal that refutes them refutes the machine. Lean builds the same
closed goals.
-/

namespace Kern
open Classical

/-! Certificates that name their hypotheses -/


-- A proof tree with the table it reads, and the hypotheses it refutes: none named, the goal's own, in the goal's order;
-- named, any of the goal's, in any order (each must be one of the goal's), so an exporter may lay its goal out its own
-- way as long as each hypothesis it uses is one Lean builds.
abbrev Cert := List VDef × List C × Tree
-- The goal's hypotheses after the first one equal to c, if there is one.
def afterFirst (c : C) : List C → Option (List C)
  | [] => none
  | h :: t => if beqC c h then some t else afterFirst c t
-- Each named hypothesis is one of the goal's: looked for after the last one found (exporters name them mostly in the
-- goal's order), and from the start when it is not there.
def namedIn (hyps : List C) : List C → List C → Bool
  | [], _ => true
  | c :: cs, rest => match afterFirst c rest with
    | some rest' => namedIn hyps cs rest'
    | none => match afterFirst c hyps with
      | some rest' => namedIn hyps cs rest'
      | none => false
def checkIn (hyps : List C) (k : Cert) : Bool :=
  if k.2.1.isEmpty then checkGoal ⟨k.1, hyps⟩ k.2.2
  else namedIn hyps k.2.1 hyps && checkGoal ⟨k.1, k.2.1⟩ k.2.2

theorem afterFirst_some : ∀ {c : C} {l t : List C}, afterFirst c l = some t → c ∈ l ∧ ∀ x ∈ t, x ∈ l
  | _, [], _, h => by simp [afterFirst] at h
  | c, h' :: l, t, h => by
    simp only [afterFirst] at h
    split at h
    · rename_i hb
      simp only [Option.some.injEq] at h; subst h
      exact ⟨by rw [beqC_eq hb]; exact List.mem_cons_self, fun x hx => List.mem_cons_of_mem _ hx⟩
    · obtain ⟨h1, h2⟩ := afterFirst_some h
      exact ⟨List.mem_cons_of_mem _ h1, fun x hx => List.mem_cons_of_mem _ (h2 x hx)⟩

theorem namedIn_sound (hyps : List C) : ∀ (cs rest : List C), (∀ x ∈ rest, x ∈ hyps) → namedIn hyps cs rest = true → ∀ c ∈ cs, c ∈ hyps
  | [], _, _, _ => by simp
  | c :: cs, rest, hr, h => by
    simp only [namedIn] at h
    split at h
    · rename_i rest' hs
      obtain ⟨h1, h2⟩ := afterFirst_some hs
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hr _ h1
      · exact namedIn_sound hyps cs rest' (fun y hy => hr y (h2 y hy)) h x hx
    · split at h
      · rename_i rest' hs
        obtain ⟨h1, h2⟩ := afterFirst_some hs
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h1
        · exact namedIn_sound hyps cs rest' h2 h x hx
      · simp at h

theorem sound_in (hyps : List C) (k : Cert) (h : checkIn hyps k = true) (env : Nat → Nat) (maps : Nat → Nat → Nat) :
    ¬ ∀ c ∈ hyps, evalC env maps c = true := by
  intro hH
  unfold checkIn at h
  split at h
  · exact sound ⟨k.1, hyps⟩ k.2.2 h env maps hH
  · simp only [Bool.and_eq_true] at h
    exact sound ⟨k.1, k.2.1⟩ k.2.2 h.2 env maps (fun c hc => hH c (namedIn_sound hyps k.2.1 hyps (fun _ hx => hx) h.1 c hc))

structure SMachine where
  f : FMMachine
  carried : List Nat               -- maps a request carries
  every : List (Nat × Nat × E)     -- (map, bound key, value): the map at every key
  qflags : List (Nat × List Nat × C) -- (flag variable, bound keys, body): 1 when the body holds at every value of the keys, else 0
  wits : List (Nat × List Nat)     -- (flag variable, its witness variables: one per key)
  facts : List MLaw                -- given about the params and the functions (maps no step writes)
  pfacts : List (MLaw × List Nat)  -- facts about several keys: the fact about its first key, and its further keys

def SMachine.qVars (s : SMachine) : List Nat := s.qflags.map (·.1)
def SMachine.wVars (s : SMachine) : List Nat := s.wits.flatMap (·.2)

/-! The meaning -/

-- The maps a step reads: its own, with the maps the request carries.
def withCarried (s : SMachine) (M κ : Nat → Nat → Nat) : Nat → Nat → Nat := fun mp => if s.carried.contains mp then κ mp else M mp

-- A state with the bound keys read from v.
def atKeys (X : Nat → Nat) (ks : List Nat) (v : Nat → Nat) : Nat → Nat := fun i => if ks.contains i then v i else X i

theorem atKeys_in {X : Nat → Nat} {ks : List Nat} {v : Nat → Nat} {i : Nat} (h : i ∈ ks) : atKeys X ks v i = v i := by
  simp [atKeys, List.contains_iff_mem, h]
theorem atKeys_out {X : Nat → Nat} {ks : List Nat} {v : Nat → Nat} {i : Nat} (h : i ∉ ks) : atKeys X ks v i = X i := by
  simp [atKeys, List.contains_iff_mem, h]

-- Each quantified flag decided: 1 where its body holds at every value of its keys, else 0.
noncomputable def decideQ (s : SMachine) (X : Nat → Nat) (N : Nat → Nat → Nat) : Nat → Nat := fun v =>
  match lookup (fun q => q.1 == v) s.qflags with
  | some q => if ∀ k, holdsC (atKeys X q.2.1 k) N q.2.2 then 1 else 0
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

-- A law at every value of each of some keys.
def holdsOver (l : MLaw) (M : Nat → Nat → Nat) : List Nat → (Nat → Nat) → Prop
  | [], ρ => l.Holds ρ M
  | g :: gs, ρ => ∀ w, holdsOver l M gs (upd ρ g w)

-- The facts about several keys, each at every value of its further keys.
def SMachine.PFacts (s : SMachine) (ρ : Nat → Nat) (M : Nat → Nat → Nat) : Prop := ∀ p ∈ s.pfacts, holdsOver p.1 M p.2 ρ

inductive SReach (s : SMachine) : (Nat → Nat) → (Nat → Nat → Nat) → Prop
  | start (ρ : Nat → Nat) (M : Nat → Nat → Nat) : StartMaps s.f.m M → evalC ρ M s.f.m.pre = true → (∀ l ∈ s.facts, l.Holds ρ M) →
      s.PFacts ρ M → SReach s (applyS s.f.m.init ρ M) M
  | step (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) : SReach s ρ M →
      evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume = true → SReach s (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2

/-! The goals -/

-- Each quantified flag closed, at the tuples the proof names.
def closingHyps (s : SMachine) (qinsts : List (Nat × List E)) : List C :=
  s.qflags.flatMap fun q =>
    [.le (.var q.1) (.const 1)]
      ++ (qinsts.filter (fun p => p.1 == q.1)).map (fun p => .or (.eq (.var q.1) (.const 0)) (substC (q.2.1.zip p.2) q.2.2))
      ++ (match lookup (fun w => w.1 == q.1) s.wits with
          | some w => [.or (.eq (.var q.1) (.const 1)) (.not (substC (q.2.1.zip (w.2.map .var)) q.2.2))]
          | none => [])

def trueC : C := .le (.const 0) (.const 0)
def pairInsts : Nat → List (Nat × E × List E) → List (Nat × E)
  | _, [] => []
  | n, p :: ps => (n, p.2.1) :: pairInsts (n + 1) ps

-- A fact about several keys at a tuple, as a fact about its first key: each further key read as the tuple's term.
def pfactLaw (s : SMachine) (p : Nat × E × List E) : MLaw :=
  match s.pfacts[p.1]? with
  | some f => ⟨substC (f.2.zip p.2.2) f.1.holds, f.1.key⟩
  | none => ⟨trueC, none⟩

-- The facts, at the keys the proof names, and the facts about several keys at the tuples it names.
def factHyps (s : SMachine) (finsts : List (Nat × E)) (pfinsts : List (Nat × E × List E)) : List C :=
  scalarHyps s.facts ++ instHyps s.facts finsts ++ instHyps (pfinsts.map (pfactLaw s)) (pairInsts 0 pfinsts)

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

def sFrameHyps (s : SMachine) (laws : List MLaw) (insts : List (Nat × E)) (qinsts : List (Nat × List E)) (w : C) : List C :=
  scalarHyps laws ++ instHyps laws insts ++ [inlineC s.f.flags s.f.m.assume, w] ++ closingHyps s qinsts

-- The state after a step, named (`names`, per step but the last: each state variable and a fresh variable): the fresh
-- variable equals the variable's term there, and later frames read it (frameSub), so a run's frames stay small.
def nameHyps (n : List (Nat × Nat)) (σ : List (Nat × E)) : List C := n.map (fun p => .eq (.var p.2) ((assoc σ p.1).getD (.var p.1)))

def sRun (s : SMachine) (laws : List MLaw) (insts : List (Nat × E)) (qinsts : List (Nat × List E)) :
    List C → List (List (Nat × Nat)) → List (List (Nat × Nat)) → List (List (Nat × Nat)) → List (Nat × E) → (Nat → E → E) → List C × List (Nat × E) × (Nat → E → E)
  | w :: ws, r :: rs, mr :: mrs, ns, σ, rd =>
    ((sFrameHyps s laws insts qinsts w).map (substRC (frameSub r σ) (frameRd mr rd))
        ++ nameHyps (ns.headD []) (stepSub s.f (frameSub r σ) (frameRd mr rd))
        ++ (sRun s laws insts qinsts ws rs mrs ns.tail (frameSub (ns.headD []) (stepSub s.f (frameSub r σ) (frameRd mr rd))) (stepRdS s (frameSub r σ) (frameRd mr rd))).1,
      (sRun s laws insts qinsts ws rs mrs ns.tail (frameSub (ns.headD []) (stepSub s.f (frameSub r σ) (frameRd mr rd))) (stepRdS s (frameSub r σ) (frameRd mr rd))).2)
  | _, _, _, _, σ, rd => ([], σ, rd)

/-! What a step's goal reads it by -/

-- Values of the keys where a quantified flag's body fails, when there are some.
noncomputable def witnessKeys (X : Nat → Nat) (N : Nat → Nat → Nat) (q : Nat × List Nat × C) : Nat → Nat :=
  if h : ∃ k, ¬ holdsC (atKeys X q.2.1 k) N q.2.2 then Classical.choose h else fun _ => 0

def SMachine.extVars (s : SMachine) : List Nat := s.f.m.inputs ++ s.qVars ++ s.wVars

-- A step's request as its goal reads it: the inputs, each quantified flag's value, each witness.
noncomputable def sReq (s : SMachine) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) : Nat → Nat := fun v =>
  if s.f.m.inputs.contains v then ι v
  else match lookup (fun q => q.1 == v) s.qflags with
    | some _ => decideQ s (withInputs s.f.m.inputs ρ ι) (withCarried s M κ) v
    | none => match lookup (fun w => w.2.contains v) s.wits with
      | some w => match lookup (fun q => q.1 == w.1) s.qflags with
        | some q => match lookup (fun p => p.2 == v) (q.2.1.zip w.2) with
          | some p => witnessKeys (withInputs s.f.m.inputs ρ ι) (withCarried s M κ) q p.1
          | none => 0
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

def distinctPairs (ws : List (Nat × List Nat)) : Bool := distinct (ws.map (·.1)) && distinct (ws.flatMap (·.2))

-- The machine's own side conditions: inputs, flags, quantified flags and witnesses are distinct variables; a body reads no flag, quantified flag or witness, and its keys are none of them
-- and distinct; every quantified flag has a witness per key; the plain flags and the step read no witness.
def sOk (s : SMachine) : Bool :=
  flagsOk s.f.flags && distinct s.qVars && distinctPairs s.wits
    && s.qflags.all (fun q => s.wits.any (fun w => w.1 == q.1 && w.2.length == q.2.1.length) && distinct q.2.1)
    && distinct (s.extVars ++ flagVars s.f.flags)
    && s.qflags.all (fun q => avoids (s.qVars ++ s.wVars ++ flagVars s.f.flags) q.2.2 && q.2.1.all (fun k => !(s.extVars ++ flagVars s.f.flags).contains k))
    && s.f.flags.all (fun p => avoids s.wVars p.2)
    && avoids (s.wVars ++ s.qVars) s.f.m.pre
    && s.f.m.step.all (fun p => avoidsE s.wVars (inlineE s.f.flags p.2))
    && s.f.m.writes.all (fun w => avoidsE s.wVars (inlineE s.f.flags w.2.1) && avoidsE s.wVars (inlineE s.f.flags w.2.2))
    && s.every.all (fun w => avoidsE s.wVars (inlineE s.f.flags w.2.2) && !(s.extVars ++ flagVars s.f.flags).contains w.2.1
        && !(s.f.m.writes.map (·.1)).contains w.1 && !s.carried.contains w.1)
    && avoids s.wVars s.f.m.assume

/-! One step's view -/

theorem lookup_unique {β : Type} {p : Nat × β} {l : List (Nat × β)} (hd : distinct (l.map (·.1)) = true) (hp : p ∈ l) :
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

-- Witnesses: distinct across the flags, each found in its flag's entry, beside its key.
theorem lookup_wit : ∀ {ws : List (Nat × List Nat)}, distinct (ws.flatMap (·.2)) = true → ∀ {w : Nat × List Nat} {v : Nat}, w ∈ ws → v ∈ w.2 →
    lookup (fun w' => w'.2.contains v) ws = some w
  | [], _, _, _, h, _ => by simp at h
  | a :: as, hd, w, v, h, hv => by
    simp only [List.flatMap_cons] at hd
    obtain ⟨_, hd2, hap⟩ := distinct_append hd
    simp only [lookup]
    rcases List.mem_cons.mp h with rfl | h
    · simp [List.contains_iff_mem, hv]
    · have hna : a.2.contains v = false := by
        have : v ∉ a.2 := fun hva => hap v hva (List.mem_flatMap.mpr ⟨w, h, hv⟩)
        simpa [List.contains_iff_mem] using this
      simp only [hna, Bool.false_eq_true, ite_false]
      exact lookup_wit hd2 h hv

theorem distinct_of_flatMap : ∀ {ws : List (Nat × List Nat)}, distinct (ws.flatMap (·.2)) = true → ∀ {w : Nat × List Nat}, w ∈ ws → distinct w.2 = true
  | [], _, _, h => by simp at h
  | a :: as, hd, w, h => by
    simp only [List.flatMap_cons] at hd
    obtain ⟨hd1, hd2, _⟩ := distinct_append hd
    rcases List.mem_cons.mp h with rfl | h
    · exact hd1
    · exact distinct_of_flatMap hd2 h

theorem lookup_zip_wit : ∀ {ks ws : List Nat}, distinct ws = true → ∀ {k w : Nat}, (k, w) ∈ ks.zip ws → lookup (fun p => p.2 == w) (ks.zip ws) = some (k, w)
  | [], _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | a :: as, b :: bs, hd, k, w, h => by
    obtain ⟨hb, hd'⟩ := distinct_cons hd
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    simp only [List.zip_cons_cons, lookup]
    rcases h with ⟨rfl, rfl⟩ | h
    · simp
    · have hw : w ≠ b := fun he => hb (he ▸ (List.of_mem_zip h).2)
      have hbw : (b == w) = false := by simp only [beq_eq_false_iff_ne]; exact fun he => hw he.symm
      simp only [hbw, Bool.false_eq_true, ite_false]
      exact lookup_zip_wit hd' h

-- Distinct keys zipped with variables: each key reads the variable beside it.
theorem assoc_zip_var : ∀ {ks ws : List Nat}, distinct ks = true → ∀ {k w : Nat}, (k, w) ∈ ks.zip ws → assoc (ks.zip (ws.map E.var)) k = some (.var w)
  | [], _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | a :: as, b :: bs, hd, k, w, h => by
    obtain ⟨ha, hd'⟩ := distinct_cons hd
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    simp only [List.map_cons, List.zip_cons_cons, assoc, lookup]
    rcases h with ⟨rfl, rfl⟩ | h
    · simp
    · have hk : k ≠ a := fun he => ha (he ▸ (List.of_mem_zip h).1)
      have hak : (a == k) = false := by simp only [beq_eq_false_iff_ne]; exact fun he => hk he.symm
      simp only [hak, Bool.false_eq_true, ite_false]
      exact assoc_zip_var hd' h

theorem zip_has : ∀ {ks ws : List Nat}, ks.length = ws.length → ∀ {k : Nat}, k ∈ ks → ∃ w, (k, w) ∈ ks.zip ws
  | [], _, _, _, h => by simp at h
  | _ :: _, [], hl, _, _ => by simp at hl
  | a :: as, b :: bs, hl, k, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨b, by simp⟩
    · obtain ⟨w, hw⟩ := zip_has hl h
      exact ⟨w, by simp [List.zip_cons_cons, hw]⟩

-- Terms put in for the keys: the state read at the keys' values.
theorem applyS_zip_atKeys (ks : List Nat) (ts : List E) (X : Nat → Nat) (N : Nat → Nat → Nat) :
    applyS (ks.zip ts) X N = atKeys X ks (applyS (ks.zip ts) X N) := by
  funext i
  simp only [atKeys]
  split
  · rfl
  · rename_i h
    exact applyS_other (fun hm => h (by obtain ⟨⟨a, b⟩, hp, rfl⟩ := List.mem_map.mp hm; exact List.contains_iff_mem.mpr (List.of_mem_zip hp).1)) X N

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
    flagsOk s.f.flags = true ∧ distinct s.qVars = true ∧ distinctPairs s.wits = true
      ∧ (∀ q ∈ s.qflags, (∃ w ∈ s.wits, w.1 = q.1 ∧ w.2.length = q.2.1.length) ∧ distinct q.2.1 = true)
      ∧ distinct (s.extVars ++ flagVars s.f.flags) = true
      ∧ (∀ q ∈ s.qflags, avoids (s.qVars ++ s.wVars ++ flagVars s.f.flags) q.2.2 = true ∧ ∀ k ∈ q.2.1, k ∉ s.extVars ++ flagVars s.f.flags)
      ∧ (∀ p ∈ s.f.flags, avoids s.wVars p.2 = true) := by
  simp only [sOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq, Bool.not_eq_true'] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hf, hq⟩, hw⟩, hcov⟩, hd⟩, hb⟩, hfl⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hs
  refine ⟨hf, hq, hw, fun q hq' => ⟨(hcov q hq').1, (hcov q hq').2⟩, hd, fun q hq' => ⟨(hb q hq').1, fun k hk hm => ?_⟩, hfl⟩
  have h2 := (hb q hq').2 k hk
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
theorem closing_true (hs : sOk s = true) (qinsts : List (Nat × List E)) :
    ∀ c ∈ closingHyps s qinsts, evalC (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ) c = true := by
  obtain ⟨_, hqd, hwd, hcov, _, hbody, _⟩ := sOk_parts s hs
  obtain ⟨hin, hqw⟩ := ext_apart s hs
  have hag := view_agree s ρ M ι κ hs
  intro c hc
  simp only [closingHyps, List.mem_flatMap, List.mem_append, List.mem_singleton, List.mem_map, List.mem_filter] at hc
  obtain ⟨q, hq, hc⟩ := hc
  have hqv : q.1 ∈ s.qVars := List.mem_map_of_mem hq
  -- The flag's value: 1 exactly when the body holds at every value of the keys (read in either view: they agree on the body).
  have hY : withExt s ρ (sReq s ρ M ι κ) q.1 = if ∀ k, holdsC (atKeys (withInputs s.f.m.inputs ρ ι) q.2.1 k) (withCarried s M κ) q.2.2 then 1 else 0 := by
    rw [← hag q.1 (hqw _ hqv)]; simp only [decideQ, lookup_unique hqd hq]
  have hbodyY : ∀ k, holdsC (atKeys (withExt s ρ (sReq s ρ M ι κ)) q.2.1 k) (withCarried s M κ) q.2.2
      ↔ holdsC (atKeys (withInputs s.f.m.inputs ρ ι) q.2.1 k) (withCarried s M κ) q.2.2 := by
    intro k
    rw [← evalC_iff, ← evalC_iff, congrC _ (atKeys (withInputs s.f.m.inputs ρ ι) q.2.1 k) (withCarried s M κ) q.2.2 (fun j hj => by
      simp only [atKeys]; split
      · rfl
      · have hjq : j ∉ s.qVars := fun h => avoids_occ (hbody q hq).1 hj (List.mem_append_left _ (List.mem_append_left _ h))
        have hjw : j ∉ s.wVars := fun h => avoids_occ (hbody q hq).1 hj (List.mem_append_left _ (List.mem_append_right _ h))
        rw [← hag j hjw]; simp only [decideQ]
        rw [lookup_none (fun q' hq' => by simp only [beq_eq_false_iff_ne]; intro he; exact hjq (by rw [← he]; exact List.mem_map_of_mem hq'))])]
  rcases hc with ((rfl | ⟨p, ⟨_, hpq⟩, rfl⟩) | hc)
  · simp only [evalC, evalE, hY]; split <;> simp
  · simp only [beq_iff_eq] at hpq
    simp only [evalC, evalE, Bool.or_eq_true, decide_eq_true_eq]
    by_cases h1 : ∀ k, holdsC (atKeys (withInputs s.f.m.inputs ρ ι) q.2.1 k) (withCarried s M κ) q.2.2
    · right; rw [subst_evalC, applyS_zip_atKeys, evalC_iff]; exact (hbodyY _).mpr (h1 _)
    · left; simp [hY, h1]
  · obtain ⟨⟨w, hw, hwq, hlen⟩, hkd⟩ := hcov q hq
    have hlw : lookup (fun w' => w'.1 == q.1) s.wits = some w := by
      rw [← hwq]; exact lookup_unique (by simp only [distinctPairs, Bool.and_eq_true] at hwd; exact hwd.1) hw
    simp only [hlw, List.mem_singleton] at hc; subst hc
    simp only [evalC, evalE, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    by_cases h1 : ∀ k, holdsC (atKeys (withInputs s.f.m.inputs ρ ι) q.2.1 k) (withCarried s M κ) q.2.2
    · left; simp [hY, h1]
    · right
      have hwd' : distinct (s.wits.flatMap (·.2)) = true := by simp only [distinctPairs, Bool.and_eq_true] at hwd; exact hwd.2
      -- Each witness reads the failing value of the key beside it.
      have hYw : ∀ k x, (k, x) ∈ q.2.1.zip w.2 → withExt s ρ (sReq s ρ M ι κ) x = witnessKeys (withInputs s.f.m.inputs ρ ι) (withCarried s M κ) q k := by
        intro k x hkx
        have hxw : x ∈ s.wVars := List.mem_flatMap.mpr ⟨w, hw, (List.of_mem_zip hkx).2⟩
        have hxi : x ∉ s.f.m.inputs := fun h => (hin _ h).2 hxw
        have hxq : x ∉ s.qVars := fun h => hqw _ h hxw
        have hext : s.extVars.contains x = true := by
          simp only [SMachine.extVars, List.contains_iff_mem, List.mem_append]; exact Or.inr hxw
        have hni : s.f.m.inputs.contains x = false := by simpa [List.contains_iff_mem] using hxi
        simp only [withExt, hext, ite_true, sReq, hni, Bool.false_eq_true, ite_false]
        rw [lookup_none (fun q' hq' => by
          simp only [beq_eq_false_iff_ne]; intro he; exact hxq (by rw [← he]; exact List.mem_map_of_mem hq')),
          lookup_wit hwd' hw (List.of_mem_zip hkx).2]
        simp only [hwq, lookup_unique hqd hq]
        rw [lookup_zip_wit (distinct_of_flatMap hwd' hw) hkx]
      have hex : ∃ k, ¬ holdsC (atKeys (withInputs s.f.m.inputs ρ ι) q.2.1 k) (withCarried s M κ) q.2.2 := by simpa using h1
      have hfail : ¬ holdsC (atKeys (withInputs s.f.m.inputs ρ ι) q.2.1 (witnessKeys (withInputs s.f.m.inputs ρ ι) (withCarried s M κ) q)) (withCarried s M κ) q.2.2 := by
        simp only [witnessKeys, dif_pos hex]; exact Classical.choose_spec hex
      rw [subst_evalC]
      cases hb : evalC (applyS (q.2.1.zip (w.2.map E.var)) (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ)) (withCarried s M κ) q.2.2
      · rfl
      · refine absurd ((hbodyY _).mp ((evalC_iff _ _ _).mp ?_)) hfail
        rw [← hb]
        apply congrC; intro j _
        simp only [atKeys]; split
        · rename_i hj
          obtain ⟨x, hx⟩ := zip_has hlen.symm (List.contains_iff_mem.mp hj)
          simp only [applyS, assoc_zip_var hkd hx, evalE]
          exact (hYw j x hx).symm
        · rename_i hj
          exact (applyS_other (fun hm => hj (by obtain ⟨⟨a, b⟩, hp, rfl⟩ := List.mem_map.mp hm; exact List.contains_iff_mem.mpr (List.of_mem_zip hp).1)) _ _).symm
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

-- A substitution's terms replaced by their values: the same environment at its keys.
theorem assoc_zip_map (f : E → E) (i : Nat) : ∀ (ks : List Nat) (ts : List E), assoc (ks.zip (ts.map f)) i = (assoc (ks.zip ts) i).map f
  | [], _ => by simp [assoc, lookup]
  | _ :: _, [] => by simp [assoc, lookup]
  | k :: ks, t :: ts => by
    have ih := assoc_zip_map f i ks ts
    by_cases h : k = i
    · simp [assoc, lookup, h]
    · simp only [assoc, List.zip_cons_cons, List.map_cons, lookup, beq_iff_eq, h, if_false] at ih ⊢; exact ih

theorem applyS_zip_const (ks : List Nat) (ts : List E) (V X : Nat → Nat) (N : Nat → Nat → Nat) (i : Nat) (h : V i = X i) :
    applyS (ks.zip ts) V N i = applyS (ks.zip (ts.map (fun t => E.const (evalE V N t)))) X N i := by
  simp only [applyS, assoc_zip_map]
  cases assoc (ks.zip ts) i <;> simp [evalE, h]

-- A frame's hypothesis is one of the frame without the flags' instances, or an instance of a flag.
theorem sframe_mem (s : SMachine) (laws : List MLaw) (insts : List (Nat × E)) (qinsts : List (Nat × List E)) (w c : C)
    (hc : c ∈ sFrameHyps s laws insts qinsts w) :
    c ∈ sFrameHyps s laws insts [] w ∨ ∃ q ∈ s.qflags, ∃ p ∈ qinsts, c = .or (.eq (.var q.1) (.const 0)) (substC (q.2.1.zip p.2) q.2.2) := by
  rcases List.mem_append.mp hc with h | h
  · exact Or.inl (List.mem_append_left _ h)
  · obtain ⟨q, hq, h⟩ := List.mem_flatMap.mp h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inl (List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, List.mem_append_left _ (List.mem_append_left _ h)⟩))
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        exact Or.inr ⟨q, hq, p, (List.mem_filter.mp hp).1, rfl⟩
    · exact Or.inl (List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, List.mem_append_right _ h⟩))

section frame2
variable (s : SMachine) (Z MZ : List Nat) (W : Nat → Nat) (M0 : Nat → Nat → Nat)

-- Every hypothesis of a frame holds where the frame is read, given the laws in the goal's view of its state.
theorem sframe_hyps (hs : sOk s = true) (laws : List MLaw) (insts : List (Nat × E)) (qinsts : List (Nat × List E))
    {σ : List (Nat × E)} {rd : Nat → E → E} {ρ : Nat → Nat} {M : Nat → Nat → Nat} {r mr : List (Nat × Nat)} {ι : Nat → Nat} {κ : Nat → Nat → Nat} {w : C}
    (hlY : ∀ l ∈ laws, l.Holds (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ))
    (hH : SHead s Z MZ W M0 σ rd ρ M r mr ι κ)
    (hav : ∀ c ∈ sFrameHyps s laws insts [] w, avoids Z c = true)
    (hqb : ∀ q ∈ s.qflags, avoids Z q.2.2 = true)
    (havm : ∀ c ∈ sFrameHyps s laws insts qinsts w, avoidsMaps MZ c = true)
    (hA : evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume = true)
    (hW : evalC (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ) w = true) :
    ∀ c ∈ sFrameHyps s laws insts qinsts w, evalC W M0 (substRC (frameSub r σ) (frameRd mr rd) c) = true := by
  obtain ⟨hX, hrd⟩ := hH
  intro c hc
  rw [substR_evalC_on (frameSub r σ) (frameRd mr rd) W M0 (withCarried s M κ) MZ hrd c (havm c hc)]
  rcases sframe_mem s laws insts qinsts w c hc with hc | ⟨q, hq, p, _, rfl⟩
  · rw [congrC _ (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ) c (fun i hi => hX i (avoids_occ (hav c hc) hi))]
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
    · exact closing_true s ρ M ι κ hs [] c hc
  · -- A flag's instance: its keys' terms may read the zone (a later step's names), the flag and its body don't. Read
    -- in the frame it is the instance at the keys' values read in the step's view, which holds there.
    have hq1 : q.1 ∉ Z := by
      have hle : C.le (.var q.1) (.const 1) ∈ sFrameHyps s laws insts [] w :=
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton.mpr rfl))⟩)
      exact avoids_occ (hav _ hle) (by simp [occC, occE])
    let ks := p.2.map (fun t => E.const (evalE (applyS (frameSub r σ) W M0) (withCarried s M κ) t))
    have hc' := closing_true s ρ M ι κ hs [(q.1, ks)] (.or (.eq (.var q.1) (.const 0)) (substC (q.2.1.zip ks) q.2.2))
      (List.mem_flatMap.mpr ⟨q, hq, List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨(q.1, ks), List.mem_filter.mpr ⟨List.mem_singleton.mpr rfl, by simp⟩, rfl⟩))⟩)
    have heq : evalC (applyS (frameSub r σ) W M0) (withCarried s M κ) (.or (.eq (.var q.1) (.const 0)) (substC (q.2.1.zip p.2) q.2.2))
        = evalC (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ) (.or (.eq (.var q.1) (.const 0)) (substC (q.2.1.zip ks) q.2.2)) := by
      simp only [evalC, evalE, subst_evalC, hX q.1 hq1]
      rw [congrC _ _ _ q.2.2 (fun i hi => applyS_zip_const q.2.1 p.2 _ _ _ i (hX i (avoids_occ (hqb q hq) hi)))]
      rfl
    rw [heq]; exact hc'

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
  keys2 : List Nat            -- a law about every two keys or more: its further keys, variables nothing but laws about them read
  insts : List (Nat × E)      -- (law index, key): where the step goal assumes the laws about every key
  qinsts : List (Nat × List E) -- (quantified flag, keys): where the step goal closes it
  finsts : List (Nat × E)     -- (fact index, key): where both goals assume the facts
  pinsts : List (Nat × E × List E) -- (law index, key, further keys): where the step goal assumes the laws about several keys
  pfinsts : List (Nat × E × List E) -- (fact index, key, further keys): where both goals assume the facts about several keys
  start : Cert
  step : Cert

-- What an entry claims: its law, at every value of each further key.
def SEntry.Holds (e : SEntry) (ρ : Nat → Nat) (M : Nat → Nat → Nat) : Prop := holdsOver e.law M e.keys2 ρ

-- A law about several keys at a tuple, as a law about every first key: each further key read as the tuple's term.
def pairLaws (ps : List SEntry) (pinsts : List (Nat × E × List E)) : List MLaw := pinsts.map fun p =>
  match ps[p.1]? with
  | some e => ⟨substC (e.keys2.zip p.2.2) e.law.holds, e.law.key⟩
  | none => ⟨trueC, none⟩
-- The laws a frame assumes (the entries' laws, then each pair's) and where (each pair's at its first term).
def sLaws (ps : List SEntry) (pinsts : List (Nat × E × List E)) : List MLaw := ps.map (·.law) ++ pairLaws ps pinsts
def sInsts (ps : List SEntry) (insts : List (Nat × E)) (pinsts : List (Nat × E × List E)) : List (Nat × E) := insts ++ pairInsts ps.length pinsts
def sStartGoal (s : SMachine) (e : SEntry) : List C := [s.f.m.pre] ++ factHyps s e.finsts e.pfinsts ++ [.not (substRC s.f.m.init (rdStart s.f.m) (goalOf e.law e.sk))]
def sStepGoal (s : SMachine) (ps : List SEntry) (e : SEntry) : List C :=
  [s.f.m.pre] ++ factHyps s e.finsts e.pfinsts ++ (sFrameHyps s (sLaws ps e.pinsts) (sInsts ps e.insts e.pinsts) e.qinsts trueC).map (substRC (frameSub [] []) (frameRd [] getRd))
    ++ [.not (substRC (stepSub s.f (frameSub [] []) (frameRd [] getRd)) (stepRdS s (frameSub [] []) (frameRd [] getRd)) (goalOf e.law e.sk))]

-- The machine's terms and the zone a frame keeps apart (the flags, and here the skolem).
def sTermsOk (s : SMachine) (Z : List Nat) : Bool :=
  s.f.flags.all (fun p => avoids Z p.2)
    && s.f.m.step.all (fun p => avoidsE (Z ++ s.wVars) (inlineE s.f.flags p.2))
    && s.f.m.writes.all (fun w => avoidsE (Z ++ s.wVars) (inlineE s.f.flags w.2.1) && avoidsE (Z ++ s.wVars) (inlineE s.f.flags w.2.2) && !s.carried.contains w.1)
    && s.every.all (fun w => avoidsE (Z ++ s.wVars) (inlineE s.f.flags w.2.2) && !Z.contains w.2.1 && !(flagVars s.f.flags).contains w.2.1
        && s.f.flags.all (fun p => !occC w.2.1 p.2) && !s.carried.contains w.1 && !(s.f.m.writes.map (·.1)).contains w.1)
    && s.facts.all (fun l => avoids Z l.holds) && s.pfacts.all (fun f => avoids Z f.1.holds)

-- The facts read the params and the functions alone: no request, flag or state variable, and no map a step writes or
-- a request carries.
def factsOk1 (s : SMachine) : Bool :=
  s.facts.all fun l => avoids (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)) l.holds
    && avoidsMaps (s.carried ++ s.every.map (·.1) ++ s.f.m.writes.map (·.1)) l.holds
-- The facts about several keys alike, each about a first key apart from its further keys.
def pfactsOk (s : SMachine) : Bool :=
  s.pfacts.all fun f => avoids (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)) f.1.holds
    && avoidsMaps (s.carried ++ s.every.map (·.1) ++ s.f.m.writes.map (·.1)) f.1.holds && f.2.all (fun g => f.1.key != some g)
def factsOk (s : SMachine) : Bool := factsOk1 s && pfactsOk s

-- The skolem is fresh for the machine: no flag, body, assumption, term or write reads it, nor binds it.
def skFresh (s : SMachine) (sk : Nat) : Bool :=
  s.f.flags.all (fun p => !occC sk p.2) && s.qflags.all (fun q => !occC sk q.2.2) && !occC sk s.f.m.assume
    && s.f.m.step.all (fun p => !occE sk p.2) && s.f.m.writes.all (fun w => !occE sk w.2.1 && !occE sk w.2.2)
    && s.every.all (fun w => !occE sk w.2.2 && w.2.1 != sk) && s.facts.all (fun l => !occC sk l.holds)
    && s.pfacts.all (fun f => !occC sk f.1.holds)

-- Further keys: each fresh as a skolem is, not the law's own key, read by no law but those about it, and no entry's skolem.
def key2Ok (s : SMachine) (ps : List SEntry) (e : SEntry) : Bool :=
  e.keys2.all fun g => e.law.key != some g && skFresh s g && !(s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains g
    && !occC g s.f.m.pre && s.f.m.init.all (fun p => !occE g p.2)
    && ps.all (fun e' => (!occC g e'.law.holds || e'.keys2.contains g) && e'.sk != g)

def checkSMachine (s : SMachine) (ps : List SEntry) : Bool :=
  sOk s && avoids (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)) s.f.m.pre && !readsC s.f.m.pre
    && sTermsOk s (flagVars s.f.flags) && factsOk s
    && ps.all fun e =>
      avoids (s.extVars ++ flagVars s.f.flags) e.law.holds && avoidsMaps s.carried e.law.holds
        && !(s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains e.sk
        && ps.all (fun e' => !occC e.sk e'.law.holds) && !occC e.sk s.f.m.pre && s.f.m.init.all (fun p => !occE e.sk p.2)
        && skFresh s e.sk && key2Ok s ps e
        && checkIn (sStartGoal s e) e.start
        && checkIn (sStepGoal s ps e) e.step

theorem skFresh_parts {s : SMachine} {sk : Nat} (h : skFresh s sk = true) :
    (∀ p ∈ s.f.flags, occC sk p.2 = false) ∧ (∀ q ∈ s.qflags, occC sk q.2.2 = false) ∧ occC sk s.f.m.assume = false
      ∧ (∀ p ∈ s.f.m.step, occE sk p.2 = false) ∧ (∀ w ∈ s.f.m.writes, occE sk w.2.1 = false ∧ occE sk w.2.2 = false)
      ∧ (∀ w ∈ s.every, occE sk w.2.2 = false ∧ w.2.1 ≠ sk) ∧ (∀ l ∈ s.facts, occC sk l.holds = false) := by
  simp only [skFresh, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, _⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem skFresh_pfacts {s : SMachine} {sk : Nat} (h : skFresh s sk = true) : ∀ f ∈ s.pfacts, occC sk f.1.holds = false := by
  simp only [skFresh, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h; exact h.2

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
      have hiff : ∀ k, holdsC (atKeys (upd X x v) q.2.1 k) N q.2.2 ↔ holdsC (atKeys X q.2.1 k) N q.2.2 := fun k => by
        rw [← evalC_iff, ← evalC_iff, congrC _ (atKeys X q.2.1 k) N q.2.2 (fun i hi => by
          have hix : i ≠ x := fun h => by rw [h, hbq] at hi; cases hi
          simp only [atKeys]; split
          · rfl
          · simp [upd, hix])]
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
  obtain ⟨⟨⟨⟨⟨hf, hst⟩, hwr⟩, hev⟩, _⟩, _⟩ := h
  refine ⟨hf, hst, fun w hw => ⟨⟨(hwr w hw).1.1, (hwr w hw).1.2⟩, by simpa using (hwr w hw).2⟩, fun w hw => ?_⟩
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hev w hw
  exact ⟨h1, by simpa using h2, by simpa using h3, fun p hp => by simpa using h4 p hp, by simpa using h5, by simpa using h6⟩

-- The precondition holds in every reachable state: it reads the params alone.
theorem pre_sreach (s : SMachine) (hp : avoids (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)) s.f.m.pre = true)
    (hr : readsC s.f.m.pre = false) : ∀ {ρ M}, SReach s ρ M → evalC ρ M s.f.m.pre = true := by
  intro ρ M h
  induction h with
  | start ρ M _ h0 _ _ =>
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

-- The facts hold in every reachable state: a run starts where they hold, and no step moves what they read.
theorem facts_sreach (s : SMachine) (hf : factsOk s = true) : ∀ {ρ M}, SReach s ρ M → ∀ l ∈ s.facts, l.Holds ρ M := by
  simp only [factsOk, Bool.and_eq_true] at hf
  have hf := hf.1
  simp only [factsOk1, List.all_eq_true, Bool.and_eq_true] at hf
  intro ρ M h
  induction h with
  | start ρ M _ _ hfa _ =>
    intro l hl
    exact holds_transfer l (hf l hl).1 (MS := []) (by simp [avoidsMaps])
      (fun i hi => applyS_other (fun h => hi (by simp [h])) ρ M) (fun _ _ => rfl) (hfa l hl)
  | step ρ M ι κ _ _ ih =>
    intro l hl
    refine holds_transfer l (hf l hl).1 (hf l hl).2 (fun i hi => ?_) (fun mp hmp => ?_) (ih l hl)
    · simp only [sNext, sView]
      rw [applyS_other (fun h => hi (by simp [h])), decide_other (fun h => hi (by simp [h]))]
      simp only [decideQ]
      rw [lookup_none (fun q hq => by
        simp only [beq_eq_false_iff_ne]; intro he
        exact hi (by simp only [SMachine.extVars, SMachine.qVars, List.mem_append, List.mem_map]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, he⟩))))))]
      exact withInputs_other (fun h => hi (by simp only [SMachine.extVars, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))) ρ ι
    · simp only [List.mem_append, not_or] at hmp
      obtain ⟨⟨hmc, hme⟩, hmw⟩ := hmp
      funext key
      simp only [sNext, sView, everyMaps]
      rw [lookup_none (fun w hw => by simp only [beq_eq_false_iff_ne]; intro he; exact hme (by rw [← he]; exact List.mem_map_of_mem hw))]
      simp only [writeMaps]
      rw [lookup_none (fun w hw => by simp only [beq_eq_false_iff_ne]; intro he; exact hmw (by rw [← he]; exact List.mem_map_of_mem hw))]
      simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmc)]

theorem sTermsOk_facts {s : SMachine} {Z : List Nat} (h : sTermsOk s Z = true) : ∀ l ∈ s.facts, avoids Z l.holds = true := by
  simp only [sTermsOk, Bool.and_eq_true, List.all_eq_true] at h; exact h.1.2
theorem sTermsOk_pfacts {s : SMachine} {Z : List Nat} (h : sTermsOk s Z = true) : ∀ f ∈ s.pfacts, avoids Z f.1.holds = true := by
  simp only [sTermsOk, Bool.and_eq_true, List.all_eq_true] at h; exact h.2

-- The facts hold wherever the variables and maps they may read are the state's: away from the request, the flags, the
-- state and the zone Vx, and from the maps a step writes, a request carries and the zone Mx.
theorem facts_frame (s : SMachine) (hfok : factsOk s = true) (Vx Mx : List Nat)
    (hvx : ∀ l ∈ s.facts, avoids Vx l.holds = true) (hmx : ∀ l ∈ s.facts, avoidsMaps Mx l.holds = true)
    {ρ : Nat → Nat} {M : Nat → Nat → Nat} {X : Nat → Nat} {N : Nat → Nat → Nat}
    (hX : ∀ i, i ∉ s.extVars → i ∉ Vx → X i = ρ i) (hN : ∀ mp, mp ∉ s.carried → mp ∉ Mx → N mp = M mp)
    (hl : ∀ l ∈ s.facts, l.Holds ρ M) : ∀ l ∈ s.facts, l.Holds X N := by
  simp only [factsOk, Bool.and_eq_true] at hfok
  have hfok := hfok.1
  simp only [factsOk1, List.all_eq_true, Bool.and_eq_true] at hfok
  intro l hl'
  refine holds_transfer (V := (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)) ++ Vx)
    (MS := (s.carried ++ s.every.map (·.1) ++ s.f.m.writes.map (·.1)) ++ Mx) l
    (by simp only [avoids, List.all_append, Bool.and_eq_true] at hfok hvx ⊢; exact ⟨(hfok l hl').1, hvx l hl'⟩)
    (by simp only [avoidsMaps, List.all_append, Bool.and_eq_true] at hfok hmx ⊢; exact ⟨(hfok l hl').2, hmx l hl'⟩)
    (fun i hi => hX i (fun h => hi (by simp [h])) (fun h => hi (by simp [h])))
    (fun mp hmp => hN mp (fun h => hmp (by simp [h])) (fun h => hmp (by simp [h]))) (hl l hl')

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

theorem sOk_of {s : SMachine} {ps : List SEntry} (hl : checkSMachine s ps = true) : sOk s = true := by
  simp only [checkSMachine, Bool.and_eq_true] at hl; exact hl.1.1.1.1.1

theorem spre_parts {s : SMachine} {ps : List SEntry} (hl : checkSMachine s ps = true) :
    avoids (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)) s.f.m.pre = true ∧ readsC s.f.m.pre = false := by
  simp only [checkSMachine, Bool.and_eq_true] at hl; exact ⟨hl.1.1.1.1.2, by simpa using hl.1.1.1.2⟩

theorem sfacts_ok {s : SMachine} {ps : List SEntry} (hl : checkSMachine s ps = true) : factsOk s = true := by
  simp only [checkSMachine, Bool.and_eq_true] at hl; exact hl.1.2

theorem slaws_avoid {s : SMachine} {ps : List SEntry} (hl : checkSMachine s ps = true) :
    ∀ l ∈ ps.map (·.law), avoids s.extVars l.holds = true ∧ avoidsMaps s.carried l.holds = true := by
  simp only [checkSMachine, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hl
  intro l hl'
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp hl'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hl.2 e' he'
  refine ⟨?_, h2⟩
  simp only [avoids, List.all_append, Bool.and_eq_true] at h1 ⊢; exact h1.1

/-! Entries, read at states -/

theorem upd_self (ρ : Nat → Nat) (x : Nat) : upd ρ x (ρ x) = ρ := funext fun i => by simp only [upd]; split <;> simp_all
theorem upd_upd_same (ρ : Nat → Nat) (x u w : Nat) : upd (upd ρ x u) x w = upd ρ x w := funext fun i => by simp only [upd]; split <;> rfl
theorem upd_comm (ρ : Nat → Nat) {x y : Nat} (h : x ≠ y) (u w : Nat) : upd (upd ρ x u) y w = upd (upd ρ y w) x u := funext fun i => by
  simp only [upd]; by_cases hy : i = y <;> by_cases hx : i = x <;> simp_all

-- An entry holds exactly where its law holds at every state that agrees with the state but at the further keys.
theorem holdsOver_any {l : MLaw} {M : Nat → Nat → Nat} : ∀ (gs : List Nat) {Y : Nat → Nat}, holdsOver l M gs Y → ∀ Z, Agree gs Z Y → l.Holds Z M
  | [], Y, h, Z, hag => by
    have hZ : Z = Y := funext fun i => hag i (by simp)
    subst hZ; exact h
  | g :: gs, Y, h, Z, hag => holdsOver_any gs (h (Z g)) Z (fun i hi => by
      simp only [upd]; split
      · rename_i hig; subst hig; rfl
      · rename_i hig; exact hag i (by simp only [List.mem_cons, not_or]; exact ⟨hig, hi⟩))

theorem holdsOver_of_any {l : MLaw} {M : Nat → Nat → Nat} : ∀ (gs : List Nat) {Y : Nat → Nat}, (∀ Z, Agree gs Z Y → l.Holds Z M) → holdsOver l M gs Y
  | [], Y, h => h Y (fun _ _ => rfl)
  | g :: gs, Y, h => by
    intro w
    exact holdsOver_of_any gs (fun Z hag => h Z (fun i hi => by
      simp only [List.mem_cons, not_or] at hi
      rw [hag i hi.2]; simp only [upd, if_neg hi.1]))

theorem SEntry.holds_law {e : SEntry} {ρ : Nat → Nat} {M : Nat → Nat → Nat} (h : e.Holds ρ M) : e.law.Holds ρ M :=
  holdsOver_any e.keys2 h ρ (fun _ _ => rfl)

-- An entry read where its law reads alike holds alike (at every value of its further keys).
theorem sentry_transfer {V MS : List Nat} {e : SEntry} (hv : avoids V e.law.holds = true) (hm : avoidsMaps MS e.law.holds = true)
    {ρ ρ' : Nat → Nat} {M M' : Nat → Nat → Nat} (hag : Agree V ρ ρ') (hmag : ∀ mp, mp ∉ MS → M mp = M' mp) : e.Holds ρ' M' → e.Holds ρ M := by
  intro h
  apply holdsOver_of_any
  intro Z hZ
  have h' := holdsOver_any e.keys2 h (fun i => if i ∈ e.keys2 then Z i else ρ' i) (fun i hi => by simp [hi])
  exact holds_transfer e.law hv hm (fun i hiV => by
    by_cases hk : i ∈ e.keys2
    · simp [hk]
    · simp only [hk, if_false]; rw [hZ i hk]; exact hag i hiV) hmag h'

-- Setting a variable the law reads nowhere, or one of its further keys, keeps the entry.
theorem sentry_upd {e : SEntry} {x : Nat} (hx : occC x e.law.holds = false ∨ x ∈ e.keys2) {ρ : Nat → Nat} {M : Nat → Nat → Nat} (u : Nat) :
    e.Holds ρ M → e.Holds (upd ρ x u) M := by
  intro h
  apply holdsOver_of_any
  intro Z hZ
  rcases hx with hx | hx
  · have h' := holdsOver_any e.keys2 h (upd Z x (ρ x)) (fun i hi => by
      simp only [upd]; split
      · rename_i hix; subst hix; rfl
      · rename_i hix; rw [hZ i hi]; simp only [upd, if_neg hix])
    exact holds_transfer (V := [x]) (MS := []) e.law (by simp [avoids, hx]) (by simp [avoidsMaps])
      (fun i hi => by simp only [upd]; rw [if_neg (by simpa using hi)]) (fun _ _ => rfl) h'
  · exact holdsOver_any e.keys2 h Z (fun i hi => by
      rw [hZ i hi]; simp only [upd]; rw [if_neg (fun h' => hi (by rw [h']; exact hx))])

-- Each tuple's law holds wherever every entry does (the law's own key none of its further keys).
theorem pairLaws_hold (ps : List SEntry) (pinsts : List (Nat × E × List E)) (hkk : ∀ e ∈ ps, ∀ k, e.law.key = some k → k ∉ e.keys2)
    {Y : Nat → Nat} {N : Nat → Nat → Nat} (hall : ∀ e ∈ ps, e.Holds Y N) : ∀ l ∈ pairLaws ps pinsts, l.Holds Y N := by
  have htrue : (⟨trueC, none⟩ : MLaw).Holds Y N := by simp [MLaw.Holds, trueC, evalC, evalE]
  intro l hl
  simp only [pairLaws, List.mem_map] at hl
  obtain ⟨p, _, rfl⟩ := hl
  split
  · rename_i e he
    have hem : e ∈ ps := List.mem_of_getElem? he
    have hany := holdsOver_any e.keys2 (hall e hem)
    have hdom : ∀ i, i ∉ e.keys2 → i ∉ (e.keys2.zip p.2.2).map (·.1) := fun i hi hm => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm; exact hi (List.of_mem_zip hq).1
    cases hk : e.law.key with
    | none =>
      have h' := hany (applyS (e.keys2.zip p.2.2) Y N) (fun i hi => applyS_other (hdom i hi) Y N)
      simp only [MLaw.Holds, hk] at h' ⊢
      rw [subst_evalC]; exact h'
    | some k =>
      have hkg := hkk e hem k hk
      simp only [MLaw.Holds, hk]
      intro v
      rw [subst_evalC]
      have h' := hany (fun i => if i ∈ e.keys2 then applyS (e.keys2.zip p.2.2) (upd Y k v) N i else Y i) (fun i hi => by simp [hi])
      simp only [MLaw.Holds, hk] at h'
      have hZ : upd (fun i => if i ∈ e.keys2 then applyS (e.keys2.zip p.2.2) (upd Y k v) N i else Y i) k v = applyS (e.keys2.zip p.2.2) (upd Y k v) N := by
        funext i
        by_cases hik : i = k
        · subst hik; simp only [upd, if_true]; rw [applyS_other (hdom i hkg)]; simp [upd]
        · simp only [upd, if_neg hik]
          by_cases hi : i ∈ e.keys2
          · simp [hi]
          · simp only [hi, if_false]; rw [applyS_other (hdom i hi)]; simp [upd, hik]
      rw [← hZ]; exact h' v
  · exact htrue

/-! Facts about several keys -/

-- A law at every value of some keys, read where it reads alike, holds alike.
theorem holdsOver_transfer {V MS : List Nat} (l : MLaw) (hv : avoids V l.holds = true) (hm : avoidsMaps MS l.holds = true) :
    ∀ (gs : List Nat) {ρ ρ' : Nat → Nat} {M M' : Nat → Nat → Nat}, Agree V ρ ρ' → (∀ mp, mp ∉ MS → M mp = M' mp) →
      holdsOver l M' gs ρ' → holdsOver l M gs ρ
  | [], _, _, _, _, hag, hmag, h => holds_transfer l hv hm hag hmag h
  | g :: gs, ρ, ρ', _, _, hag, hmag, h => fun w =>
      holdsOver_transfer l hv hm gs (ρ := upd ρ g w) (ρ' := upd ρ' g w) (fun i hi => by
        simp only [upd]; split
        · rfl
        · exact hag i hi) hmag (h w)

-- A law at every value of its further keys holds with each set to a term (the law about its first key, at the tuple).
theorem holdsOver_subst (l : MLaw) (gs : List Nat) (ts : List E) (hkk : ∀ k, l.key = some k → k ∉ gs)
    {Y : Nat → Nat} {N : Nat → Nat → Nat} (h : holdsOver l N gs Y) : (⟨substC (gs.zip ts) l.holds, l.key⟩ : MLaw).Holds Y N := by
  have hany := holdsOver_any gs h
  have hdom : ∀ i, i ∉ gs → i ∉ (gs.zip ts).map (·.1) := fun i hi hm => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm; exact hi (List.of_mem_zip hq).1
  cases hk : l.key with
  | none =>
    have h' := hany (applyS (gs.zip ts) Y N) (fun i hi => applyS_other (hdom i hi) Y N)
    simp only [MLaw.Holds, hk] at h' ⊢
    rw [subst_evalC]; exact h'
  | some k =>
    have hkg := hkk k hk
    simp only [MLaw.Holds, hk]
    intro v
    rw [subst_evalC]
    have h' := hany (fun i => if i ∈ gs then applyS (gs.zip ts) (upd Y k v) N i else Y i) (fun i hi => by simp [hi])
    simp only [MLaw.Holds, hk] at h'
    have hZ : upd (fun i => if i ∈ gs then applyS (gs.zip ts) (upd Y k v) N i else Y i) k v = applyS (gs.zip ts) (upd Y k v) N := by
      funext i
      by_cases hik : i = k
      · subst hik; simp only [upd, if_true]; rw [applyS_other (hdom i hkg)]; simp [upd]
      · simp only [upd, if_neg hik]
        by_cases hi : i ∈ gs
        · simp [hi]
        · simp only [hi, if_false]; rw [applyS_other (hdom i hi)]; simp [upd, hik]
    rw [← hZ]; exact h' v

theorem pfactsOk_parts {s : SMachine} (h : factsOk s = true) : ∀ f ∈ s.pfacts,
    avoids (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)) f.1.holds = true
      ∧ avoidsMaps (s.carried ++ s.every.map (·.1) ++ s.f.m.writes.map (·.1)) f.1.holds = true ∧ ∀ k, f.1.key = some k → k ∉ f.2 := by
  simp only [factsOk, pfactsOk, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
  intro f hf
  obtain ⟨⟨h1, h2⟩, h3⟩ := h.2 f hf
  exact ⟨h1, h2, fun k hk hm => h3 k hm (by rw [hk])⟩

-- The facts about several keys at the tuples a goal names hold wherever the facts do.
theorem pfactLaws_hold (s : SMachine) (pfinsts : List (Nat × E × List E)) (hkk : ∀ f ∈ s.pfacts, ∀ k, f.1.key = some k → k ∉ f.2)
    {Y : Nat → Nat} {N : Nat → Nat → Nat} (hp : s.PFacts Y N) : ∀ l ∈ pfinsts.map (pfactLaw s), l.Holds Y N := by
  intro l hl
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hl
  unfold pfactLaw
  split
  · rename_i f hf
    have hfm : f ∈ s.pfacts := List.mem_of_getElem? hf
    exact holdsOver_subst f.1 f.2 p.2.2 (hkk f hfm) (hp f hfm)
  · simp [MLaw.Holds, trueC, evalC, evalE]

-- A goal's facts all hold where the facts and the facts about several keys do.
theorem facthyps_true (s : SMachine) (finsts : List (Nat × E)) (pfinsts : List (Nat × E × List E)) (Y : Nat → Nat) (N : Nat → Nat → Nat)
    (hkk : ∀ f ∈ s.pfacts, ∀ k, f.1.key = some k → k ∉ f.2) (hf : ∀ l ∈ s.facts, l.Holds Y N) (hp : s.PFacts Y N) :
    ∀ c ∈ factHyps s finsts pfinsts, evalC Y N c = true := by
  intro c hc
  simp only [factHyps] at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact laws_hyps_true s.facts finsts Y N hf c hc
  · exact laws_hyps_true (pfinsts.map (pfactLaw s)) (pairInsts 0 pfinsts) Y N (pfactLaws_hold s pfinsts hkk hp) c (List.mem_append_right _ hc)

-- The facts about several keys hold in every reachable state, and wherever what they read is the state's.
theorem pfacts_sreach (s : SMachine) (hf : factsOk s = true) : ∀ {ρ M}, SReach s ρ M → s.PFacts ρ M := by
  have hf := pfactsOk_parts hf
  intro ρ M h
  induction h with
  | start ρ M _ _ _ hpf =>
    intro f hfm
    exact holdsOver_transfer f.1 (hf f hfm).1 (MS := []) (by simp [avoidsMaps]) f.2
      (fun i hi => applyS_other (fun h => hi (by simp [h])) ρ M) (fun _ _ => rfl) (hpf f hfm)
  | step ρ M ι κ _ _ ih =>
    intro f hfm
    refine holdsOver_transfer f.1 (hf f hfm).1 (hf f hfm).2.1 f.2 (fun i hi => ?_) (fun mp hmp => ?_) (ih f hfm)
    · simp only [sNext, sView]
      rw [applyS_other (fun h => hi (by simp [h])), decide_other (fun h => hi (by simp [h]))]
      simp only [decideQ]
      rw [lookup_none (fun q hq => by
        simp only [beq_eq_false_iff_ne]; intro he
        exact hi (by simp only [SMachine.extVars, SMachine.qVars, List.mem_append, List.mem_map]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, he⟩))))))]
      exact withInputs_other (fun h => hi (by simp only [SMachine.extVars, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))) ρ ι
    · simp only [List.mem_append, not_or] at hmp
      obtain ⟨⟨hmc, hme⟩, hmw⟩ := hmp
      funext key
      simp only [sNext, sView, everyMaps]
      rw [lookup_none (fun w hw => by simp only [beq_eq_false_iff_ne]; intro he; exact hme (by rw [← he]; exact List.mem_map_of_mem hw))]
      simp only [writeMaps]
      rw [lookup_none (fun w hw => by simp only [beq_eq_false_iff_ne]; intro he; exact hmw (by rw [← he]; exact List.mem_map_of_mem hw))]
      simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmc)]

theorem pfacts_frame (s : SMachine) (hfok : factsOk s = true) (Vx Mx : List Nat)
    (hvx : ∀ f ∈ s.pfacts, avoids Vx f.1.holds = true) (hmx : ∀ f ∈ s.pfacts, avoidsMaps Mx f.1.holds = true)
    {ρ : Nat → Nat} {M : Nat → Nat → Nat} {X : Nat → Nat} {N : Nat → Nat → Nat}
    (hX : ∀ i, i ∉ s.extVars → i ∉ Vx → X i = ρ i) (hN : ∀ mp, mp ∉ s.carried → mp ∉ Mx → N mp = M mp)
    (hl : s.PFacts ρ M) : s.PFacts X N := by
  have hp := pfactsOk_parts hfok
  intro f hf'
  refine holdsOver_transfer (V := (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)) ++ Vx)
    (MS := (s.carried ++ s.every.map (·.1) ++ s.f.m.writes.map (·.1)) ++ Mx) f.1
    (by have h1 := (hp f hf').1; simp only [avoids, List.all_append, Bool.and_eq_true] at hvx h1 ⊢; exact ⟨h1, hvx f hf'⟩)
    (by have h2 := (hp f hf').2.1; simp only [avoidsMaps, List.all_append, Bool.and_eq_true] at hmx h2 ⊢; exact ⟨h2, hmx f hf'⟩) f.2
    (fun i hi => hX i (fun h => hi (by simp [h])) (fun h => hi (by simp [h])))
    (fun mp hmp => hN mp (fun h => hmp (by simp [h])) (fun h => hmp (by simp [h]))) (hl f hf')

-- A variable fresh as a skolem: setting it commutes with a step's view and with the step.
theorem fresh_parts {s : SMachine} {x : Nat} (hf : skFresh s x = true)
    (hc : (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains x = false) (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) (v : Nat) :
    sNext s (upd ρ x v) M ι κ = (upd (sNext s ρ M ι κ).1 x v, (sNext s ρ M ι κ).2)
      ∧ sView s (upd ρ x v) M ι κ = (upd (sView s ρ M ι κ).1 x v, (sView s ρ M ι κ).2)
      ∧ x ∉ s.f.m.init.map (·.1) := by
  obtain ⟨hf1, hf2, _, hf4, hf5, hf6, _⟩ := skFresh_parts hf
  have hnot : x ∉ s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1) := fun hm => by
    rw [List.contains_iff_mem.mpr hm] at hc; cases hc
  have hE : x ∉ s.extVars := fun hm => hnot (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hm)))
  have hF : x ∉ flagVars s.f.flags := fun hm => hnot (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hm)))
  have hS : x ∉ s.f.m.step.map (·.1) := fun hm => hnot (List.mem_append_right _ hm)
  have hI : x ∉ s.f.m.init.map (·.1) := fun hm => hnot (List.mem_append_left _ (List.mem_append_right _ hm))
  have hi : x ∉ s.f.m.inputs := fun hm => hE (by simp only [SMachine.extVars, List.mem_append]; exact Or.inl (Or.inl hm))
  have hq : x ∉ s.qVars := fun hm => hE (by simp only [SMachine.extVars, List.mem_append]; exact Or.inl (Or.inr hm))
  exact ⟨sNext_upd hi hq hF hf2 hf1 hS hf4 hf5 hf6 ρ M ι κ v, sView_upd hi hq hF hf2 hf1 ρ M ι κ v, hI⟩

theorem skey2_parts {s : SMachine} {ps : List SEntry} (h : checkSMachine s ps = true) {e : SEntry} (he : e ∈ ps) {g : Nat} (hg : g ∈ e.keys2) :
    skFresh s g = true ∧ (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains g = false
      ∧ occC g s.f.m.pre = false ∧ (∀ p ∈ s.f.m.init, occE g p.2 = false) ∧ (∀ e' ∈ ps, occC g e'.law.holds = false ∨ g ∈ e'.keys2)
      ∧ e.law.key ≠ some g := by
  simp only [checkSMachine, List.all_eq_true, Bool.and_eq_true] at h
  have hk := (h.2 e he).1.1.2
  simp only [key2Ok, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, Bool.or_eq_true, List.contains_iff_mem] at hk
  obtain ⟨⟨⟨⟨⟨hkey, hf⟩, hc⟩, hp⟩, hi⟩, hall⟩ := hk g hg
  exact ⟨hf, hc, hp, hi, fun e' he' => (by have := (hall e' he').1; simpa using this), hkey⟩

theorem skeys_apart {s : SMachine} {ps : List SEntry} (h : checkSMachine s ps = true) : ∀ e ∈ ps, ∀ k, e.law.key = some k → k ∉ e.keys2 :=
  fun e he k hk hg => (skey2_parts h he hg).2.2.2.2.2 hk

/-- The start: at params that meet the precondition and the facts, with maps as declared, every law holds. -/
theorem sstart_case (s : SMachine) (ps : List SEntry) (h : checkSMachine s ps = true) (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (hM : StartMaps s.f.m M) (h0 : evalC ρ M s.f.m.pre = true) (hfa : ∀ l ∈ s.facts, l.Holds ρ M) (hpf : s.PFacts ρ M) :
    ∀ e ∈ ps, e.law.Holds (applyS s.f.m.init ρ M) M := by
  simp only [checkSMachine, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hfok⟩, h⟩ := h
  intro e he
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hfresh⟩, hslaw⟩, hspre⟩, hsinit⟩, hskf⟩, _⟩, hst⟩, _⟩ := h e he
  refine goalOf_holds e.law (hslaw e he) _ M (fun v => ?_)
  apply Decidable.byContradiction; intro hn
  apply sound_in _ _ hst (upd ρ e.sk v) M
  intro c hc
  simp only [sStartGoal, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | hc) | rfl
  · rw [congrC _ ρ M s.f.m.pre (fun i hi => by
      simp only [upd]; split
      · rename_i hik; subst hik; simp [hspre] at hi
      · rfl)]
    exact h0
  · -- The facts hold at the start, and read not the skolem.
    exact facthyps_true s e.finsts e.pfinsts _ M (fun f hf => (pfactsOk_parts hfok f hf).2.2)
      (facts_frame s hfok [e.sk] [] (fun l hl => by simp [avoids, (skFresh_parts hskf).2.2.2.2.2.2 l hl])
        (fun _ _ => by simp [avoidsMaps]) (fun i _ hik => by simp only [upd]; rw [if_neg (by simpa using hik)]) (fun _ _ _ => rfl) hfa)
      (pfacts_frame s hfok [e.sk] [] (fun f hf => by simp [avoids, skFresh_pfacts hskf f hf])
        (fun _ _ => by simp [avoidsMaps]) (fun i _ hik => by simp only [upd]; rw [if_neg (by simpa using hik)]) (fun _ _ _ => rfl) hpf) c hc
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

/-- One step: from a state where the precondition, the facts and every entry hold, a request allowed keeps each law. -/
theorem sstep_case (s : SMachine) (ps : List SEntry) (h : checkSMachine s ps = true) (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) (hp0 : evalC ρ M s.f.m.pre = true) (hfa : ∀ l ∈ s.facts, l.Holds ρ M) (hpf : s.PFacts ρ M)
    (ih : ∀ e ∈ ps, e.Holds ρ M) (ha : evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume = true) :
    ∀ e ∈ ps, e.law.Holds (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2 := by
  have hlav := slaws_avoid h
  have hkk := skeys_apart h
  simp only [checkSMachine, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hs, hpre⟩, hrp⟩, hterms⟩, hfok⟩, h⟩ := h
  obtain ⟨hfav, hstp, hwr, hev⟩ := sTermsOk_parts hterms
  intro e he
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hlx, hlm⟩, hfresh⟩, hslaw⟩, hspre⟩, _⟩, hskf⟩, _⟩, _⟩, hst⟩ := h e he
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩ := skFresh_parts hskf
  have hnot : e.sk ∉ s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1) := fun hm => by
    rw [List.contains_iff_mem.mpr hm] at hfresh; cases hfresh
  have hskE : e.sk ∉ s.extVars := fun hm => hnot (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hm)))
  have hskF : e.sk ∉ flagVars s.f.flags := fun hm => hnot (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hm)))
  -- The law at the next state with the carried maps in place reads as at the next state: it reads none of them.
  refine holds_transfer (V := []) (MS := s.carried) (ρ' := (sNext s ρ M ι κ).1) (M' := withCarried s (sNext s ρ M ι κ).2 κ) e.law (by simp [avoids]) hlm (fun i _ => rfl)
    (fun mp hmp => by simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmp)]) ?_
  refine goalOf_holds e.law (hslaw e he) _ _ (fun v => ?_)
  apply Decidable.byContradiction; intro hn
  -- The frame runs from the state with the skolem set to v: the machine reads it nowhere, so the step is the same.
  obtain ⟨hNext, hView, _⟩ := fresh_parts hskf (by simpa [List.contains_iff_mem] using hnot) ρ M ι κ v
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
  apply sound_in _ _ hst W M0
  intro c hc
  simp only [sStepGoal, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, List.mem_map] at hc
  rcases hc with ((rfl | hc) | ⟨c', hc', rfl⟩) | rfl
  · -- The precondition: it reads no map, no request and not the skolem.
    rw [noReadsC W M0 M s.f.m.pre hrp, congrC W ρ M s.f.m.pre (fun i hi => ?_)]
    · exact hp0
    · have hi1 := avoids_occ hpre hi
      have hik : i ≠ e.sk := fun h' => by rw [h'] at hi; simp [hspre] at hi
      simp only [W, withExt]
      rw [if_neg (fun h' => hi1 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.contains_iff_mem.mp h')))))]
      simp only [upd, if_neg hik]
  · -- The facts: they read no request, not the skolem, and no map a request carries.
    exact facthyps_true s e.finsts e.pfinsts W M0 (fun f hf => (pfactsOk_parts hfok f hf).2.2)
      (facts_frame s hfok [e.sk] [] (fun l hl => by simp [avoids, hf7 l hl])
        (fun _ _ => by simp [avoidsMaps])
        (fun i hie hik => by simp only [W, withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hie)]; simp only [upd]; rw [if_neg (by simpa using hik)])
        (fun mp hmc _ => by simp only [M0, withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmc)]) hfa)
      (pfacts_frame s hfok [e.sk] [] (fun f hf => by simp [avoids, skFresh_pfacts hskf f hf])
        (fun _ _ => by simp [avoidsMaps])
        (fun i hie hik => by simp only [W, withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hie)]; simp only [upd]; rw [if_neg (by simpa using hik)])
        (fun mp hmc _ => by simp only [M0, withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmc)]) hpf) c hc
  · -- The entries hold at the state with the skolem set (their laws don't read it), so in the goal's view of it, and so
    -- does each pair's law; the assumption reads the skolem nowhere either.
    have hA : evalC (sView s (upd ρ e.sk v) M ι κ).1 (sView s (upd ρ e.sk v) M ι κ).2 s.f.m.assume = true := by
      rw [hView]; dsimp only
      rw [congrC _ (sView s ρ M ι κ).1 _ _ (fun i hi => by
        have hik : i ≠ e.sk := fun h' => by rw [h', hf3] at hi; cases hi
        simp only [upd, if_neg hik])]
      exact ha
    have hallY : ∀ e' ∈ ps, e'.Holds W M0 := fun e' he' =>
      sentry_transfer (hlav e'.law (List.mem_map_of_mem he')).1 (hlav e'.law (List.mem_map_of_mem he')).2
        (fun i hi => by simp only [W, withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hi)])
        (fun mp hmp => by simp only [M0, withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmp)])
        (sentry_upd (Or.inl (hslaw e' he')) v (ih e' he'))
    exact sframe_hyps s [] [] W M0 hs (sLaws ps e.pinsts) (sInsts ps e.insts e.pinsts) e.qinsts
      (fun l hl => by
        rcases List.mem_append.mp hl with hl | hl
        · obtain ⟨e', he', rfl⟩ := List.mem_map.mp hl; exact SEntry.holds_law (hallY e' he')
        · exact pairLaws_hold ps e.pinsts hkk hallY l hl)
      (hH []) (fun _ _ => by simp [avoids]) (fun _ _ => by simp [avoids]) (fun _ _ => by simp [avoidsMaps]) hA (by simp [trueC, evalC, evalE]) c' hc'
  · -- The goal, read across the step: the maps a request carries read as carried, the rest as the step leaves them.
    have hrd' : ∀ mp k, evalE W M0 (stepRdS s (frameSub [] []) (frameRd [] getRd) mp k) = withCarried s (sNext s ρ M ι κ).2 κ mp (evalE W M0 k) := by
      intro mp k
      by_cases hmp : mp ∈ s.carried
      · have hne : lookup (fun w => w.1 == mp) s.every = none := lookup_none (fun w hw => by
          simp only [beq_eq_false_iff_ne]; intro h'; exact (hev w hw).2.2.2.2.1 (by rw [h']; exact hmp))
        have hnw : lookup (fun w : Nat × E × E => w.1 == mp) s.f.m.writes = none := lookup_none (fun w hw => by
          simp only [beq_eq_false_iff_ne]; intro h'; exact (hwr w hw).2 (by rw [h']; exact hmp))
        simp only [stepRdS, hne, stepRd, hnw]
        simp [frameRd, getRd, lookup, evalE, M0, withCarried, hmp]
      · rw [hD'.2 mp k hmp (by simp), hNext]; simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmp)]
    simp only [evalC]
    rw [substR_evalC _ _ W M0 _ hrd', goalOf_agree e.law e.sk _ (X' := upd (sNext s ρ M ι κ).1 e.sk v)
      (by rw [hD'.1 e.sk hskE hskF, hNext]) (fun i hi => ?_)]
    · simpa using hn
    · have hi1 := avoids_occ hlx hi
      rw [hD'.1 i (fun h' => hi1 (List.mem_append_left _ h')) (fun h' => hi1 (List.mem_append_right _ h')), hNext]

/-- The induction rule with sets: for params that meet the precondition, maps that start as declared and functions that
meet the facts, every entry of an accepted proof holds in every reachable state (a law about several keys at every value
of its further keys), whatever maps each request carries. -/
theorem smachine_sound (s : SMachine) (ps : List SEntry) (h : checkSMachine s ps = true) :
    ∀ ρ M, SReach s ρ M → ∀ e ∈ ps, e.Holds ρ M := by
  have hpre := spre_parts h
  have hfok := sfacts_ok h
  -- Facts at a state hold with a further key set: they read no further key.
  have hfacts : ∀ {ρ : Nat → Nat} {M : Nat → Nat → Nat} {g : Nat}, skFresh s g = true → (∀ l ∈ s.facts, l.Holds ρ M) → ∀ w, ∀ l ∈ s.facts, l.Holds (upd ρ g w) M := by
    intro ρ M g hf hfa w
    exact facts_frame s hfok [g] [] (fun l hl => by simp [avoids, (skFresh_parts hf).2.2.2.2.2.2 l hl]) (fun _ _ => by simp [avoidsMaps])
      (fun i _ hig' => by simp only [upd]; rw [if_neg (by simpa using hig')]) (fun _ _ _ => rfl) hfa
  have hpfacts : ∀ {ρ : Nat → Nat} {M : Nat → Nat → Nat} {g : Nat}, skFresh s g = true → s.PFacts ρ M → ∀ w, s.PFacts (upd ρ g w) M := by
    intro ρ M g hf hpf w
    exact pfacts_frame s hfok [g] [] (fun f hfm => by simp [avoids, skFresh_pfacts hf f hfm]) (fun _ _ => by simp [avoidsMaps])
      (fun i _ hig' => by simp only [upd]; rw [if_neg (by simpa using hig')]) (fun _ _ _ => rfl) hpf
  have hpreu : ∀ {ρ : Nat → Nat} {M : Nat → Nat → Nat} {g : Nat}, occC g s.f.m.pre = false → evalC ρ M s.f.m.pre = true → ∀ w, evalC (upd ρ g w) M s.f.m.pre = true := by
    intro ρ M g hpg h0 w
    rw [congrC _ ρ M s.f.m.pre (fun i hi => by have hig' : i ≠ g := (fun h' => by rw [h', hpg] at hi; cases hi); simp only [upd, if_neg hig'])]; exact h0
  intro ρ M hr
  induction hr with
  | start ρ M hM h0 hfa hpf =>
    intro e he
    -- Each further key set in turn, from a start state that meets the precondition and the facts.
    suffices hs : ∀ gs : List Nat, (∀ g ∈ gs, g ∈ e.keys2) → ∀ ρ', evalC ρ' M s.f.m.pre = true → (∀ l ∈ s.facts, l.Holds ρ' M) →
        s.PFacts ρ' M → holdsOver e.law M gs (applyS s.f.m.init ρ' M) from hs e.keys2 (fun g hg => hg) ρ h0 hfa hpf
    intro gs
    induction gs with
    | nil => intro _ ρ' hp hf hq; exact sstart_case s ps h ρ' M hM hp hf hq e he
    | cons g gs ih =>
      intro hsub ρ' hp hf hq w
      obtain ⟨hfr, hc, hpg, hig, _, _⟩ := skey2_parts h he (hsub g List.mem_cons_self)
      have hI := (fresh_parts hfr hc ρ' M (fun _ => 0) (fun _ _ => 0) 0).2.2
      rw [← applyS_upd hI (by simpa [List.all_eq_true] using hig)]
      exact ih (fun g' hg' => hsub g' (List.mem_cons_of_mem _ hg')) (upd ρ' g w) (hpreu hpg hp w) (hfacts hfr hf w) (hpfacts hfr hq w)
  | step ρ M ι κ hr ha ih =>
    intro e he
    suffices hs : ∀ gs : List Nat, (∀ g ∈ gs, g ∈ e.keys2) → ∀ ρ', evalC ρ' M s.f.m.pre = true → (∀ l ∈ s.facts, l.Holds ρ' M) →
        s.PFacts ρ' M → (∀ e' ∈ ps, e'.Holds ρ' M) → evalC (sView s ρ' M ι κ).1 (sView s ρ' M ι κ).2 s.f.m.assume = true →
        holdsOver e.law (sNext s ρ' M ι κ).2 gs (sNext s ρ' M ι κ).1 from
      hs e.keys2 (fun g hg => hg) ρ (pre_sreach s hpre.1 hpre.2 hr) (facts_sreach s hfok hr) (pfacts_sreach s hfok hr) ih ha
    intro gs
    induction gs with
    | nil => intro _ ρ' hp hf hq hi ha'; exact sstep_case s ps h ρ' M ι κ hp hf hq hi ha' e he
    | cons g gs ihg =>
      intro hsub ρ' hp hf hq hi ha' w
      obtain ⟨hfr, hc, hpg, _, hall, _⟩ := skey2_parts h he (hsub g List.mem_cons_self)
      obtain ⟨hNext, hView, _⟩ := fresh_parts hfr hc ρ' M ι κ w
      have := ihg (fun g' hg' => hsub g' (List.mem_cons_of_mem _ hg')) (upd ρ' g w) (hpreu hpg hp w) (hfacts hfr hf w) (hpfacts hfr hq w)
        (fun e' he' => sentry_upd (hall e' he') w (hi e' he'))
        (by
          rw [hView]; dsimp only
          rw [congrC _ (sView s ρ' M ι κ).1 _ _ (fun i hi => by
            have hig' : i ≠ g := fun h' => by rw [h', (skFresh_parts hfr).2.2.1] at hi; cases hi
            simp only [upd, if_neg hig'])]
          exact ha')
      rw [hNext] at this; exact this

/-! k-step laws over sets -/

structure SKStep where
  k : KStep                        -- whens (flags inlined), then, ren (each later step: every extended request variable), primes, insts, proof
  mren : List (List (Nat × Nat))   -- per step: (carried map, the name the goal reads it by there); [] for the first step
  qinsts : List (Nat × List E)     -- (quantified flag, keys): where each frame closes it
  finsts : List (Nat × E)          -- (fact index, key): where the goal assumes the facts, read at the first frame
  pinsts : List (Nat × E × List E) -- (law index, key, further keys): where each frame assumes the laws about several keys
  pfinsts : List (Nat × E × List E) -- (fact index, key, further keys): where the goal assumes the facts about several keys
  used : List C                    -- the hypotheses the tree refutes ([] for the goal's own, in its order)
  names : List (List (Nat × Nat))  -- per step but the last: (state variable, the fresh variable naming it after that step)

def sKOut (s : SMachine) (ps : List SEntry) (sl : SKStep) := sRun s (sLaws ps sl.pinsts) (sInsts ps sl.k.insts sl.pinsts) sl.qinsts sl.k.whens sl.k.ren sl.mren sl.names [] getRd
def sKGoal (s : SMachine) (ps : List SEntry) (sl : SKStep) : List C :=
  [s.f.m.pre] ++ factHyps s sl.finsts sl.pfinsts ++ (sKOut s ps sl).1
    ++ [.not (substRC (kEndSub sl.k (sKOut s ps sl).2.1 (sKOut s ps sl).2.2) (kEndRd sl.k (sKOut s ps sl).2.2) sl.k.then_)]

-- The step's terms, flags inlined, read none of the names later requests' maps are read by.
def sMapsOk (s : SMachine) (MZ : List Nat) : Bool :=
  s.f.m.step.all (fun p => avoidsMapsE MZ (inlineE s.f.flags p.2))
    && s.f.m.writes.all (fun w => avoidsMapsE MZ (inlineE s.f.flags w.2.1) && avoidsMapsE MZ (inlineE s.f.flags w.2.2))
    && s.every.all (fun w => avoidsMapsE MZ (inlineE s.f.flags w.2.2))
    && s.facts.all (fun l => avoidsMaps MZ l.holds) && s.pfacts.all (fun f => avoidsMaps MZ f.1.holds)

def szone (s : SMachine) (sl : SKStep) : List Nat := tgts sl.k.ren ++ flagVars s.f.flags ++ tgts sl.names

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
    && sl.k.whens.all (fun w => (sFrameHyps s (sLaws ps sl.pinsts) (sInsts ps sl.k.insts sl.pinsts) [] w).all (fun c => avoids (szone s sl) c)
      && (sFrameHyps s (sLaws ps sl.pinsts) (sInsts ps sl.k.insts sl.pinsts) sl.qinsts w).all (fun c => avoidsMaps (tgts sl.mren) c))
    && s.qflags.all (fun q => avoids (szone s sl) q.2.2)
    && sTermsOk s (szone s sl) && sMapsOk s (tgts sl.mren)
    && checkIn (sKGoal s ps sl) ⟨sl.k.proof.1, sl.used, sl.k.proof.2⟩
    && distinct (tgts sl.k.ren ++ tgts sl.names)
    && sl.names.all (fun n => n.all fun p => !s.extVars.contains p.1 && !(szone s sl).contains p.1)
    && avoids (tgts sl.names) sl.k.then_

/-! What a k-step law over sets claims -/

abbrev SRequest := (Nat → Nat) × (Nat → Nat → Nat)   -- a request's inputs, and the maps it carries

noncomputable def sEnd (s : SMachine) : (Nat → Nat) → (Nat → Nat → Nat) → List SRequest → (Nat → Nat) × (Nat → Nat → Nat)
  | ρ, M, [] => (ρ, M)
  | ρ, M, q :: qs => sEnd s (sNext s ρ M q.1 q.2).1 (sNext s ρ M q.1 q.2).2 qs

-- The state after each step.
noncomputable def sStates (s : SMachine) : (Nat → Nat) → (Nat → Nat → Nat) → List SRequest → List (Nat → Nat)
  | _, _, [] => []
  | ρ, M, q :: qs => (sNext s ρ M q.1 q.2).1 :: sStates s (sNext s ρ M q.1 q.2).1 (sNext s ρ M q.1 q.2).2 qs

theorem evalE_assoc_getD (σ : List (Nat × E)) (W : Nat → Nat) (M0 : Nat → Nat → Nat) (v : Nat) :
    evalE W M0 ((assoc σ v).getD (.var v)) = applyS σ W M0 v := by
  simp only [applyS]; cases assoc σ v <;> simp [evalE]

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

theorem sMapsOk_parts {s : SMachine} {MZ : List Nat} (h : sMapsOk s MZ = true) :
    (∀ p ∈ s.f.m.step, avoidsMapsE MZ (inlineE s.f.flags p.2) = true)
      ∧ (∀ w ∈ s.f.m.writes, avoidsMapsE MZ (inlineE s.f.flags w.2.1) = true ∧ avoidsMapsE MZ (inlineE s.f.flags w.2.2) = true)
      ∧ (∀ w ∈ s.every, avoidsMapsE MZ (inlineE s.f.flags w.2.2) = true) := by
  simp only [sMapsOk, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2⟩

theorem sMapsOk_facts {s : SMachine} {MZ : List Nat} (h : sMapsOk s MZ = true) : ∀ l ∈ s.facts, avoidsMaps MZ l.holds = true := by
  simp only [sMapsOk, Bool.and_eq_true, List.all_eq_true] at h; exact h.1.2
theorem sMapsOk_pfacts {s : SMachine} {MZ : List Nat} (h : sMapsOk s MZ = true) : ∀ f ∈ s.pfacts, avoidsMaps MZ f.1.holds = true := by
  simp only [sMapsOk, Bool.and_eq_true, List.all_eq_true] at h; exact h.2

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

theorem skrun_sound (s : SMachine) (ps : List SEntry) (hl : checkSMachine s ps = true) (Z MZ : List Nat) (laws : List MLaw) (insts : List (Nat × E)) (qinsts : List (Nat × List E))
    (hlY : ∀ ρ M ι κ, SReach s ρ M → ∀ l ∈ laws, l.Holds (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ))
    (W : Nat → Nat) (M0 : Nat → Nat → Nat)
    (hfz : ∀ v ∈ flagVars s.f.flags, v ∈ Z) (hterms : sTermsOk s Z = true) (hmaps : sMapsOk s MZ = true)
    (hqb : ∀ q ∈ s.qflags, avoids Z q.2.2 = true) :
    ∀ (ws : List C) (rs mrs ns : List (List (Nat × Nat))) (qs : List SRequest) (σ : List (Nat × E)) (rd : Nat → E → E)
      (ρ : Nat → Nat) (M : Nat → Nat → Nat),
      ws.length = rs.length → ws.length = mrs.length → ws.length = qs.length →
      (∀ w ∈ ws, (∀ c ∈ sFrameHyps s laws insts [] w, avoids Z c = true) ∧ ∀ c ∈ sFrameHyps s laws insts qinsts w, avoidsMaps MZ c = true) →
      (∀ r ∈ rs, ∀ p ∈ r, p.1 ∈ s.extVars) →
      (∀ r ∈ rs.tail, ∀ i ∈ s.extVars, ∃ p ∈ r, p.1 = i) →
      (∀ r ∈ mrs, ∀ p ∈ r, p.1 ∈ s.carried) →
      (∀ r ∈ mrs.tail, ∀ mp ∈ s.carried, ∃ p ∈ r, p.1 = mp) →
      RenOK W rs.tail (sExts s ρ M qs).tail → MRenOK M0 mrs.tail (qs.map (·.2)).tail →
      (∀ n ∈ ns, ∀ p ∈ n, p.1 ∉ s.extVars ∧ p.1 ∉ Z) → RenOK W ns (sStates s ρ M qs) →
      SReach s ρ M → SDenotes s Z MZ W M0 σ rd ρ M → SHeadL s Z MZ W M0 σ rd ρ M rs mrs qs → SAllowed s ws ρ M qs →
      (∀ c ∈ (sRun s laws insts qinsts ws rs mrs ns σ rd).1, evalC W M0 c = true)
        ∧ SDenotes s Z MZ W M0 (sRun s laws insts qinsts ws rs mrs ns σ rd).2.1 (sRun s laws insts qinsts ws rs mrs ns σ rd).2.2
            (sEnd s ρ M qs).1 (sEnd s ρ M qs).2
  | [], rs, mrs, ns, qs, σ, rd, ρ, M, hl1, hl2, hl3, _, _, _, _, _, _, _, _, _, _, hD, _, _ => by
    cases rs with
    | cons _ _ => simp at hl1
    | nil =>
      cases mrs with
      | cons _ _ => simp at hl2
      | nil =>
        cases qs with
        | cons _ _ => simp at hl3
        | nil => exact ⟨fun c hc => by simp [sRun] at hc, hD⟩
  | w :: ws, rs, mrs, ns, qs, σ, rd, ρ, M, hl1, hl2, hl3, hav, hkeys, hcov, hmkeys, hmcov, hren, hmren, hnsrc, hnok, hr, hD, hH, hK => by
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
    -- The state after the step, named: each fresh variable holds the next state's value of the variable it names.
    have hnames : ∀ p ∈ ns.headD [], W p.2 = (sNext s ρ M q.1 q.2).1 p.1 := by
      cases ns with
      | nil => intro p hp; simp at hp
      | cons n ns' => exact hnok.1
    have hnsrc1 : ∀ p ∈ ns.headD [], p.1 ∉ s.extVars ∧ p.1 ∉ Z := by
      cases ns with
      | nil => intro p hp; simp at hp
      | cons n ns' => exact hnsrc n List.mem_cons_self
    have hD'' : SDenotes s Z MZ W M0 (frameSub (ns.headD []) (stepSub s.f (frameSub r σ) (frameRd mr rd))) (stepRdS s (frameSub r σ) (frameRd mr rd))
        (sNext s ρ M q.1 q.2).1 (sNext s ρ M q.1 q.2).2 := by
      refine ⟨fun v hve hvz => ?_, hD'.2⟩
      by_cases hin : ∃ p ∈ ns.headD [], p.1 = v
      · exact applyS_frame_in hin hnames
      · rw [applyS_frame_out (fun p hp he => hin ⟨p, hp, he⟩)]; exact hD'.1 v hve hvz
    -- The next step's frame, its request set and its maps read, agrees with the next state and request.
    have hH' : SHeadL s Z MZ W M0 (frameSub (ns.headD []) (stepSub s.f (frameSub r σ) (frameRd mr rd))) (stepRdS s (frameSub r σ) (frameRd mr rd))
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
            hD''.1 v hve hvz]
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
    have hnsrc' : ∀ n ∈ ns.tail, ∀ p ∈ n, p.1 ∉ s.extVars ∧ p.1 ∉ Z := fun n hn => hnsrc n (List.mem_of_mem_tail hn)
    have hnok' : RenOK W ns.tail (sStates s (sNext s ρ M q.1 q.2).1 (sNext s ρ M q.1 q.2).2 qs) := by
      cases ns with
      | nil => exact trivial
      | cons n ns' => exact hnok.2
    obtain ⟨ih1, ih2⟩ := skrun_sound s ps hl Z MZ laws insts qinsts hlY W M0 hfz hterms hmaps hqb ws rs mrs ns.tail qs _ _ _ _ hl1 hl2 hl3
      (fun w' hw' => hav w' (List.mem_cons_of_mem _ hw'))
      (fun r' hr'' => hkeys r' (List.mem_cons_of_mem _ hr''))
      (fun r' hr'' => hcov r' (List.mem_of_mem_tail hr''))
      (fun r' hr'' => hmkeys r' (List.mem_cons_of_mem _ hr''))
      (fun r' hr'' => hmcov r' (List.mem_of_mem_tail hr''))
      hren' hmren' hnsrc' hnok' hr' hD'' hH' hK'
    refine ⟨fun c hc => ?_, ih2⟩
    simp only [sRun, List.mem_append, List.mem_map] at hc
    rcases hc with (⟨c', hc', rfl⟩ | hc) | hc
    · exact sframe_hyps s Z MZ W M0 (sOk_of hl) laws insts qinsts (hlY ρ M q.1 q.2 hr)
        hH1 (hav w List.mem_cons_self).1 hqb (hav w List.mem_cons_self).2 hA hW c' hc'
    · -- Each name's equation: the fresh variable holds the next state's value, which the term denotes.
      simp only [nameHyps, List.mem_map] at hc
      obtain ⟨p, hp, rfl⟩ := hc
      simp only [evalC]
      apply decide_eq_true
      show W p.2 = evalE W M0 ((assoc (stepSub s.f (frameSub r σ) (frameRd mr rd)) p.1).getD (.var p.1))
      rw [hnames p hp, evalE_assoc_getD]
      exact (hD'.1 p.1 (hnsrc1 p hp).1 (hnsrc1 p hp).2).symm
    · exact ih1 c hc

/-- The k-step rule over sets: an accepted k-step goal makes its law hold. -/
theorem skstep_sound (s : SMachine) (ps : List SEntry) (sl : SKStep)
    (hl : checkSMachine s ps = true) (hc : checkSKStep s ps sl = true) : SKStepHolds s sl := by
  intro ρ M hr q₁ qs hlen hK
  simp only [checkSKStep, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlw, hlm⟩, hhead⟩, hmhead⟩, hdist⟩, hmdist⟩, hkeys⟩, hcov⟩, hmkeys⟩, hmcov⟩, hpr⟩, hpm⟩, hpre⟩, hws⟩, hqb⟩, hterms⟩, hmaps⟩, hgoal⟩, hnd⟩, hnsrc⟩, hnthen⟩ := hc
  obtain ⟨hpreS, hrp⟩ := spre_parts hl
  have hflags : ∀ v ∈ flagVars s.f.flags, v ∈ szone s sl := fun v hv => List.mem_append_left _ (List.mem_append_right _ hv)
  obtain ⟨rs, hrs⟩ : ∃ rs, sl.k.ren = [] :: rs := by
    cases h : sl.k.ren with
    | nil => rw [h] at hhead; simp at hhead
    | cons r rs => rw [h] at hhead; simp only [List.head?_cons, Option.some.injEq] at hhead; exact ⟨rs, by rw [hhead]⟩
  obtain ⟨mrs, hmrs⟩ : ∃ mrs, sl.mren = [] :: mrs := by
    cases h : sl.mren with
    | nil => rw [h] at hmhead; simp at hmhead
    | cons r rs => rw [h] at hmhead; simp only [List.head?_cons, Option.some.injEq] at hmhead; exact ⟨rs, by rw [hmhead]⟩
  -- The goal's environment: each later request at its fresh variables, and each step's state at its names.
  let W0 := renEnv sl.k.ren (sExts s ρ M (q₁ :: qs)) (withExt s ρ (sReq s ρ M q₁.1 q₁.2))
  let W := renEnv sl.names (sStates s ρ M (q₁ :: qs)) W0
  obtain ⟨_, hndn, hndis⟩ := distinct_append hnd
  have hWn : ∀ v, v ∉ tgts sl.names → W v = W0 v := fun v hv => renEnv_other _ _ _ v hv
  let M0 := renMaps sl.mren ((q₁ :: qs).map (·.2)) (withCarried s M q₁.2)
  have hWo : ∀ v, v ∉ szone s sl → W v = withExt s ρ (sReq s ρ M q₁.1 q₁.2) v := fun v hv => by
    rw [hWn v (fun h => hv (List.mem_append_right _ h))]
    exact renEnv_other _ _ _ v (fun h => hv (List.mem_append_left _ (List.mem_append_left _ h)))
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
    have h : RenOK W sl.k.ren (sExts s ρ M (q₁ :: qs)) :=
      renOK_congr _ _ (fun v hv => hWn v (hndis v hv)) (renEnv_ok sl.k.ren _ _ hdist)
    rw [hrs] at h ⊢; exact h.2
  have hmren0 : MRenOK M0 sl.mren.tail ((q₁ :: qs).map (·.2)).tail := by
    have h : MRenOK M0 sl.mren ((q₁ :: qs).map (·.2)) := renMaps_ok sl.mren _ _ hmdist
    rw [hmrs] at h ⊢; exact h.2
  -- Every entry holds at each reachable state, so each law (and each pair's) holds in the goal's view of it.
  have hlY : ∀ ρ M ι κ, SReach s ρ M → ∀ l ∈ sLaws ps sl.pinsts, l.Holds (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ) := by
    intro ρ M ι κ hr l hl'
    have hall : ∀ e ∈ ps, e.Holds (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ) := fun e he =>
      sentry_transfer (slaws_avoid hl e.law (List.mem_map_of_mem he)).1 (slaws_avoid hl e.law (List.mem_map_of_mem he)).2
        (fun i hi => by simp only [withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hi)])
        (fun mp hmp => by simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmp)])
        (smachine_sound s ps hl ρ M hr e he)
    rcases List.mem_append.mp hl' with hl' | hl'
    · obtain ⟨e', he', rfl⟩ := List.mem_map.mp hl'; exact SEntry.holds_law (hall e' he')
    · exact pairLaws_hold ps sl.pinsts (skeys_apart hl) hall l hl'
  obtain ⟨hh, hfin⟩ := skrun_sound s ps hl (szone s sl) (tgts sl.mren) (sLaws ps sl.pinsts) (sInsts ps sl.k.insts sl.pinsts) sl.qinsts hlY W M0 hflags hterms hmaps hqb
    sl.k.whens sl.k.ren sl.mren sl.names (q₁ :: qs) [] getRd ρ M hlw (by omega) (by simp only [List.length_cons]; omega)
    hws (fun r hr p hp => List.contains_iff_mem.mp (hkeys r hr p hp))
    (fun r hr i hi => by have := hcov r hr i hi; simpa only [List.any_eq_true, beq_iff_eq] using this)
    (fun r hr p hp => List.contains_iff_mem.mp (hmkeys r hr p hp))
    (fun r hr i hi => by have := hmcov r hr i hi; simpa only [List.any_eq_true, beq_iff_eq] using this)
    hren0 hmren0
    (fun n hn p hp => by
      have h := hnsrc n hn p hp
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at h
      exact ⟨by simpa using h.1, by simpa using h.2⟩)
    (renEnv_ok sl.names _ _ hndn) hr hD0 hH0 hK
  have hfin' : SDenotes s (szone s sl) (tgts sl.mren) W M0 (sKOut s ps sl).2.1 (sKOut s ps sl).2.2
      (sEnd s ρ M (q₁ :: qs)).1 (sEnd s ρ M (q₁ :: qs)).2 := hfin
  apply Decidable.byContradiction; intro hn
  -- `then` reads none of the names, so the goal's environment reads it as the claim's does.
  have hn' : ¬ evalC (primed sl.k.prime (sEnd s ρ M (q₁ :: qs)).1 W) (primedMaps sl.k.primeMaps (sEnd s ρ M (q₁ :: qs)).2 M0) sl.k.then_ = true := by
    rw [congrC (primed sl.k.prime (sEnd s ρ M (q₁ :: qs)).1 W) (primed sl.k.prime (sEnd s ρ M (q₁ :: qs)).1 W0) _ sl.k.then_ (fun i hi => by
      simp only [primed]; split
      · rfl
      · exact hWn i (avoids_occ hnthen hi))]
    exact hn
  apply sound_in _ _ hgoal W M0
  intro c hc
  simp only [sKGoal, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ((rfl | hc) | hc) | rfl
  · -- The precondition: at the first state (it reads no map, no request and no fresh variable).
    rw [noReadsC W M0 M s.f.m.pre hrp, congrC W ρ M s.f.m.pre (fun j hj => ?_)]
    · exact pre_sreach s hpreS hrp hr
    · rw [hWo j (avoids_occ hpre hj)]; simp only [withExt]
      rw [if_neg (fun h' => avoids_occ hpreS hj (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.contains_iff_mem.mp h')))))]
  · -- The facts, at the first frame: it agrees with the first state away from the zone and the request.
    exact facthyps_true s sl.finsts sl.pfinsts W M0 (fun f hf => (pfactsOk_parts (sfacts_ok hl) f hf).2.2)
      (facts_frame s (sfacts_ok hl) (szone s sl) (tgts sl.mren) (sTermsOk_facts hterms) (sMapsOk_facts hmaps)
        (fun i hie hiz => by rw [hWo i hiz]; simp only [withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hie)])
        (fun mp hmc hmz => by rw [hMo mp hmz]; simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmc)])
        (facts_sreach s (sfacts_ok hl) hr))
      (pfacts_frame s (sfacts_ok hl) (szone s sl) (tgts sl.mren) (sTermsOk_pfacts hterms) (sMapsOk_pfacts hmaps)
        (fun i hie hiz => by rw [hWo i hiz]; simp only [withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hie)])
        (fun mp hmc hmz => by rw [hMo mp hmz]; simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmc)])
        (pfacts_sreach s (sfacts_ok hl) hr)) c hc
  · exact hh c hc
  · -- `then`, read across the run, is what SKStepHolds reads.
    have hrdE : ∀ mp k, evalE W M0 (kEndRd sl.k (sKOut s ps sl).2.2 mp k)
        = primedMaps sl.k.primeMaps (sEnd s ρ M (q₁ :: qs)).2 M0 mp (evalE W M0 k) := by
      intro mp k
      simp only [kEndRd, primedMaps]
      cases hq : lookup (fun q => q.2 == mp) sl.k.primeMaps with
      | none => simp [evalE]
      | some q =>
        have hq1 := hpm q (lookup_some hq).1
        simp only [Bool.not_eq_true'] at hq1
        exact hfin'.2 q.1 k (by simpa using hq1.1) (by simpa using hq1.2)
    have henv : applyS (kEndSub sl.k (sKOut s ps sl).2.1 (sKOut s ps sl).2.2) W M0
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
        show evalE W M0 (substRE (sKOut s ps sl).2.1 (sKOut s ps sl).2.2 (.var q.1)) = (sEnd s ρ M (q₁ :: qs)).1 q.1
        rw [substR_var]; exact hfin'.1 q.1 hqi hqz
    simp only [evalC, substR_evalC _ _ W M0 _ hrdE, henv]
    simpa using hn'

end Kern

#print axioms Kern.smachine_sound
#print axioms Kern.skstep_sound

import Live

/-!
KInd: k-induction for machines with sets, proven sound. Lean 4.34.0, core only, on top of `Sets.lean` and `Live.lean`.

A law L (about the state, params and maps, no key) is k-inductive when
- the base: L holds at the start (`kStartGoal`), and after every run of j steps from the start, 1 ≤ j < k; and
- the step: after any k steps in a row from a reachable state, each starting where L holds, L holds.

Every goal but the start's is Sets.lean's k-step goal (`SKStep`, checked by `checkSKStep`, its claim `skstep_sound`):
Lean builds each `when` and the `then` itself from L (`KInd.with`), and only the trees, the instances and the names a
goal reads later requests by come from the certificate. The base of depth j reads the first state as the start
(`startC`: each state variable its start term; a reachable state where they hold is the start's as far as the scalars
go, so the claim, made of every reachable state, covers the start) with L there too, and L before each later step; the
step reads L before each of its k steps. `then` is L with its state variables and maps renamed to their primed names
(Live.lean's `primeC`). So `kind_sound`: if the laws' proof checks and the certificate does, L holds in every reachable
state, by strong induction on the length of the run that reaches it: a run shorter than k is a base, a longer one is the
step from the state k requests back, where L held at each state after by the induction.
-/

namespace Kern
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! The certificate -/

-- A conjunction: the condition itself for one, true for none (as kernel.ts's `and` prints).
def andC : List C → C
  | [] => trueC
  | [c] => c
  | c :: cs => .and c (andC cs)

-- The start, as a condition: each state variable its start term.
def startC (s : SMachine) : C := andC (s.f.m.init.map fun p => .eq (.var p.1) p.2)

structure KInd where
  law : C
  k : Nat
  prime : List (Nat × Nat)          -- a state variable, and the name `then` reads its value after the last step by
  primeMaps : List (Nat × Nat)      -- a map, and the name `then` reads it after the last step by
  finsts : List (Nat × E)           -- the start goal's fact instances
  pfinsts : List (Nat × E × List E) -- and its instances of the facts about several keys
  start : Cert                      -- L at the start
  base : List SKStep                -- depth j = 1, …, k − 1: its instances, names and tree (Lean sets whens and then)
  step : SKStep                     -- depth k: k states where L held, then L

def KInd.then_ (kc : KInd) : C := primeC kc.prime kc.primeMaps kc.law
def KInd.with (kc : KInd) (ws : List C) (sl : SKStep) : SKStep :=
  { sl with k := { sl.k with whens := ws, then_ := kc.then_, prime := kc.prime, primeMaps := kc.primeMaps } }

-- The base of depth j: the start with L, then L before each later step.
def baseWhens (s : SMachine) (L : C) (j : Nat) : List C := .and (startC s) L :: List.replicate (j - 1) L
def kStartGoal (s : SMachine) (kc : KInd) : List C :=
  [s.f.m.pre] ++ factHyps s kc.finsts kc.pfinsts ++ [.not (substRC s.f.m.init (rdStart s.f.m) kc.law)]

-- What L may not read: a primed name, a request's variables, a flag, and a state variable a step writes that has no
-- primed name; a primed map, a carried map, and a map a step writes that has none.
def kindVars (s : SMachine) (kc : KInd) : List Nat :=
  kc.prime.map (·.2) ++ s.extVars ++ (flagVars s.f.flags ++ s.f.m.step.map (·.1)).filter (fun i => !(kc.prime.map (·.1)).contains i)
def kindMaps (s : SMachine) (kc : KInd) : List Nat :=
  kc.primeMaps.map (·.2) ++ s.carried ++ (s.f.m.writes.map (·.1) ++ s.every.map (·.1)).filter (fun mp => !(kc.primeMaps.map (·.1)).contains mp)
-- Nor a name a k-step goal reads a later request by.
def kAvoids (kc : KInd) (sl : SKStep) : Bool := avoids (tgts sl.k.ren) kc.law && avoidsMaps (tgts sl.mren) kc.law

-- The start terms read no request variable, no state variable the start sets and no carried map; each variable once.
def startOk (s : SMachine) : Bool :=
  distinct (s.f.m.init.map (·.1))
    && s.f.m.init.all (fun p => !s.extVars.contains p.1 && avoidsE (s.extVars ++ s.f.m.init.map (·.1)) p.2 && avoidsMapsE s.carried p.2)

def checkBase (s : SMachine) (ps : List SEntry) (kc : KInd) : Nat → List SKStep → Bool
  | _, [] => true
  | j, sl :: rest => kAvoids kc sl && checkSKStep s ps (kc.with (baseWhens s kc.law j) sl) && checkBase s ps kc (j + 1) rest

def checkKInd (s : SMachine) (ps : List SEntry) (kc : KInd) : Bool :=
  1 ≤ kc.k && kc.base.length + 1 == kc.k
    && distinct (kc.prime.map (·.2)) && distinct (kc.primeMaps.map (·.2))
    && avoids (kindVars s kc) kc.law && avoidsMaps (kindMaps s kc) kc.law
    && startOk s
    && checkIn (kStartGoal s kc) kc.start
    && checkBase s ps kc 1 kc.base
    && kAvoids kc kc.step && checkSKStep s ps (kc.with (List.replicate kc.k kc.law) kc.step)

/-! Runs as lists of requests -/

-- Each request allowed in turn.
def SPath (s : SMachine) : (Nat → Nat) → (Nat → Nat → Nat) → List SRequest → Prop
  | _, _, [] => True
  | ρ, M, q :: qs => evalC (sView s ρ M q.1 q.2).1 (sView s ρ M q.1 q.2).2 s.f.m.assume = true
      ∧ SPath s (sNext s ρ M q.1 q.2).1 (sNext s ρ M q.1 q.2).2 qs

theorem sEnd_append (s : SMachine) : ∀ (a b : List SRequest) (ρ : Nat → Nat) (M : Nat → Nat → Nat),
    sEnd s ρ M (a ++ b) = sEnd s (sEnd s ρ M a).1 (sEnd s ρ M a).2 b
  | [], _, _, _ => rfl
  | q :: a, b, ρ, M => by simp only [List.cons_append, sEnd]; exact sEnd_append s a b _ _

theorem spath_append (s : SMachine) : ∀ (a b : List SRequest) (ρ : Nat → Nat) (M : Nat → Nat → Nat),
    SPath s ρ M (a ++ b) ↔ SPath s ρ M a ∧ SPath s (sEnd s ρ M a).1 (sEnd s ρ M a).2 b
  | [], _, _, _ => by simp [SPath, sEnd]
  | q :: a, b, ρ, M => by
    simp only [List.cons_append, SPath, sEnd]
    rw [spath_append s a b _ _]; exact and_assoc.symm

theorem spath_take {s : SMachine} {ρ : Nat → Nat} {M : Nat → Nat → Nat} {qs : List SRequest} (h : SPath s ρ M qs) (j : Nat) :
    SPath s ρ M (qs.take j) := by
  rw [← List.take_append_drop j qs, spath_append] at h; exact h.1

theorem sreach_path (s : SMachine) : ∀ (qs : List SRequest) {ρ : Nat → Nat} {M : Nat → Nat → Nat},
    SReach s ρ M → SPath s ρ M qs → SReach s (sEnd s ρ M qs).1 (sEnd s ρ M qs).2
  | [], _, _, hr, _ => hr
  | q :: qs, _, _, hr, hp => sreach_path s qs (SReach.step _ _ _ _ hr hp.1) hp.2

-- A reachable state is the end of a run from a start.
theorem sreach_from (s : SMachine) {ρ : Nat → Nat} {M : Nat → Nat → Nat} (h : SReach s ρ M) :
    ∃ ρ0 M0, StartMaps s.f.m M0 ∧ evalC ρ0 M0 s.f.m.pre = true ∧ (∀ l ∈ s.facts, l.Holds ρ0 M0) ∧ s.PFacts ρ0 M0
      ∧ ∃ qs, SPath s (applyS s.f.m.init ρ0 M0) M0 qs ∧ sEnd s (applyS s.f.m.init ρ0 M0) M0 qs = (ρ, M) := by
  induction h with
  | start ρ M hM h0 hf hpf => exact ⟨ρ, M, hM, h0, hf, hpf, [], trivial, rfl⟩
  | step ρ M ι κ _ ha ih =>
    obtain ⟨ρ0, M0, hM, h0, hf, hpf, qs, hp, he⟩ := ih
    refine ⟨ρ0, M0, hM, h0, hf, hpf, qs ++ [(ι, κ)], ?_, ?_⟩
    · rw [spath_append, he]; exact ⟨hp, ha, trivial⟩
    · rw [sEnd_append, he]; rfl

/-! What a run leaves alone -/

theorem sNext_other (s : SMachine) {i : Nat} (hx : i ∉ s.extVars) (hf : i ∉ flagVars s.f.flags) (hs : i ∉ s.f.m.step.map (·.1))
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) : (sNext s ρ M ι κ).1 i = ρ i := by
  simp only [SMachine.extVars, SMachine.qVars, List.mem_append, not_or] at hx
  simp only [sNext, sView]
  rw [applyS_other hs, decide_other hf, decideQ_other (by simpa [SMachine.qVars] using hx.1.2), withInputs_other hx.1.1]

theorem sEnd_other (s : SMachine) {i : Nat} (hx : i ∉ s.extVars) (hf : i ∉ flagVars s.f.flags) (hs : i ∉ s.f.m.step.map (·.1)) :
    ∀ (qs : List SRequest) (ρ : Nat → Nat) (M : Nat → Nat → Nat), (sEnd s ρ M qs).1 i = ρ i
  | [], _, _ => rfl
  | q :: qs, ρ, M => by simp only [sEnd]; rw [sEnd_other s hx hf hs qs _ _, sNext_other s hx hf hs]

theorem sNext_maps_other (s : SMachine) {mp : Nat} (hc : mp ∉ s.carried) (hw : mp ∉ s.f.m.writes.map (·.1)) (he : mp ∉ s.every.map (·.1))
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) : (sNext s ρ M ι κ).2 mp = M mp := by
  funext k
  simp only [sNext, everyMaps]
  rw [lookup_none (fun w hw' => by simp only [beq_eq_false_iff_ne]; intro h; exact he (by rw [← h]; exact List.mem_map_of_mem hw'))]
  simp only [writeMaps]
  rw [lookup_none (fun w hw' => by simp only [beq_eq_false_iff_ne]; intro h; exact hw (by rw [← h]; exact List.mem_map_of_mem hw'))]
  simp only [sView, withCarried]
  rw [if_neg (by simpa [List.contains_iff_mem] using hc)]

theorem sEnd_maps_other (s : SMachine) {mp : Nat} (hc : mp ∉ s.carried) (hw : mp ∉ s.f.m.writes.map (·.1)) (he : mp ∉ s.every.map (·.1)) :
    ∀ (qs : List SRequest) (ρ : Nat → Nat) (M : Nat → Nat → Nat), (sEnd s ρ M qs).2 mp = M mp
  | [], _, _ => rfl
  | q :: qs, ρ, M => by simp only [sEnd]; rw [sEnd_maps_other s hc hw he qs _ _, sNext_maps_other s hc hw he]

-- A condition that reads no request variable and no carried map reads the same in a step's view.
theorem view_eval {s : SMachine} {c : C} (hx : avoids s.extVars c = true) (hm : avoidsMaps s.carried c = true)
    (ρ X : Nat → Nat) (M κ : Nat → Nat → Nat) : evalC (withExt s ρ X) (withCarried s M κ) c = evalC ρ M c := by
  rw [congrMC _ _ M c (fun mp hmp => by
    simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using avoidsMaps_occ hm hmp)])]
  exact congrC _ _ _ c (fun i hi => by
    simp only [withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using avoids_occ hx hi)])

theorem andC_true {ρ : Nat → Nat} {M : Nat → Nat → Nat} : ∀ {cs : List C}, (∀ c ∈ cs, evalC ρ M c = true) → evalC ρ M (andC cs) = true
  | [], _ => by simp [andC, trueC, evalC, evalE]
  | [c], h => by simpa [andC] using h c List.mem_cons_self
  | c :: d :: cs, h => by
    simp only [andC, evalC, Bool.and_eq_true]
    exact ⟨h c List.mem_cons_self, andC_true (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

/-! The parts of the check -/

section parts
variable {s : SMachine} {ps : List SEntry} {kc : KInd}

theorem kind_parts (h : checkKInd s ps kc = true) :
    1 ≤ kc.k ∧ kc.base.length + 1 = kc.k ∧ distinct (kc.prime.map (·.2)) = true ∧ distinct (kc.primeMaps.map (·.2)) = true
      ∧ avoids (kindVars s kc) kc.law = true ∧ avoidsMaps (kindMaps s kc) kc.law = true ∧ startOk s = true
      ∧ checkIn (kStartGoal s kc) kc.start = true ∧ checkBase s ps kc 1 kc.base = true
      ∧ kAvoids kc kc.step = true ∧ checkSKStep s ps (kc.with (List.replicate kc.k kc.law) kc.step) = true := by
  simp only [checkKInd, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem checkBase_get : ∀ (l : List SKStep) (j : Nat), checkBase s ps kc j l = true → ∀ i (hi : i < l.length),
    kAvoids kc l[i] = true ∧ checkSKStep s ps (kc.with (baseWhens s kc.law (j + i)) l[i]) = true
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | sl :: rest, j, h, i, hi => by
    simp only [checkBase, Bool.and_eq_true] at h
    cases i with
    | zero => exact ⟨h.1.1, by simpa using h.1.2⟩
    | succ i =>
      have := checkBase_get rest (j + 1) h.2 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

-- L reads none of the request variables and carried maps; outside its primed names, what it reads no step moves.
theorem law_reads (h5 : avoids (kindVars s kc) kc.law = true) (h6 : avoidsMaps (kindMaps s kc) kc.law = true) :
    avoids s.extVars kc.law = true ∧ avoidsMaps s.carried kc.law = true
      ∧ (∀ i, occC i kc.law = true → i ∉ kc.prime.map (·.2) ∧ i ∉ s.extVars
          ∧ (i ∈ kc.prime.map (·.1) ∨ (i ∉ flagVars s.f.flags ∧ i ∉ s.f.m.step.map (·.1))))
      ∧ (∀ mp, occMC mp kc.law = true → mp ∉ kc.primeMaps.map (·.2) ∧ mp ∉ s.carried
          ∧ (mp ∈ kc.primeMaps.map (·.1) ∨ (mp ∉ s.f.m.writes.map (·.1) ∧ mp ∉ s.every.map (·.1)))) := by
  have hv : ∀ i, occC i kc.law = true → i ∉ kindVars s kc := fun i hi => avoids_occ h5 hi
  have hm : ∀ mp, occMC mp kc.law = true → mp ∉ kindMaps s kc := fun mp hmp => avoidsMaps_occ h6 hmp
  refine ⟨?_, ?_, fun i hi => ?_, fun mp hmp => ?_⟩
  · simp only [avoids, List.all_eq_true, Bool.not_eq_true']
    intro i hx
    cases hc : occC i kc.law
    · rfl
    · exact absurd (List.mem_append_left _ (List.mem_append_right _ hx)) (hv i hc)
  · simp only [avoidsMaps, List.all_eq_true, Bool.not_eq_true']
    intro mp hx
    cases hc : occMC mp kc.law
    · rfl
    · exact absurd (List.mem_append_left _ (List.mem_append_right _ hx)) (hm mp hc)
  · have h := hv i hi
    simp only [kindVars, List.mem_append, List.mem_filter, not_or, not_and, Bool.not_eq_true', List.contains_iff_mem] at h
    refine ⟨h.1.1, h.1.2, ?_⟩
    by_cases hp : i ∈ kc.prime.map (·.1)
    · exact Or.inl hp
    · right
      have hpf : (kc.prime.map (·.1)).contains i = false := by simpa [List.contains_iff_mem] using hp
      exact ⟨fun hf => by have := h.2 (Or.inl hf); simp_all, fun hs => by have := h.2 (Or.inr hs); simp_all⟩
  · have h := hm mp hmp
    simp only [kindMaps, List.mem_append, List.mem_filter, not_or, not_and, Bool.not_eq_true', List.contains_iff_mem] at h
    refine ⟨h.1.1, h.1.2, ?_⟩
    by_cases hp : mp ∈ kc.primeMaps.map (·.1)
    · exact Or.inl hp
    · right
      have hpf : (kc.primeMaps.map (·.1)).contains mp = false := by simpa [List.contains_iff_mem] using hp
      exact ⟨fun hf => by have := h.2 (Or.inl hf); simp_all, fun hs => by have := h.2 (Or.inr hs); simp_all⟩

end parts

/-! Each part's meaning -/

-- The start goal: L at the start.
theorem kind_start (s : SMachine) (ps : List SEntry) (kc : KInd) (hl : checkSMachine s ps = true)
    (hst : checkIn (kStartGoal s kc) kc.start = true) (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (hM : StartMaps s.f.m M) (h0 : evalC ρ M s.f.m.pre = true) (hfa : ∀ l ∈ s.facts, l.Holds ρ M) (hpf : s.PFacts ρ M) :
    evalC (applyS s.f.m.init ρ M) M kc.law = true := by
  have hfok := sfacts_ok hl
  apply Decidable.byContradiction; intro hn
  apply sound_in _ _ hst ρ M
  intro c hc
  simp only [kStartGoal, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | hc) | rfl
  · exact h0
  · exact facthyps_true s kc.finsts kc.pfinsts ρ M (fun f hf => (pfactsOk_parts hfok f hf).2.2) hfa hpf c hc
  · have hrd : ∀ mp k, evalE ρ M (rdStart s.f.m mp k) = M mp (evalE ρ M k) := by
      intro mp k
      simp only [rdStart]
      split
      · rename_i p hp
        have ⟨hm, hq⟩ := lookup_some hp
        simp only [beq_iff_eq] at hq
        simp only [evalE]; rw [← hq, hM p hm]
      · rfl
    simp only [evalC, substR_evalC _ _ _ M M hrd]
    simpa using hn

-- The start meets `startC`, read in a step's view.
theorem start_meets (s : SMachine) (hs : startOk s = true) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (X : Nat → Nat) (κ : Nat → Nat → Nat) :
    evalC (withExt s (applyS s.f.m.init ρ M) X) (withCarried s M κ) (startC s) = true := by
  simp only [startOk, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hs
  obtain ⟨hd, hp⟩ := hs
  apply andC_true
  intro c hc
  obtain ⟨p, hpm, rfl⟩ := List.mem_map.mp hc
  obtain ⟨⟨hx, hav⟩, havm⟩ := hp p hpm
  have hx' : p.1 ∉ s.extVars := by simpa [List.contains_iff_mem] using hx
  simp only [evalC]
  apply decide_eq_true
  simp only [evalE]
  have hl : withExt s (applyS s.f.m.init ρ M) X p.1 = evalE ρ M p.2 := by
    simp only [withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hx')]
    simp only [applyS, assoc, lookup_unique hd hpm, Option.map_some]
  rw [hl]
  symm
  rw [congrME _ _ M p.2 (fun mp hmp => by
    simp only [withCarried]
    rw [if_neg (by
      simp only [avoidsMapsE, List.all_eq_true, Bool.not_eq_true'] at havm
      intro hc'; have := havm mp (List.contains_iff_mem.mp hc'); simp [hmp] at this)])]
  exact congrE _ _ M p.2 (fun i hi => by
    simp only [avoidsE, List.all_eq_true, Bool.not_eq_true'] at hav
    have hi1 : i ∉ s.extVars := fun h' => by have := hav i (List.mem_append_left _ h'); simp [hi] at this
    have hi2 : i ∉ s.f.m.init.map (·.1) := fun h' => by have := hav i (List.mem_append_right _ h'); simp [hi] at this
    simp only [withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hi1)]
    exact applyS_other hi2 ρ M)

-- Requests allowed in turn, L before each: the k-step goal's `when`s for L, k times.
theorem sallowed_rep (s : SMachine) (L : C) (hx : avoids s.extVars L = true) (hm : avoidsMaps s.carried L = true) :
    ∀ (qs : List SRequest) (ρ : Nat → Nat) (M : Nat → Nat → Nat), SPath s ρ M qs →
      (∀ j < qs.length, evalC (sEnd s ρ M (qs.take j)).1 (sEnd s ρ M (qs.take j)).2 L = true) →
      SAllowed s (List.replicate qs.length L) ρ M qs
  | [], _, _, _, _ => by simp [SAllowed]
  | q :: qs, ρ, M, hp, hL => by
    simp only [List.length_cons, List.replicate_succ, SAllowed]
    refine ⟨hp.1, ?_, sallowed_rep s L hx hm qs _ _ hp.2 (fun j hj => ?_)⟩
    · rw [view_eval hx hm]; exact hL 0 (by simp)
    · have := hL (j + 1) (by simp; omega)
      simpa [List.take_succ_cons, sEnd] using this

-- A k-step goal Lean built from L: L after its steps.
theorem kind_then (s : SMachine) (kc : KInd) (ws : List C) (sl : SKStep) (h : SKStepHolds s (kc.with ws sl))
    (h3 : distinct (kc.prime.map (·.2)) = true) (h4 : distinct (kc.primeMaps.map (·.2)) = true)
    (h5 : avoids (kindVars s kc) kc.law = true) (h6 : avoidsMaps (kindMaps s kc) kc.law = true) (hav : kAvoids kc sl = true)
    {ρ : Nat → Nat} {M : Nat → Nat → Nat} (hr : SReach s ρ M) (q₁ : SRequest) (qs : List SRequest)
    (hlen : qs.length + 1 = ws.length) (hA : SAllowed s ws ρ M (q₁ :: qs)) :
    evalC (sEnd s ρ M (q₁ :: qs)).1 (sEnd s ρ M (q₁ :: qs)).2 kc.law = true := by
  have hh := h ρ M hr q₁ qs hlen hA
  simp only [KInd.with, KInd.then_] at hh
  obtain ⟨_, _, hv, hmv⟩ := law_reads h5 h6
  simp only [kAvoids, Bool.and_eq_true] at hav
  rw [primeC_eval kc.prime kc.primeMaps h3 h4 _ _ _ _ kc.law (fun i hi => ?_) (fun mp hmp => ?_)] at hh
  · exact hh
  · obtain ⟨hpt, hx, hor⟩ := hv i hi
    refine ⟨hpt, hor.imp id (fun hn => ?_)⟩
    rw [sEnd_other s hx hn.1 hn.2, renEnv_other _ _ _ i (avoids_occ hav.1 hi)]
    simp only [withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hx)]
  · obtain ⟨hpt, hc, hor⟩ := hmv mp hmp
    refine ⟨hpt, hor.imp id (fun hn => ?_)⟩
    rw [sEnd_maps_other s hc hn.1 hn.2, renMaps_other _ _ _ mp (avoidsMaps_occ hav.2 hmp)]
    simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hc)]

/-! k-induction -/

/-- k-induction: if the laws' proof checks and a k-induction certificate for L does (its start goal, the k-step goals
of its base from the start for each depth 1 ≤ j < k, and its step over k steps, every `when` and `then` built by Lean
from L), then L holds in every reachable state. -/
theorem kind_sound (s : SMachine) (ps : List SEntry) (kc : KInd) (hl : checkSMachine s ps = true) (hk : checkKInd s ps kc = true) :
    ∀ ρ M, SReach s ρ M → evalC ρ M kc.law = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := kind_parts hk
  obtain ⟨hx, hm, _, _⟩ := law_reads h5 h6
  intro ρ M hr
  obtain ⟨ρ0, M0, hM0, hp0, hf0, hpf0, qs, hpath, hend⟩ := sreach_from s hr
  have hrs : SReach s (applyS s.f.m.init ρ0 M0) M0 := SReach.start ρ0 M0 hM0 hp0 hf0 hpf0
  suffices hall : ∀ n, ∀ qs : List SRequest, qs.length = n → SPath s (applyS s.f.m.init ρ0 M0) M0 qs →
      evalC (sEnd s (applyS s.f.m.init ρ0 M0) M0 qs).1 (sEnd s (applyS s.f.m.init ρ0 M0) M0 qs).2 kc.law = true by
    have := hall qs.length qs rfl hpath
    rw [hend] at this; exact this
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro qs hn hp
    -- L at every shorter run's end, and so at each state along this one.
    have ihp : ∀ j < n, evalC (sEnd s (applyS s.f.m.init ρ0 M0) M0 (qs.take j)).1 (sEnd s (applyS s.f.m.init ρ0 M0) M0 (qs.take j)).2 kc.law = true :=
      fun j hj => ih j hj _ (by rw [List.length_take]; omega) (spath_take hp j)
    by_cases h0 : n = 0
    · -- The start.
      subst h0
      rw [List.length_eq_zero_iff.mp hn]
      exact kind_start s ps kc hl h8 ρ0 M0 hM0 hp0 hf0 hpf0
    by_cases hlt : n < kc.k
    · -- A base: the run from the start, of depth n.
      obtain ⟨q₁, rest, rfl⟩ : ∃ q₁ rest, qs = q₁ :: rest := by
        cases qs with
        | nil => simp at hn; omega
        | cons q rest => exact ⟨q, rest, rfl⟩
      have hi : n - 1 < kc.base.length := by omega
      obtain ⟨hav, hc⟩ := checkBase_get kc.base 1 h9 (n - 1) hi
      rw [show 1 + (n - 1) = n by omega] at hc
      have hs := skstep_sound s ps _ hl hc
      simp only [List.length_cons] at hn
      refine kind_then s kc _ _ hs h3 h4 h5 h6 hav hrs q₁ rest (by simp [baseWhens]; omega) ?_
      simp only [baseWhens, SAllowed]
      refine ⟨hp.1, ?_, ?_⟩
      · simp only [evalC, Bool.and_eq_true]
        refine ⟨start_meets s h7 ρ0 M0 _ _, ?_⟩
        rw [view_eval hx hm]; exact ihp 0 (by omega)
      · rw [show n - 1 = rest.length by omega]
        exact sallowed_rep s kc.law hx hm rest _ _ hp.2 (fun j hj => by
          have := ihp (j + 1) (by omega)
          simpa [List.take_succ_cons, sEnd] using this)
    · -- The step: the state k requests back, and L at each state after it.
      have hkn : kc.k ≤ n := by omega
      let pre := qs.take (n - kc.k)
      let post := qs.drop (n - kc.k)
      have hsplit : pre ++ post = qs := List.take_append_drop _ _
      have hpost : post.length = kc.k := by simp only [post, List.length_drop]; omega
      have hp' := hp
      rw [← hsplit, spath_append] at hp'
      have hr' := sreach_path s pre hrs hp'.1
      obtain ⟨q₁, rest, hqr⟩ : ∃ q₁ rest, post = q₁ :: rest := by
        cases h : post with
        | nil => rw [h] at hpost; simp at hpost; omega
        | cons q rest => exact ⟨q, rest, rfl⟩
      have hs := skstep_sound s ps _ hl h11
      have hA : SAllowed s (List.replicate kc.k kc.law) (sEnd s (applyS s.f.m.init ρ0 M0) M0 pre).1 (sEnd s (applyS s.f.m.init ρ0 M0) M0 pre).2 post := by
        rw [← hpost]
        refine sallowed_rep s kc.law hx hm post _ _ hp'.2 (fun j hj => ?_)
        rw [← sEnd_append]
        have hpre : pre.length = n - kc.k := by simp only [pre, List.length_take]; omega
        have := ih (n - kc.k + j) (by omega) (pre ++ post.take j) (by simp [hpre, List.length_take]; omega)
          ((spath_append s _ _ _ _).mpr ⟨hp'.1, spath_take hp'.2 j⟩)
        exact this
      rw [hqr] at hA
      have := kind_then s kc _ _ hs h3 h4 h5 h6 h10 hr' q₁ rest (by rw [List.length_replicate, ← hpost, hqr]; simp) hA
      rw [← hqr, ← sEnd_append, hsplit] at this
      exact this

end Kern

#print axioms Kern.kind_sound

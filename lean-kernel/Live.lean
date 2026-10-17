import Sets

/-!
Liveness under fairness: "from leads to to" for machines with maps and flags, proven sound. kernel.ts proves it by a
rank (a natural term over the state and params) and a helpful request: while `from` holds and `to` doesn't, every request
allowed keeps `from` or reaches `to` and lets the rank rise only by reaching `to` (a step law), and the helpful request is
allowed and reaches `to` or lowers the rank (progress). Lean builds both goals from the liveness itself, checks them with
StepLaw.lean's and Progress.lean's rules, and `leads_sound` concludes: along every run that takes the helpful request
infinitely often, each state where `from` holds is followed by one where `to` holds. The rank can't drop forever.
-/

namespace Kern

/-! A rank that can't drop forever -/

-- Along a run, if `P ∧ ¬Q` is kept (or Q reached) with the rank never rising, and the helpful steps, taken infinitely
-- often, lower it (or reach Q), then Q follows every P.
theorem leads_of_rank {S : Type} (run : Nat → S) (P Q : S → Prop) (r : S → Nat) (H : Nat → Prop)
    (hstay : ∀ n, P (run n) → ¬ Q (run n) → (P (run (n + 1)) ∨ Q (run (n + 1))) ∧ (Q (run (n + 1)) ∨ r (run (n + 1)) ≤ r (run n)))
    (hhelp : ∀ n, P (run n) → ¬ Q (run n) → H n → Q (run (n + 1)) ∨ r (run (n + 1)) < r (run n))
    (fair : ∀ n, ∃ m, n ≤ m ∧ H m) : ∀ n, P (run n) → ∃ m, n ≤ m ∧ Q (run m) := by
  -- By induction on a bound of the rank.
  suffices h : ∀ k n, r (run n) ≤ k → P (run n) → ∃ m, n ≤ m ∧ Q (run m) from fun n hP => h _ n (Nat.le_refl _) hP
  intro k
  induction k with
  | zero => ?_
  | succ k ih => ?_
  all_goals
    intro n hr hP
    apply Classical.byContradiction
    intro hno
    have hnq : ∀ m, n ≤ m → ¬ Q (run m) := fun m hm hq => hno ⟨m, hm, hq⟩
    -- P holds, and the rank stays within its bound, at every step from n on.
    have hinv : ∀ d, P (run (n + d)) ∧ r (run (n + d)) ≤ r (run n) := by
      intro d
      induction d with
      | zero => exact ⟨hP, Nat.le_refl _⟩
      | succ d ihd =>
        obtain ⟨hPd, hrd⟩ := ihd
        obtain ⟨h1, h2⟩ := hstay (n + d) hPd (hnq _ (Nat.le_add_right _ _))
        have hq1 : ¬ Q (run (n + d + 1)) := hnq _ (by omega)
        refine ⟨?_, ?_⟩
        · rcases h1 with h1 | h1
          · exact h1
          · exact absurd h1 hq1
        · rcases h2 with h2 | h2
          · exact absurd h2 hq1
          · exact Nat.le_trans h2 hrd
    obtain ⟨m, hm, hH⟩ := fair n
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    obtain ⟨hPm, hrm⟩ := hinv d
    rcases hhelp (n + d) hPm (hnq _ (Nat.le_add_right _ _)) hH with hq | hlt
    · exact hnq _ (by omega) hq
  · -- With the rank bounded by 0, nothing lowers it.
    omega
  · -- One helpful step lowers the rank below k + 1; from there, the bound k.
    have hP1 := (hinv (d + 1)).1
    obtain ⟨m', hm', hq'⟩ := ih (n + d + 1) (by omega) (hP1 : P (run (n + d + 1)))
    exact hnq m' (by omega) hq'

/-! Primed names: a condition read after a step -/

-- A term with its state variables renamed to their primed names (`pr`: variable, name) and its maps to theirs (`pm`).
mutual
def primeE (pr pm : List (Nat × Nat)) : E → E
  | .var i => match lookup (fun q => q.1 == i) pr with
    | some q => .var q.2
    | none => .var i
  | .const n => .const n
  | .add a b => .add (primeE pr pm a) (primeE pr pm b)
  | .sub a b => .sub (primeE pr pm a) (primeE pr pm b)
  | .mul k a => .mul k (primeE pr pm a)
  | .min a b => .min (primeE pr pm a) (primeE pr pm b)
  | .max a b => .max (primeE pr pm a) (primeE pr pm b)
  | .prod a b => .prod (primeE pr pm a) (primeE pr pm b)
  | .ite c t f => .ite (primeC pr pm c) (primeE pr pm t) (primeE pr pm f)
  | .get m k => .get (match lookup (fun q => q.1 == m) pm with
      | some q => q.2
      | none => m) (primeE pr pm k)
def primeC (pr pm : List (Nat × Nat)) : C → C
  | .le a b => .le (primeE pr pm a) (primeE pr pm b)
  | .lt a b => .lt (primeE pr pm a) (primeE pr pm b)
  | .eq a b => .eq (primeE pr pm a) (primeE pr pm b)
  | .and a b => .and (primeC pr pm a) (primeC pr pm b)
  | .or a b => .or (primeC pr pm a) (primeC pr pm b)
  | .not a => .not (primeC pr pm a)
end

-- Read where `then` reads (primed names after, the rest before), a renamed term is the term after, wherever a variable
-- or map it reads is renamed or the same before and after, and reads no primed name.
section prime
variable (pr pm : List (Nat × Nat)) (hpr : distinct (pr.map (·.2)) = true) (hpm : distinct (pm.map (·.2)) = true)
  (ρ ρ' : Nat → Nat) (M M' : Nat → Nat → Nat)
include hpr hpm
mutual
theorem primeE_eval : (e : E) → (∀ i, occE i e = true → i ∉ pr.map (·.2) ∧ (i ∈ pr.map (·.1) ∨ ρ' i = ρ i)) →
    (∀ mp, occME mp e = true → mp ∉ pm.map (·.2) ∧ (mp ∈ pm.map (·.1) ∨ M' mp = M mp)) →
    evalE (primed pr ρ' ρ) (primedMaps pm M' M) (primeE pr pm e) = evalE ρ' M' e
  | .var i, hv, _ => by
    simp only [primeE]
    cases hl : lookup (fun q => q.1 == i) pr with
    | some q =>
      have ⟨hq, hqi⟩ := lookup_some hl
      simp only [beq_iff_eq] at hqi
      simp only [evalE, primed, lookup_ren hpr q hq, hqi]
    | none =>
      have hi := hv i (by simp [occE])
      have hnot : i ∉ pr.map (·.1) := fun hm => by
        obtain ⟨q, hq, hqi⟩ := List.mem_map.mp hm
        have := lookup_none_all hl q hq; simp [hqi] at this
      have hn2 : lookup (fun q => q.2 == i) pr = none := lookup_none (fun q hq => by
        simp only [beq_eq_false_iff_ne]; intro he; exact hi.1 (by rw [← he]; exact List.mem_map_of_mem hq))
      simp only [evalE, primed, hn2]
      rcases hi.2 with h | h
      · exact absurd h hnot
      · exact h.symm
  | .const n, _, _ => rfl
  | .add a b, hv, hm => by
    simp only [primeE, evalE, primeE_eval a (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h])),
      primeE_eval b (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h]))]
  | .sub a b, hv, hm => by
    simp only [primeE, evalE, primeE_eval a (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h])),
      primeE_eval b (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h]))]
  | .mul k a, hv, hm => by
    simp only [primeE, evalE, primeE_eval a (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h]))]
  | .min a b, hv, hm => by
    simp only [primeE, evalE, primeE_eval a (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h])),
      primeE_eval b (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h]))]
  | .max a b, hv, hm => by
    simp only [primeE, evalE, primeE_eval a (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h])),
      primeE_eval b (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h]))]
  | .prod a b, hv, hm => by
    simp only [primeE, evalE, primeE_eval a (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h])),
      primeE_eval b (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h]))]
  | .ite c t f, hv, hm => by
    simp only [primeE, evalE, primeC_eval c (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h])),
      primeE_eval t (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h])),
      primeE_eval f (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h]))]
  | .get m k, hv, hm => by
    have hk := primeE_eval k (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h]))
    simp only [primeE, evalE, hk]
    cases hl : lookup (fun q => q.1 == m) pm with
    | some q =>
      have ⟨hq, hqm⟩ := lookup_some hl
      simp only [beq_iff_eq] at hqm
      simp only [primedMaps, lookup_ren hpm q hq, hqm]
    | none =>
      have hmm := hm m (by simp [occME])
      have hnot : m ∉ pm.map (·.1) := fun hmem => by
        obtain ⟨q, hq, hqm⟩ := List.mem_map.mp hmem
        have := lookup_none_all hl q hq; simp [hqm] at this
      have hn2 : lookup (fun q => q.2 == m) pm = none := lookup_none (fun q hq => by
        simp only [beq_eq_false_iff_ne]; intro he; exact hmm.1 (by rw [← he]; exact List.mem_map_of_mem hq))
      simp only [primedMaps, hn2]
      rcases hmm.2 with h | h
      · exact absurd h hnot
      · rw [h]
theorem primeC_eval : (c : C) → (∀ i, occC i c = true → i ∉ pr.map (·.2) ∧ (i ∈ pr.map (·.1) ∨ ρ' i = ρ i)) →
    (∀ mp, occMC mp c = true → mp ∉ pm.map (·.2) ∧ (mp ∈ pm.map (·.1) ∨ M' mp = M mp)) →
    evalC (primed pr ρ' ρ) (primedMaps pm M' M) (primeC pr pm c) = evalC ρ' M' c
  | .le a b, hv, hm => by
    simp only [primeC, evalC, primeE_eval a (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h])),
      primeE_eval b (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h]))]
  | .lt a b, hv, hm => by
    simp only [primeC, evalC, primeE_eval a (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h])),
      primeE_eval b (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h]))]
  | .eq a b, hv, hm => by
    simp only [primeC, evalC, primeE_eval a (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h])),
      primeE_eval b (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h]))]
  | .and a b, hv, hm => by
    simp only [primeC, evalC, primeC_eval a (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h])),
      primeC_eval b (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h]))]
  | .or a b, hv, hm => by
    simp only [primeC, evalC, primeC_eval a (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h])),
      primeC_eval b (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h]))]
  | .not a, hv, hm => by
    simp only [primeC, evalC, primeC_eval a (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h]))]
end
end prime

/-! Liveness -/

structure Live where
  from_ : C
  to : C
  rank : E
  req : List (Nat × E)          -- the helpful request: an input and its term over the state and params
  prime : List (Nat × Nat)      -- a state variable, and its primed name
  primeMaps : List (Nat × Nat)  -- a map, and its primed name

def liveWhen (l : Live) : C := .and l.from_ (.not l.to)
-- The step law and the progress goal Lean checks: built here from the liveness.
def liveStay (l : Live) (insts : List (Nat × E)) (proof : List VDef × Tree) : StepLaw :=
  ⟨liveWhen l, .and (.or (primeC l.prime l.primeMaps l.from_) (primeC l.prime l.primeMaps l.to))
      (.or (primeC l.prime l.primeMaps l.to) (.le (primeE l.prime l.primeMaps l.rank) l.rank)), l.prime, l.primeMaps, insts, proof⟩
def liveHelp (l : Live) (insts : List (Nat × E)) (allowed causes : List VDef × Tree) : Progress :=
  ⟨liveWhen l, .or (primeC l.prime l.primeMaps l.to) (.lt (primeE l.prime l.primeMaps l.rank) l.rank), l.req, l.prime, l.primeMaps, insts, allowed, causes⟩

-- What `from`, `to` and the rank read: no primed name; a variable unprimed is no input, flag or step target, and a map
-- unprimed is never written (so each reads the same before and after a step). Primed names are distinct.
def liveVars (f : FMMachine) (l : Live) : List Nat :=
  l.prime.map (·.2) ++ f.m.inputs ++ (flagVars f.flags ++ f.m.step.map (·.1)).filter (fun i => !(l.prime.map (·.1)).contains i)
def liveMaps (f : FMMachine) (l : Live) : List Nat :=
  l.primeMaps.map (·.2) ++ (f.m.writes.map (·.1)).filter (fun mp => !(l.primeMaps.map (·.1)).contains mp)
def liveOk (f : FMMachine) (l : Live) : Bool :=
  distinct (l.prime.map (·.2)) && distinct (l.primeMaps.map (·.2))
    && [l.from_, l.to, .eq l.rank l.rank].all (fun c => avoids (liveVars f l) c && avoidsMaps (liveMaps f l) c)

-- A run of a machine with maps and flags: from a reachable state, each step a request the machine allows.
structure FRun (f : FMMachine) where
  st : Nat → (Nat → Nat) × (Nat → Nat → Nat)
  req : Nat → Nat → Nat
  start : FMReach f (st 0).1 (st 0).2
  allowed : ∀ n, evalC (decideFlags f.flags (withInputs f.m.inputs (st n).1 (req n)) (st n).2) (st n).2 f.m.assume = true
  next : ∀ n, st (n + 1) = (applyS f.m.step (decideFlags f.flags (withInputs f.m.inputs (st n).1 (req n)) (st n).2) (st n).2,
    writeMaps f.m.writes (decideFlags f.flags (withInputs f.m.inputs (st n).1 (req n)) (st n).2) (st n).2)

theorem frun_reach {f : FMMachine} (run : FRun f) : ∀ n, FMReach f (run.st n).1 (run.st n).2
  | 0 => run.start
  | n + 1 => by rw [run.next n]; exact FMReach.step _ _ _ (frun_reach run n) (run.allowed n)

-- A variable or map `from`, `to` or the rank reads: read alike before and after a step, if unprimed.
theorem live_reads {f : FMMachine} {l : Live} (hok : liveOk f l = true) {c : C} (hc : c = l.from_ ∨ c = l.to ∨ c = .eq l.rank l.rank)
    (ρ ι : Nat → Nat) (M : Nat → Nat → Nat) :
    (∀ i, occC i c = true → i ∉ l.prime.map (·.2) ∧ (i ∈ l.prime.map (·.1) ∨
        applyS f.m.step (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M i = withInputs f.m.inputs ρ ι i))
      ∧ (∀ mp, occMC mp c = true → mp ∉ l.primeMaps.map (·.2) ∧ (mp ∈ l.primeMaps.map (·.1) ∨
        writeMaps f.m.writes (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M mp = M mp))
      ∧ (∀ i, occC i c = true → withInputs f.m.inputs ρ ι i = ρ i) := by
  simp only [liveOk, Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] at hok
  obtain ⟨⟨_, _⟩, ⟨hfv, hfm⟩, ⟨htv, htm⟩, ⟨hrv, hrm⟩⟩ := hok
  have hv : avoids (liveVars f l) c = true ∧ avoidsMaps (liveMaps f l) c = true := by
    rcases hc with rfl | rfl | rfl
    · exact ⟨hfv, hfm⟩
    · exact ⟨htv, htm⟩
    · exact ⟨hrv, hrm⟩
  have notIn : ∀ i, occC i c = true → i ∉ l.prime.map (·.1) → i ∉ flagVars f.flags ++ f.m.step.map (·.1) := fun i hi hn hm =>
    avoids_occ hv.1 hi (List.mem_append_right _ (List.mem_filter.mpr ⟨hm, by simpa [List.contains_iff_mem] using hn⟩))
  have noIn : ∀ i, occC i c = true → i ∉ f.m.inputs := fun i hi hm => avoids_occ hv.1 hi (List.mem_append_left _ (List.mem_append_right _ hm))
  refine ⟨fun i hi => ⟨fun h => avoids_occ hv.1 hi (List.mem_append_left _ (List.mem_append_left _ h)), ?_⟩, fun mp hmp => ⟨fun h => avoidsMaps_occ hv.2 hmp (List.mem_append_left _ h), ?_⟩,
    fun i hi => withInputs_other (noIn i hi) ρ ι⟩
  · by_cases hp : i ∈ l.prime.map (·.1)
    · exact Or.inl hp
    · right
      have hn := notIn i hi hp
      rw [applyS_other (fun h => hn (List.mem_append_right _ h)), decide_other (fun h => hn (List.mem_append_left _ h)), withInputs_other (noIn i hi)]
  · by_cases hp : mp ∈ l.primeMaps.map (·.1)
    · exact Or.inl hp
    · right
      have hw : mp ∉ f.m.writes.map (·.1) := fun hm => avoidsMaps_occ hv.2 hmp (List.mem_append_right _ (List.mem_filter.mpr ⟨hm, by simpa [List.contains_iff_mem] using hp⟩))
      funext k
      simp only [writeMaps]
      rw [lookup_none (fun w hw' => by simp only [beq_eq_false_iff_ne]; intro he; exact hw (by rw [← he]; exact List.mem_map_of_mem hw'))]

-- Read where `then` reads, a term that reads no primed name is the term before the step.
theorem unprimed_eval {pr pm : List (Nat × Nat)} {e : E} (hv : ∀ i, occE i e = true → i ∉ pr.map (·.2)) (hm : ∀ mp, occME mp e = true → mp ∉ pm.map (·.2))
    (ρ ρ' : Nat → Nat) (M M' : Nat → Nat → Nat) : evalE (primed pr ρ' ρ) (primedMaps pm M' M) e = evalE ρ M e := by
  rw [congrE _ ρ _ e (fun i hi => by
    simp only [primed]
    rw [lookup_none (fun q hq => by simp only [beq_eq_false_iff_ne]; intro he; exact hv i hi (by rw [← he]; exact List.mem_map_of_mem hq))])]
  exact congrME ρ _ M e (fun mp hmp => by
    funext k; simp only [primedMaps]
    rw [lookup_none (fun q hq => by simp only [beq_eq_false_iff_ne]; intro he; exact hm mp hmp (by rw [← he]; exact List.mem_map_of_mem hq))])

/-- Liveness under fairness: if the laws' proof checks, the liveness reads what it may (`liveOk`), and the step law and
the progress goal Lean builds from it check, then along every run that takes the helpful request infinitely often, each
state where `from` holds is followed (then or later) by one where `to` holds. -/
theorem leads_sound (f : FMMachine) (ps : List MEntry) (l : Live) (sinsts : List (Nat × E)) (sproof : List VDef × Tree)
    (pinsts : List (Nat × E)) (pa pc : List VDef × Tree)
    (hl : checkFMMachine f ps = true) (hok : liveOk f l = true)
    (hs : checkStepLaw f ps (liveStay l sinsts sproof) = true) (hp : checkProgress f ps (liveHelp l pinsts pa pc) = true)
    (run : FRun f) (fair : ∀ n, ∃ m, n ≤ m ∧ ∀ i ∈ f.m.inputs, run.req m i = applyS l.req (run.st m).1 (run.st m).2 i) :
    ∀ n, evalC (run.st n).1 (run.st n).2 l.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 l.to = true := by
  have hSL := steplaw_sound f ps _ hl hs
  have hPR := progress_sound f ps _ hl hp
  have hdist : distinct (l.prime.map (·.2)) = true ∧ distinct (l.primeMaps.map (·.2)) = true := by
    simp only [liveOk, Bool.and_eq_true] at hok; exact hok.1
  -- After a step (request ι from ρ, M): `from`, `to` and the rank read primed are read at the next state; the rank read
  -- plain is read at the state before.
  have hC : ∀ c, (c = l.from_ ∨ c = l.to) → ∀ ρ ι M,
      evalC (primed l.prime (applyS f.m.step (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M) (withInputs f.m.inputs ρ ι))
        (primedMaps l.primeMaps (writeMaps f.m.writes (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M) M) (primeC l.prime l.primeMaps c)
      = evalC (applyS f.m.step (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M) (writeMaps f.m.writes (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M) c := by
    intro c hc ρ ι M
    obtain ⟨hv, hm, _⟩ := live_reads hok (c := c) (by rcases hc with h | h; exact Or.inl h; exact Or.inr (Or.inl h)) ρ ι M
    exact primeC_eval _ _ hdist.1 hdist.2 _ _ _ _ c hv hm
  have hR := live_reads hok (c := .eq l.rank l.rank) (by simp)
  have hE : ∀ ρ ι M,
      evalE (primed l.prime (applyS f.m.step (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M) (withInputs f.m.inputs ρ ι))
        (primedMaps l.primeMaps (writeMaps f.m.writes (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M) M) (primeE l.prime l.primeMaps l.rank)
      = evalE (applyS f.m.step (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M) (writeMaps f.m.writes (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M) l.rank := by
    intro ρ ι M
    obtain ⟨hv, hm, _⟩ := hR ρ ι M
    exact primeE_eval _ _ hdist.1 hdist.2 _ _ _ _ l.rank (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h]))
  have hE0 : ∀ ρ ι M,
      evalE (primed l.prime (applyS f.m.step (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M) (withInputs f.m.inputs ρ ι))
        (primedMaps l.primeMaps (writeMaps f.m.writes (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M) M) l.rank = evalE ρ M l.rank := by
    intro ρ ι M
    obtain ⟨hv, hm, hin⟩ := hR ρ ι M
    rw [unprimed_eval (fun i hi => (hv i (by simp [occC, hi])).1) (fun mp h => (hm mp (by simp [occMC, h])).1)]
    exact congrE _ _ M l.rank (fun i hi => hin i (by simp [occC, hi]))
  -- `from` and `to` read the state, not the request.
  have hW : ∀ c, (c = l.from_ ∨ c = l.to) → ∀ ρ ι M, evalC (withInputs f.m.inputs ρ ι) M c = evalC ρ M c := by
    intro c hc ρ ι M
    obtain ⟨_, _, hin⟩ := live_reads hok (c := c) (by rcases hc with h | h; exact Or.inl h; exact Or.inr (Or.inl h)) ρ ι M
    exact congrC _ _ M c hin
  refine leads_of_rank run.st (fun s => evalC s.1 s.2 l.from_ = true) (fun s => evalC s.1 s.2 l.to = true) (fun s => evalE s.1 s.2 l.rank)
    (fun m => ∀ i ∈ f.m.inputs, run.req m i = applyS l.req (run.st m).1 (run.st m).2 i) ?_ ?_ fair
  · intro n hP hnQ
    have h := hSL (run.st n).1 (run.st n).2 (frun_reach run n) (run.req n) (run.allowed n)
      (by simp only [liveStay, liveWhen, evalC, Bool.and_eq_true, Bool.not_eq_true']
          rw [hW _ (Or.inl rfl), hW _ (Or.inr rfl)]
          exact ⟨hP, by simpa using hnQ⟩)
    simp only [liveStay, evalC, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    rw [hC _ (Or.inl rfl), hC _ (Or.inr rfl), hE, hE0] at h
    rw [run.next n]
    exact h
  · intro n hP hnQ hH
    obtain ⟨_, h⟩ := hPR (run.st n).1 (run.st n).2 (frun_reach run n)
      (by simp only [liveHelp, liveWhen, evalC, Bool.and_eq_true, Bool.not_eq_true']; exact ⟨hP, by simpa using hnQ⟩)
    -- The helpful request is the request the run took.
    have hreq : withInputs f.m.inputs (run.st n).1 (applyS (liveHelp l pinsts pa pc).req (run.st n).1 (run.st n).2)
        = withInputs f.m.inputs (run.st n).1 (run.req n) := by
      funext i
      simp only [withInputs]
      split
      · rename_i hi; exact (hH i (List.contains_iff_mem.mp hi)).symm
      · rfl
    simp only [liveHelp] at h hreq
    rw [hreq] at h
    simp only [evalC, Bool.or_eq_true, decide_eq_true_eq] at h
    rw [hC _ (Or.inr rfl), hE, hE0] at h
    rw [run.next n]
    exact h

end Kern

#print axioms Kern.leads_sound

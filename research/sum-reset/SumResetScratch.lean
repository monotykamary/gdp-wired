import Sums
/-!
Scratch Lean 4.34.0 proof for conditional zero-reset guards in `SumMachine` (`neon-sums` Step 1).
Imports `Sums` without modifying any trusted file (`lean-kernel/*.lean` or `kernel/kernel.ts`).

Proves:
1. `Kern.isSum_reset`: the 2-branch finite-sum step combining `isSum_zero` and `isSum_change`.
2. `Kern.SumReset`: the full `SumDeclR` / `SumMachineR` machine-level soundness theorems
   (`sum_stepR`, `sum_cellsR`, `sum_holdsR`, `sum_allowedR`, `sum_lawsR`, `sum_project_lawsR`,
   `sumleads_soundR`, `sumleads_wf_soundR`, `sumleads_sf_soundR`).
3. Concrete `decide +kernel` sanity checks on a minimal put/clear machine (accepted) and
   four mutant classes (key-dependent guard, partial wipe, reset that also writes, guard reading
   a summed cell) all rejected (`checkSumsR = false`).
4. `#print axioms` audit (must be only `[propext, Classical.choice, Quot.sound]`).
-/
namespace Kern
open Classical

/-- Two-branch finite-sum preservation: if `r = true` drives every key's value to `0` (`isSum_zero`),
and `r = false` keeps every key outside `cs` unchanged (`isSum_change`), then the new function sums
to `if r then 0 else s + dsum f' cs - dsum f cs`. -/
theorem isSum_reset {f f' : Nat → Nat} {s : Nat} (r : Bool) (cs : List Nat) (h : IsSum f s)
    (hzero : r = true → ∀ k, f' k = 0)
    (hag : r = false → ∀ k, k ∉ cs → f' k = f k) :
    IsSum f' (if r then 0 else s + dsum f' cs - dsum f cs) := by
  cases r with
  | true => exact isSum_zero (hzero rfl)
  | false => exact isSum_change cs h (hag rfl)

namespace SumReset

structure SumDeclR where
  v : Nat          -- the sum's state variable
  k : Nat          -- the key the term reads its maps at
  g : E            -- the term at each key
  cs : List E      -- the cover keys: every key a step may change the term at when not resetting
  reset : Option C -- optional key-independent reset guard: when true, gAfter is 0 at every key
  q : Nat          -- the quantified flag
  w : Nat          -- its witness
  x : Nat          -- the key a cover or reset goal reads

structure SumMachineR where
  s : SMachine
  sums : List SumDeclR

def gHereR (d : SumDeclR) (t : E) : E := substE [(d.k, t)] d.g
def gAfterR (s : SMachine) (d : SumDeclR) (t : E) : E := substRE [(d.k, t)] (postRd s) d.g

-- A map read after a step with plain flags inlined, over the pre-flag view X.
def postRdInlined (s : SMachine) : Nat → E → E := fun mp key =>
  match lookup (fun w => w.1 == mp) s.every with
  | some w => substE [(w.2.1, key)] (inlineE s.f.flags w.2.2)
  | none => match lookup (fun w => w.1 == mp) s.f.m.writes with
    | some w => .ite (.eq key (inlineE s.f.flags w.2.1)) (inlineE s.f.flags w.2.2) (.get mp key)
    | none => .get mp key

def gAfterInlined (s : SMachine) (d : SumDeclR) (t : E) : E :=
  substRE [(d.k, t)] (postRdInlined s) d.g

def sumNextR (s : SMachine) (d : SumDeclR) : E :=
  let delta := .sub (.add (.var d.v) (dTermE (gAfterR s d) d.cs)) (dTermE (gHereR d) d.cs)
  match d.reset with
  | none => delta
  | some r => .ite r (.const 0) delta

def sumFactR (d : SumDeclR) : C := .le (dTermE (gHereR d) d.cs) (.var d.v)
def sumBodyR (s : SMachine) (d : SumDeclR) : C :=
  .le (dTermE (gHereR d) (.var d.k :: d.cs.map (inlineE s.f.flags))) (.var d.v)

def sumsCR : List SumDeclR → C
  | [] => trueC
  | d :: ds => .and (.and (sumFactR d) (.eq (.var d.q) (.const 1))) (sumsCR ds)

def SumMachineR.plain (h : SumMachineR) : SMachine :=
  { h.s with
    f := ⟨{ h.s.f.m with
      init := h.s.f.m.init ++ h.sums.map (fun d => (d.v, .const 0)),
      step := h.s.f.m.step ++ h.sums.map (fun d => (d.v, sumNextR h.s d)),
      assume := .and h.s.f.m.assume (sumsCR h.sums) }, h.s.f.flags⟩,
    qflags := h.s.qflags ++ h.sums.map (fun d => (d.q, [d.k], sumBodyR h.s d)),
    wits := h.s.wits ++ h.sums.map (fun d => (d.q, [d.w])) }

def coverWsR (s : SMachine) (d : SumDeclR) : List (Nat × Nat × E) :=
  s.every.filter (fun w => occME w.1 d.g)

def cellLawsR (ps : List SEntry) (d : SumDeclR) : List C := ps.filterMap fun e =>
  match e.law.key with
  | some kv => if e.keys2.isEmpty && gOkC kv e.law.holds && (mapsC e.law.holds).all (fun mp => (mapsE d.g).contains mp)
      then some (substC [(kv, .var d.x)] e.law.holds) else none
  | none => none

-- Under the rule's assumption and ¬reset, at any key x outside the cover, each every-write keeps the cell.
def sumCoverGoalR (s : SMachine) (ps : List SEntry) (d : SumDeclR) (w : Nat × Nat × E) : List C :=
  [inlineC s.f.flags s.f.m.assume]
    ++ (match d.reset with | none => [] | some r => [.not (inlineC s.f.flags r)])
    ++ cellLawsR ps d
    ++ d.cs.map (fun c => .not (.eq (.var d.x) (inlineE s.f.flags c)))
    ++ [.not (.eq (substE [(w.2.1, .var d.x)] (inlineE s.f.flags w.2.2)) (.get w.1 (.var d.x)))]

-- Under the rule's assumption and reset, at any key x, the post-step summand is 0.
def sumResetGoalR (s : SMachine) (ps : List SEntry) (d : SumDeclR) (r : C) : List C :=
  [inlineC s.f.flags s.f.m.assume, inlineC s.f.flags r]
    ++ cellLawsR ps d
    ++ [.not (.eq (gAfterInlined s d (.var d.x)) (.const 0))]

-- Side conditions on `d.reset`:
-- - `avoids [d.k] r`, `avoids [d.x] (inlineC s.f.flags r)`, and `avoids [w.2.1] (inlineC s.f.flags r)` for every
--   `each`-write `w ∈ coverWsR s d`: key-independent (never reads the sum key, cover key, or write key).
-- - `avoidsMaps (mapsE d.g) (inlineC s.f.flags r)`: never reads any map the sum aggregates over (even through flags).
def resetOk (s : SMachine) (d : SumDeclR) : Bool :=
  match d.reset with
  | none => true
  | some r =>
      avoids [d.k] r
      && avoids [d.x] (inlineC s.f.flags r)
      && (coverWsR s d).all (fun w => avoids [w.2.1] (inlineC s.f.flags r))
      && avoidsMaps (mapsE d.g) (inlineC s.f.flags r)
      && s.f.m.writes.all (fun w => !occME w.1 d.g || (avoidsE [d.x] (inlineE s.f.flags w.2.1) && avoidsE [d.x] (inlineE s.f.flags w.2.2)))

def sumOk1R (h : SumMachineR) (d : SumDeclR) : Bool :=
  let s := h.s
  gOkE d.k d.g
    && (mapsE d.g).all (fun mp => (s.f.m.maps0.map (·.1)).contains mp)
    && evalE (fun _ => 0) (fun mp _ => startVal s mp) d.g == 0
    && avoidsMapsE s.carried d.g
    && s.f.m.writes.all (fun w => !occME w.1 d.g || d.cs.any (fun c => beqE c w.2.1))
    && (coverWsR s d).all (fun w => s.f.flags.all (fun p => !occC w.2.1 p.2) && !(flagVars s.f.flags).contains w.2.1
        && avoidsE [d.x] (inlineE s.f.flags w.2.2) && d.x != w.2.1)
    && d.cs.all (fun c => avoidsE [d.k] c && avoidsE [d.x] (inlineE s.f.flags c))
    && avoids [d.x] (inlineC s.f.flags s.f.m.assume)
    && !(s.f.m.inputs ++ flagVars s.f.flags ++ h.plain.qVars ++ h.plain.wVars ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains d.v
    && d.v != d.k
    && resetOk s d

def sumOkR (h : SumMachineR) : Bool := distinct (h.sums.map (·.v)) && h.sums.all (sumOk1R h)

def checkSumReset (s : SMachine) (ps : List SEntry) (d : SumDeclR) (rt : Option (List VDef × Tree)) : Bool :=
  match d.reset, rt with
  | none, none => true
  | some r, some t => checkGoal ⟨t.1, sumResetGoalR s ps d r⟩ t.2
  | _, _ => false

def checkSumsR (h : SumMachineR) (ps : List SEntry)
    (covers : List (List (List VDef × Tree) × Option (List VDef × Tree))) : Bool :=
  sumOkR h && covers.length == h.sums.length
    && (h.sums.zip covers).all (fun p =>
      (coverWsR h.s p.1).length == p.2.1.length
        && ((coverWsR h.s p.1).zip p.2.1).all (fun x => checkGoal ⟨x.2.1, sumCoverGoalR h.s ps p.1 x.1⟩ x.2.2)
        && checkSumReset h.s ps p.1 p.2.2)

/-! Helper lemmas -/

theorem sumOk1R_parts {h : SumMachineR} {d : SumDeclR} (hd : sumOk1R h d = true) :
    gOkE d.k d.g = true
    ∧ (∀ mp ∈ mapsE d.g, mp ∈ h.s.f.m.maps0.map (·.1))
    ∧ evalE (fun _ => 0) (fun mp _ => startVal h.s mp) d.g = 0
    ∧ avoidsMapsE h.s.carried d.g = true
    ∧ (∀ w ∈ h.s.f.m.writes, occME w.1 d.g = true → ∃ c ∈ d.cs, beqE c w.2.1 = true)
    ∧ (∀ w ∈ coverWsR h.s d, (∀ p ∈ h.s.f.flags, occC w.2.1 p.2 = false) ∧ w.2.1 ∉ flagVars h.s.f.flags
        ∧ avoidsE [d.x] (inlineE h.s.f.flags w.2.2) = true ∧ d.x ≠ w.2.1)
    ∧ (∀ c ∈ d.cs, avoidsE [d.k] c = true ∧ avoidsE [d.x] (inlineE h.s.f.flags c) = true)
    ∧ avoids [d.x] (inlineC h.s.f.flags h.s.f.m.assume) = true
    ∧ d.v ∉ h.s.f.m.inputs ++ flagVars h.s.f.flags ++ h.plain.qVars ++ h.plain.wVars ++ h.s.f.m.init.map (·.1) ++ h.s.f.m.step.map (·.1)
    ∧ d.v ≠ d.k
    ∧ resetOk h.s d = true := by
  simp only [sumOk1R, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne, ne_eq,
    Bool.or_eq_true, List.contains_iff_mem] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hg, hm⟩, h0⟩, hc⟩, hw⟩, hev⟩, hcs⟩, ha⟩, hv⟩, hvk⟩, hr⟩ := hd
  refine ⟨hg, hm, h0, hc, fun w hw' ho => ?_, fun w hw' => ?_, hcs, ha, ?_, hvk, hr⟩
  · rcases hw w hw' with h1 | h1
    · simp [h1] at ho
    · exact h1
  · obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hev w hw'
    exact ⟨fun p hp => by simpa using h1 p hp, by simpa using h2, h3, h4⟩
  · intro hm'; simp_all

theorem resetOk_parts {s : SMachine} {d : SumDeclR} {r : C} (hr : d.reset = some r) (hok : resetOk s d = true) :
    avoids [d.k] r = true
    ∧ avoids [d.x] (inlineC s.f.flags r) = true
    ∧ (∀ w ∈ coverWsR s d, avoids [w.2.1] (inlineC s.f.flags r) = true)
    ∧ avoidsMaps (mapsE d.g) (inlineC s.f.flags r) = true
    ∧ ∀ w ∈ s.f.m.writes, occME w.1 d.g = true →
        avoidsE [d.x] (inlineE s.f.flags w.2.1) = true ∧ avoidsE [d.x] (inlineE s.f.flags w.2.2) = true := by
  simp only [resetOk, hr, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨hk, hx⟩, hwk⟩, hm⟩, hw⟩ := hok
  refine ⟨hk, hx, hwk, hm, fun w hwm ho => ?_⟩
  rcases hw w hwm with h1 | h1
  · simp [h1] at ho
  · exact h1

theorem sumOkR_parts {h : SumMachineR} (hok : sumOkR h = true) :
    distinct (h.sums.map (·.v)) = true ∧ ∀ d ∈ h.sums, sumOk1R h d = true := by
  simp only [sumOkR, Bool.and_eq_true, List.all_eq_true] at hok; exact hok

theorem checkSumsR_parts {h : SumMachineR} {ps : List SEntry}
    {covers : List (List (List VDef × Tree) × Option (List VDef × Tree))}
    (hc : checkSumsR h ps covers = true) :
    sumOkR h = true
    ∧ (∀ d ∈ h.sums, ∀ w ∈ coverWsR h.s d, ∃ t : List VDef × Tree, checkGoal ⟨t.1, sumCoverGoalR h.s ps d w⟩ t.2 = true)
    ∧ (∀ d ∈ h.sums, ∀ r, d.reset = some r → ∃ t : List VDef × Tree, checkGoal ⟨t.1, sumResetGoalR h.s ps d r⟩ t.2 = true) := by
  simp only [checkSumsR, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨hok, hlen⟩, hall⟩ := hc
  refine ⟨hok, fun d hd w hw => ?_, fun d hd r hr => ?_⟩
  · obtain ⟨cl, hcl⟩ := zip_cover h.sums covers hlen.symm d hd
    obtain ⟨⟨hl2, hall2⟩, _⟩ := hall _ hcl
    obtain ⟨t, ht⟩ := zip_cover (coverWsR h.s d) cl.1 hl2 w hw
    exact ⟨t, hall2 _ ht⟩
  · obtain ⟨cl, hcl⟩ := zip_cover h.sums covers hlen.symm d hd
    obtain ⟨_, hres⟩ := hall _ hcl
    simp only [checkSumReset, hr] at hres
    cases hrt : cl.2 with
    | none => simp [hrt] at hres
    | some t => simp only [hrt] at hres; exact ⟨t, hres⟩

theorem assoc_sumsR (F : SumDeclR → E) {ds : List SumDeclR} (hd : distinct (ds.map (·.v)) = true) {d : SumDeclR} (hm : d ∈ ds) :
    assoc (ds.map (fun d => (d.v, F d))) d.v = some (F d) := by
  have hd' : distinct ((ds.map (fun d => (d.v, F d))).map (·.1)) = true := by rw [List.map_map]; exact hd
  have := lookup_unique_fst hd' (List.mem_map_of_mem (f := fun d => (d.v, F d)) hm)
  simp only [assoc, this, Option.map_some]

-- Structural evaluation of `substRE [(k, t)] rd` on any `gOkE k` term / `gOkC k` condition, requiring `rd` agreement
-- only on maps actually occurring in the term.
mutual
theorem substRE_gOkE (k : Nat) (t : E) (rd : Nat → E → E) (W : Nat → Nat) (N M' : Nat → Nat → Nat) :
    (e : E) → gOkE k e = true →
    (∀ mp, occME mp e = true → evalE W N (rd mp t) = M' mp (evalE W N t)) →
    evalE W N (substRE [(k, t)] rd e) = evalE (fun _ => 0) (fun mp _ => M' mp (evalE W N t)) e
  | .var _, hg, _ => by simp [gOkE] at hg
  | .const _, _, _ => rfl
  | .add a b, hg, hrd => by
      simp only [gOkE, Bool.and_eq_true] at hg
      simp only [substRE, evalE,
        substRE_gOkE k t rd W N M' a hg.1 (fun mp hm => hrd mp (by simp [occME, hm])),
        substRE_gOkE k t rd W N M' b hg.2 (fun mp hm => hrd mp (by simp [occME, hm]))]
  | .sub a b, hg, hrd => by
      simp only [gOkE, Bool.and_eq_true] at hg
      simp only [substRE, evalE,
        substRE_gOkE k t rd W N M' a hg.1 (fun mp hm => hrd mp (by simp [occME, hm])),
        substRE_gOkE k t rd W N M' b hg.2 (fun mp hm => hrd mp (by simp [occME, hm]))]
  | .mul _ a, hg, hrd => by
      simp only [gOkE] at hg
      simp only [substRE, evalE, substRE_gOkE k t rd W N M' a hg (fun mp hm => hrd mp (by simp [occME, hm]))]
  | .min a b, hg, hrd => by
      simp only [gOkE, Bool.and_eq_true] at hg
      simp only [substRE, evalE,
        substRE_gOkE k t rd W N M' a hg.1 (fun mp hm => hrd mp (by simp [occME, hm])),
        substRE_gOkE k t rd W N M' b hg.2 (fun mp hm => hrd mp (by simp [occME, hm]))]
  | .max a b, hg, hrd => by
      simp only [gOkE, Bool.and_eq_true] at hg
      simp only [substRE, evalE,
        substRE_gOkE k t rd W N M' a hg.1 (fun mp hm => hrd mp (by simp [occME, hm])),
        substRE_gOkE k t rd W N M' b hg.2 (fun mp hm => hrd mp (by simp [occME, hm]))]
  | .prod a b, hg, hrd => by
      simp only [gOkE, Bool.and_eq_true] at hg
      simp only [substRE, evalE,
        substRE_gOkE k t rd W N M' a hg.1 (fun mp hm => hrd mp (by simp [occME, hm])),
        substRE_gOkE k t rd W N M' b hg.2 (fun mp hm => hrd mp (by simp [occME, hm]))]
  | .ite c a b, hg, hrd => by
      simp only [gOkE, Bool.and_eq_true] at hg
      simp only [substRE, evalE,
        substRC_gOkC k t rd W N M' c hg.1.1 (fun mp hm => hrd mp (by simp [occME, hm])),
        substRE_gOkE k t rd W N M' a hg.1.2 (fun mp hm => hrd mp (by simp [occME, hm])),
        substRE_gOkE k t rd W N M' b hg.2 (fun mp hm => hrd mp (by simp [occME, hm]))]
  | .get mp key, hg, hrd => by
      cases key with
      | var i =>
        simp only [gOkE, beq_iff_eq] at hg
        subst hg
        simp only [substRE, assoc, lookup, beq_self_eq_true, evalE]
        exact hrd mp (by simp [occME])
      | _ => simp [gOkE] at hg
  | .tup a b, hg, hrd => by
      simp only [gOkE, Bool.and_eq_true] at hg
      simp only [substRE, evalE,
        substRE_gOkE k t rd W N M' a hg.1 (fun mp hm => hrd mp (by simp [occME, hm])),
        substRE_gOkE k t rd W N M' b hg.2 (fun mp hm => hrd mp (by simp [occME, hm]))]
  | .proj _ a, hg, hrd => by
      simp only [gOkE] at hg
      simp only [substRE, evalE, substRE_gOkE k t rd W N M' a hg (fun mp hm => hrd mp (by simp [occME, hm]))]

theorem substRC_gOkC (k : Nat) (t : E) (rd : Nat → E → E) (W : Nat → Nat) (N M' : Nat → Nat → Nat) :
    (c : C) → gOkC k c = true →
    (∀ mp, occMC mp c = true → evalE W N (rd mp t) = M' mp (evalE W N t)) →
    evalC W N (substRC [(k, t)] rd c) = evalC (fun _ => 0) (fun mp _ => M' mp (evalE W N t)) c
  | .le a b, hg, hrd => by
      simp only [gOkC, Bool.and_eq_true] at hg
      simp only [substRC, evalC,
        substRE_gOkE k t rd W N M' a hg.1 (fun mp hm => hrd mp (by simp [occMC, hm])),
        substRE_gOkE k t rd W N M' b hg.2 (fun mp hm => hrd mp (by simp [occMC, hm]))]
  | .lt a b, hg, hrd => by
      simp only [gOkC, Bool.and_eq_true] at hg
      simp only [substRC, evalC,
        substRE_gOkE k t rd W N M' a hg.1 (fun mp hm => hrd mp (by simp [occMC, hm])),
        substRE_gOkE k t rd W N M' b hg.2 (fun mp hm => hrd mp (by simp [occMC, hm]))]
  | .eq a b, hg, hrd => by
      simp only [gOkC, Bool.and_eq_true] at hg
      simp only [substRC, evalC,
        substRE_gOkE k t rd W N M' a hg.1 (fun mp hm => hrd mp (by simp [occMC, hm])),
        substRE_gOkE k t rd W N M' b hg.2 (fun mp hm => hrd mp (by simp [occMC, hm]))]
  | .and a b, hg, hrd => by
      simp only [gOkC, Bool.and_eq_true] at hg
      simp only [substRC, evalC,
        substRC_gOkC k t rd W N M' a hg.1 (fun mp hm => hrd mp (by simp [occMC, hm])),
        substRC_gOkC k t rd W N M' b hg.2 (fun mp hm => hrd mp (by simp [occMC, hm]))]
  | .or a b, hg, hrd => by
      simp only [gOkC, Bool.and_eq_true] at hg
      simp only [substRC, evalC,
        substRC_gOkC k t rd W N M' a hg.1 (fun mp hm => hrd mp (by simp [occMC, hm])),
        substRC_gOkC k t rd W N M' b hg.2 (fun mp hm => hrd mp (by simp [occMC, hm]))]
  | .not a, hg, hrd => by
      simp only [gOkC] at hg
      simp only [substRC, evalC, substRC_gOkC k t rd W N M' a hg (fun mp hm => hrd mp (by simp [occMC, hm]))]
end

theorem gHereR_eval (d : SumDeclR) (hg : gOkE d.k d.g = true) (W : Nat → Nat) (N : Nat → Nat → Nat) (t : E) :
    evalE W N (gHereR d t) = gAt d.g N (evalE W N t) := by
  rw [gHereR, subst_evalE, applyS_single, gAt_eval hg, upd_at]

theorem gAfterR_eval (h : SumMachineR) (d : SumDeclR) (hg : gOkE d.k d.g = true) (W : Nat → Nat) (N : Nat → Nat → Nat) (t : E) :
    evalE W N (gAfterR h.s d t) = gAt d.g (everyMaps h.s W N) (evalE W N t) := by
  have hpost : ∀ mp, occME mp d.g = true → evalE W N (postRd h.s mp t) = everyMaps h.s W N mp (evalE W N t) := by
    intro mp _
    simp only [postRd, everyMaps]
    cases hl : lookup (fun w => w.1 == mp) h.s.every with
    | some w => simp only [subst_evalE, applyS_single]
    | none =>
      simp only [writeMaps]
      cases hl2 : lookup (fun w => w.1 == mp) h.s.f.m.writes with
      | some w => simp only [evalE, evalC]; by_cases hk : evalE W N t = evalE W N w.2.1 <;> simp [hk]
      | none => rfl
  exact substRE_gOkE d.k t (postRd h.s) W N (everyMaps h.s W N) d.g hg hpost

theorem gAtR_carried (h : SumMachineR) (d : SumDeclR) (hc : avoidsMapsE h.s.carried d.g = true) (M κ : Nat → Nat → Nat) :
    gAt d.g (withCarried h.s M κ) = gAt d.g M := by
  funext key
  apply gAt_congr; intro mp hmp
  simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using avoidsMapsE_occ hc hmp)]

theorem cellLawR_holds {ps : List SEntry} {d : SumDeclR} {c : C} (hc : c ∈ cellLawsR ps d) {carried : List Nat}
    (hcar : ∀ e ∈ ps, avoidsMaps carried e.law.holds = true) {ρ : Nat → Nat} {M : Nat → Nat → Nat} (hlaws : ∀ e ∈ ps, e.Holds ρ M)
    (W : Nat → Nat) (N : Nat → Nat → Nat) (hN : ∀ mp, mp ∉ carried → N mp (W d.x) = M mp (W d.x)) : evalC W N c = true := by
  obtain ⟨e, he, hsome⟩ := List.mem_filterMap.mp hc
  cases hk : e.law.key with
  | none => simp [hk] at hsome
  | some kv =>
    simp only [hk] at hsome
    split at hsome
    · rename_i hif
      simp only [Option.some.injEq] at hsome
      subst hsome
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hif
      obtain ⟨⟨hk2, hg⟩, _⟩ := hif
      have hl := hlaws e he
      simp only [SEntry.Holds, hk2, holdsOver, MLaw.Holds, hk] at hl
      have h1 := hl (W d.x)
      rw [g_sliceC kv _ M _ hg] at h1
      rw [subst_evalC, applyS_single, g_sliceC kv _ N _ hg]
      simp only [evalE, upd_at] at h1 ⊢
      rw [congrMC _ _ _ _ (fun mp hmp => funext fun _ => hN mp (avoidsMaps_occ (hcar e he) hmp))]
      exact h1
    · simp at hsome

theorem view_vR (h : SumMachineR) {d : SumDeclR}
    (hv : d.v ∉ h.s.f.m.inputs ++ flagVars h.s.f.flags ++ h.plain.qVars ++ h.plain.wVars ++ h.s.f.m.init.map (·.1) ++ h.s.f.m.step.map (·.1))
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) : (sView h.plain ρ M ι κ).1 d.v = ρ d.v := by
  simp only [List.mem_append, not_or] at hv
  show decideFlags h.s.f.flags (decideQ h.plain (withInputs h.s.f.m.inputs ρ ι) (withCarried h.s M κ)) (withCarried h.s M κ) d.v = ρ d.v
  rw [decide_other hv.1.1.1.1.2, decideQ_other hv.1.1.1.2, withInputs_other hv.1.1.1.1.1]

/-- One step allowed by the rule keeps every sum exact, with optional conditional zero-reset. -/
theorem sum_stepR (h : SumMachineR) {ps : List SEntry} {covers : List (List (List VDef × Tree) × Option (List VDef × Tree))}
    (hL : checkSMachine h.plain ps = true) (hc : checkSumsR h ps covers = true) {ρ : Nat → Nat} {M : Nat → Nat → Nat}
    (hsum : ∀ d ∈ h.sums, IsSum (gAt d.g M) (ρ d.v)) (hlaws : ∀ e ∈ ps, e.Holds ρ M) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (ha : evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.s.f.m.assume = true) :
    ∀ d ∈ h.sums, IsSum (gAt d.g (sNext h.plain ρ M ι κ).2) ((sNext h.plain ρ M ι κ).1 d.v) := by
  obtain ⟨hok, hcov, hres⟩ := checkSumsR_parts hc
  obtain ⟨hdist, hall⟩ := sumOkR_parts hok
  intro d hd
  obtain ⟨hg, _, _, hcar, hwr, hev, hcs, hax, hv, _, hrok⟩ := sumOk1R_parts (hall d hd)
  let X := decideQ h.plain (withInputs h.s.f.m.inputs ρ ι) (withCarried h.s M κ)
  let N := withCarried h.s M κ
  let V := decideFlags h.s.f.flags X N
  have hV : (sView h.plain ρ M ι κ).1 = V := rfl
  have hN : (sView h.plain ρ M ι κ).2 = N := rfl
  let M' := everyMaps h.s V N
  have hM' : (sNext h.plain ρ M ι κ).2 = M' := rfl
  let cs' := d.cs.map (evalE V N)
  have hold : evalE V N (dTermE (gHereR d) d.cs) = dsum (gAt d.g M) cs' := by
    rw [dTermE_eval V N d.cs (gHereR d) (gAt d.g N) (fun t => gHereR_eval d hg V N t), gAtR_carried h d hcar]
  have hnew : evalE V N (dTermE (gAfterR h.s d) d.cs) = dsum (gAt d.g M') cs' :=
    dTermE_eval V N d.cs (gAfterR h.s d) (gAt d.g M') (fun t => gAfterR_eval h d hg V N t)
  have hstep_eq : (sNext h.plain ρ M ι κ).1 d.v = evalE V N (sumNextR h.s d) := by
    show applyS (h.s.f.m.step ++ h.sums.map (fun d => (d.v, sumNextR h.s d))) V N d.v = _
    simp only [applyS]
    rw [assoc_after (fun hm => hv (by simp [hm])), assoc_sumsR (sumNextR h.s) hdist hd]
  have hdelta : evalE V N (.sub (.add (.var d.v) (dTermE (gAfterR h.s d) d.cs)) (dTermE (gHereR d) d.cs))
      = ρ d.v + dsum (gAt d.g M') cs' - dsum (gAt d.g M) cs' := by
    simp only [evalE, hold, hnew]
    rw [← hV, view_vR h hv ρ M ι κ]
  -- Non-reset branch: when not resetting, every key outside cs' keeps its cell.
  have hag_when_no_reset :
      (∀ r, d.reset = some r → evalC V N r = false) →
      ∀ key, key ∉ cs' → gAt d.g M' key = gAt d.g M key := by
    intro hno key hkey
    apply gAt_congr; intro mp hmp
    have hNM : N mp key = M mp key := by
      simp only [N, withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using avoidsMapsE_occ hcar hmp)]
    simp only [M', everyMaps]
    cases hl : lookup (fun w => w.1 == mp) h.s.every with
    | some w =>
      obtain ⟨hwm, hw1⟩ := lookup_some hl
      simp only [beq_iff_eq] at hw1
      have hwc : w ∈ coverWsR h.s d := List.mem_filter.mpr ⟨hwm, by rw [hw1]; exact hmp⟩
      obtain ⟨t, ht⟩ := hcov d hd w hwc
      obtain ⟨hfl, hbf, hxv, _⟩ := hev w hwc
      show evalE (upd V w.2.1 key) N w.2.2 = M mp key
      apply Decidable.byContradiction; intro hne
      apply sound ⟨t.1, sumCoverGoalR h.s ps d w⟩ t.2 ht (upd X d.x key) N
      intro c hcm
      simp only [sumCoverGoalR, List.mem_append, List.mem_singleton, List.mem_map] at hcm
      rcases hcm with (((rfl | hnr) | hcl) | ⟨c0, hc0, rfl⟩) | rfl
      · rw [congrC _ X N _ (fun i hi => by simp only [upd]; rw [if_neg (fun he => avoids_occ hax hi (by simp [he]))]), inline_evalC]
        exact ha
      · cases hreset : d.reset with
        | none => simp [hreset] at hnr
        | some r =>
          simp only [hreset, List.mem_singleton] at hnr
          subst hnr
          obtain ⟨_, hrx, _, _, _⟩ := resetOk_parts hreset hrok
          simp only [evalC, Bool.not_eq_true']
          rw [congrC _ X N _ (fun i hi => by simp only [upd]; rw [if_neg (fun he => avoids_occ hrx hi (by simp [he]))]), inline_evalC]
          exact hno r hreset
      · refine cellLawR_holds hcl (carried := h.s.carried) (fun e he => (slaws_avoid hL e.law (List.mem_map_of_mem he)).2) hlaws _ N (fun mp hmp => ?_)
        simp only [upd_at, N, withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmp)]
      · have hc0' := (hcs c0 hc0).2
        simp only [evalC, evalE, upd_at, Bool.not_eq_true', decide_eq_false_iff_not]
        rw [congrE _ X N _ (fun i hi => by simp only [upd]; rw [if_neg (fun he => avoidsE_occ hc0' hi (by simp [he]))]), inline_evalE]
        intro he; exact hkey (List.mem_map.mpr ⟨c0, hc0, he.symm⟩)
      · simp only [evalC, evalE, Bool.not_eq_true', decide_eq_false_iff_not, upd_at]
        rw [subst_evalE, applyS_single]
        simp only [evalE, upd_at]
        rw [congrE _ (upd X w.2.1 key) N _ (fun i hi => by
          simp only [upd]; by_cases hib : i = w.2.1
          · simp [hib]
          · rw [if_neg hib, if_neg hib, if_neg (fun he => avoidsE_occ hxv hi (by simp [he]))]), inline_evalE,
          decide_upd hbf (fun p hp => hfl p hp)]
        intro he; rw [he] at hne; exact hne (by rw [hw1]; exact hNM)
    | none =>
      simp only [writeMaps]
      cases hl2 : lookup (fun w => w.1 == mp) h.s.f.m.writes with
      | some w =>
        obtain ⟨hwm, hw1⟩ := lookup_some hl2
        simp only [beq_iff_eq] at hw1
        obtain ⟨c, hcm, hce⟩ := hwr w hwm (by rw [hw1]; exact hmp)
        have hin : evalE V N w.2.1 ∈ cs' := List.mem_map.mpr ⟨c, hcm, by rw [beqE_eq hce]⟩
        have hne : key ≠ evalE V N w.2.1 := fun he => hkey (by rw [he]; exact hin)
        simp only [if_neg hne]; exact hNM
      | none => exact hNM
  rw [hstep_eq, hM']
  cases hreset : d.reset with
  | none =>
    simp only [sumNextR, hreset, hdelta]
    exact isSum_change cs' (hsum d hd) (hag_when_no_reset (fun _ h' => by simp [hreset] at h'))
  | some r =>
    simp only [sumNextR, hreset, evalE, hold, hnew]
    rw [← hV, view_vR h hv ρ M ι κ]
    obtain ⟨_, hrx, _, _, hwrx⟩ := resetOk_parts hreset hrok
    obtain ⟨tr, htr⟩ := hres d hd r hreset
    have hzero : evalC V N r = true → ∀ key, gAt d.g M' key = 0 := by
      intro hrt key
      apply Decidable.byContradiction; intro hne
      apply sound ⟨tr.1, sumResetGoalR h.s ps d r⟩ tr.2 htr (upd X d.x key) N
      intro c hcm
      simp only [sumResetGoalR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcm
      rcases hcm with ((rfl | rfl) | hcl) | rfl
      · rw [congrC _ X N _ (fun i hi => by simp only [upd]; rw [if_neg (fun he => avoids_occ hax hi (by simp [he]))]), inline_evalC]
        exact ha
      · rw [congrC _ X N _ (fun i hi => by simp only [upd]; rw [if_neg (fun he => avoids_occ hrx hi (by simp [he]))]), inline_evalC]
        exact hrt
      · refine cellLawR_holds hcl (carried := h.s.carried) (fun e he => (slaws_avoid hL e.law (List.mem_map_of_mem he)).2) hlaws _ N (fun mp hmp => ?_)
        simp only [upd_at, N, withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmp)]
      · simp only [evalC, evalE, Bool.not_eq_true']
        have hga : evalE (upd X d.x key) N (gAfterInlined h.s d (.var d.x)) = gAt d.g M' key := by
          have hpost : ∀ mp, occME mp d.g = true →
              evalE (upd X d.x key) N (postRdInlined h.s mp (.var d.x)) = M' mp (evalE (upd X d.x key) N (.var d.x)) := by
            intro mp hmp
            simp only [evalE, upd_at, postRdInlined, M', everyMaps]
            cases hl : lookup (fun w => w.1 == mp) h.s.every with
            | some w =>
              obtain ⟨hwm, hw1⟩ := lookup_some hl
              simp only [beq_iff_eq] at hw1
              have hwc : w ∈ coverWsR h.s d := List.mem_filter.mpr ⟨hwm, by rw [hw1]; exact hmp⟩
              obtain ⟨hfl, hbf, hxv, _⟩ := hev w hwc
              rw [subst_evalE, applyS_single]
              simp only [evalE, upd_at]
              rw [congrE _ (upd X w.2.1 key) N _ (fun i hi => by
                simp only [upd]; by_cases hib : i = w.2.1
                · simp [hib]
                · rw [if_neg hib, if_neg hib, if_neg (fun he => avoidsE_occ hxv hi (by simp [he]))]),
                inline_evalE, decide_upd hbf (fun p hp => hfl p hp)]
            | none =>
              simp only [writeMaps]
              cases hl2 : lookup (fun w => w.1 == mp) h.s.f.m.writes with
              | some w =>
                obtain ⟨hwm, hw1⟩ := lookup_some hl2
                simp only [beq_iff_eq] at hw1
                obtain ⟨hwx1, hwx2⟩ := hwrx w hwm (by rw [hw1]; exact hmp)
                have hk1 : evalE (upd X d.x key) N (inlineE h.s.f.flags w.2.1) = evalE V N w.2.1 := by
                  rw [congrE _ X N _ (fun i hi => by simp only [upd]; rw [if_neg (fun he => avoidsE_occ hwx1 hi (by simp [he]))]), inline_evalE]
                have hk2 : evalE (upd X d.x key) N (inlineE h.s.f.flags w.2.2) = evalE V N w.2.2 := by
                  rw [congrE _ X N _ (fun i hi => by simp only [upd]; rw [if_neg (fun he => avoidsE_occ hwx2 hi (by simp [he]))]), inline_evalE]
                simp only [evalE, evalC, upd_at, hk1, hk2]
                by_cases hk : key = evalE V N w.2.1 <;> simp [hk]
              | none => simp only [evalE, upd_at]
          have hsub := substRE_gOkE d.k (.var d.x) (postRdInlined h.s) (upd X d.x key) N M' d.g hg hpost
          simpa [gAfterInlined, gAt, evalE, upd_at] using hsub
        rw [hga]; exact decide_eq_false hne
    exact isSum_reset (evalC V N r) cs' (hsum d hd) hzero (fun hrf => hag_when_no_reset (fun r' hr' => by
      rw [hreset] at hr'; cases hr'; exact hrf))

theorem sum_startR (h : SumMachineR) {ps : List SEntry} {covers : List (List (List VDef × Tree) × Option (List VDef × Tree))}
    (hc : checkSumsR h ps covers = true) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hM : StartMaps h.plain.f.m M) :
    ∀ d ∈ h.sums, IsSum (gAt d.g M) (applyS h.plain.f.m.init ρ M d.v) := by
  obtain ⟨hok, _, _⟩ := checkSumsR_parts hc
  obtain ⟨hdist, hall⟩ := sumOkR_parts hok
  intro d hd
  obtain ⟨_, hm, h0, _, _, _, _, _, hv, _, _⟩ := sumOk1R_parts (hall d hd)
  have hval : applyS h.plain.f.m.init ρ M d.v = 0 := by
    show applyS (h.s.f.m.init ++ h.sums.map (fun d => (d.v, E.const 0))) ρ M d.v = 0
    simp only [applyS]
    rw [assoc_after (fun hm' => hv (by simp [hm'])), assoc_sumsR (fun _ => E.const 0) hdist hd]
    rfl
  rw [hval]
  refine isSum_zero (fun key => ?_)
  rw [gAt]
  refine Eq.trans (congrME _ _ _ d.g (fun mp hmp => ?_)) h0
  funext _
  obtain ⟨p, hp, hpe⟩ := List.mem_map.mp (hm mp (mapsE_occ mp d.g hmp))
  cases hl : lookup (fun p => p.1 == mp) h.s.f.m.maps0 with
  | none => exact absurd (lookup_none_all hl p hp) (by simp [hpe])
  | some p0 =>
    obtain ⟨hp0, hp0e⟩ := lookup_some hl
    simp only [beq_iff_eq] at hp0e
    simp only [startVal, hl, Option.map_some, Option.getD_some]
    rw [← hp0e]; exact hM p0 hp0 key

theorem q_memR (h : SumMachineR) {d : SumDeclR} (hd : d ∈ h.sums) : (d.q, [d.k], sumBodyR h.s d) ∈ h.plain.qflags :=
  List.mem_append_right _ (List.mem_map.mpr ⟨d, hd, rfl⟩)

theorem sum_factsR (h : SumMachineR) {ps : List SEntry} {covers : List (List (List VDef × Tree) × Option (List VDef × Tree))}
    (hc : checkSumsR h ps covers = true) (hs : sOk h.plain = true) {ρ : Nat → Nat} {M : Nat → Nat → Nat}
    (hsum : ∀ d ∈ h.sums, IsSum (gAt d.g M) (ρ d.v)) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 (sumsCR h.sums) = true := by
  obtain ⟨hok, _, _⟩ := checkSumsR_parts hc
  obtain ⟨_, hall⟩ := sumOkR_parts hok
  obtain ⟨_, hqd, _, _, hdx, _, _⟩ := sOk_parts h.plain hs
  let N := withCarried h.s M κ
  let Wi := withInputs h.s.f.m.inputs ρ ι
  have one : ∀ d ∈ h.sums, evalC (sView h.plain ρ M ι κ).1 N (.and (sumFactR d) (.eq (.var d.q) (.const 1))) = true := by
    intro d hd
    obtain ⟨hg, _, _, hcar, _, _, _, _, hv, hvk, _⟩ := sumOk1R_parts (hall d hd)
    have hvi : d.v ∉ h.s.f.m.inputs := fun hm => hv (by simp [hm])
    simp only [evalC, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · show decide (evalE _ N (dTermE (gHereR d) d.cs) ≤ (sView h.plain ρ M ι κ).1 d.v) = true
      apply decide_eq_true
      rw [dTermE_eval _ N d.cs (gHereR d) (gAt d.g N) (fun t => gHereR_eval d hg _ N t), gAtR_carried h d hcar, view_vR h hv ρ M ι κ]
      exact dsum_le (hsum d hd) _
    · have hqv : d.q ∈ h.plain.qVars := List.mem_map_of_mem (q_memR h hd)
      have hqf : d.q ∉ flagVars h.s.f.flags := fun hm =>
        (distinct_append hdx).2.2 d.q (by simp only [SMachine.extVars, List.mem_append]; exact Or.inl (Or.inr hqv)) hm
      show decideFlags h.s.f.flags (decideQ h.plain Wi N) N d.q = 1
      rw [decide_other hqf, decideQ_of, lookup_unique hqd (q_memR h hd)]
      simp only
      rw [if_pos]
      intro key
      rw [← evalC_iff]
      show decide (evalE _ N (dTermE (gHereR d) (.var d.k :: d.cs.map (inlineE h.s.f.flags))) ≤ atKeys Wi [d.k] key d.v) = true
      apply decide_eq_true
      rw [dTermE_eval _ N _ (gHereR d) (gAt d.g N) (fun t => gHereR_eval d hg _ N t), gAtR_carried h d hcar,
        atKeys_out (show d.v ∉ [d.k] by simpa using hvk)]
      show _ ≤ withInputs h.s.f.m.inputs ρ ι d.v
      rw [withInputs_other hvi]
      exact dsum_le (hsum d hd) _
  have all : ∀ ds : List SumDeclR, (∀ d ∈ ds, d ∈ h.sums) → evalC (sView h.plain ρ M ι κ).1 N (sumsCR ds) = true := by
    intro ds
    induction ds with
    | nil => intro _; rfl
    | cons d ds ih =>
      intro hm
      have h1 := one d (hm d List.mem_cons_self)
      have h2 := ih (fun d' hd' => hm d' (List.mem_cons_of_mem _ hd'))
      show (evalC _ N (.and (sumFactR d) (.eq (.var d.q) (.const 1))) && evalC _ N (sumsCR ds)) = true
      rw [h1, h2]; rfl
  exact all h.sums (fun _ hd => hd)

theorem sum_assumeR (h : SumMachineR) {ps : List SEntry} {covers : List (List (List VDef × Tree) × Option (List VDef × Tree))}
    (hc : checkSumsR h ps covers = true) (hs : sOk h.plain = true) {ρ : Nat → Nat} {M : Nat → Nat → Nat}
    (hsum : ∀ d ∈ h.sums, IsSum (gAt d.g M) (ρ d.v)) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.plain.f.m.assume
      = evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.s.f.m.assume := by
  show (evalC _ _ h.s.f.m.assume && evalC _ _ (sumsCR h.sums)) = _
  rw [sum_factsR h hc hs hsum ι κ, Bool.and_true]

theorem sum_cellsR (h : SumMachineR) {ps : List SEntry} {covers : List (List (List VDef × Tree) × Option (List VDef × Tree))}
    (hl : checkSMachine h.plain ps = true) (hc : checkSumsR h ps covers = true) :
    ∀ ρ M, SReach h.plain ρ M → (∀ d ∈ h.sums, IsSum (gAt d.g M) (ρ d.v)) ∧ ∀ e ∈ ps, e.Holds ρ M := by
  intro ρ M hr
  induction hr with
  | start ρ M hM h0 hfa hpf => exact ⟨sum_startR h hc ρ M hM, smachine_sound h.plain ps hl _ _ (SReach.start ρ M hM h0 hfa hpf)⟩
  | step ρ M ι κ hr' ha ih =>
    have ha0 : evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.s.f.m.assume = true := by
      have : evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 (.and h.s.f.m.assume (sumsCR h.sums)) = true := ha
      simp only [evalC, Bool.and_eq_true] at this; exact this.1
    exact ⟨sum_stepR h hl hc ih.1 ih.2 ι κ ha0, smachine_sound h.plain ps hl _ _ (SReach.step ρ M ι κ hr' ha)⟩

theorem sum_holdsR (h : SumMachineR) {ps : List SEntry} {covers : List (List (List VDef × Tree) × Option (List VDef × Tree))}
    (hl : checkSMachine h.plain ps = true) (hc : checkSumsR h ps covers = true) :
    ∀ ρ M, SReach h.plain ρ M → ∀ d ∈ h.sums, IsSum (gAt d.g M) (ρ d.v) :=
  fun ρ M hr => (sum_cellsR h hl hc ρ M hr).1

theorem sum_allowedR (h : SumMachineR) {ps : List SEntry} {covers : List (List (List VDef × Tree) × Option (List VDef × Tree))}
    (hl : checkSMachine h.plain ps = true) (hc : checkSumsR h ps covers = true) :
    ∀ ρ M, SReach h.plain ρ M → ∀ ι κ, evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.plain.f.m.assume
      = evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.s.f.m.assume :=
  fun ρ M hr ι κ => sum_assumeR h hc (sOk_of hl) (sum_holdsR h hl hc ρ M hr) ι κ

def SumMachineR.ghosts (h : SumMachineR) : SGhosted :=
  ⟨h.s, h.sums.flatMap (fun d => [(d.v, .const 0, .var d.v), (d.q, .const 0, .var d.q)])⟩

theorem ghosts_varsR (h : SumMachineR) {d : SumDeclR} (hd : d ∈ h.sums) : d.v ∈ h.ghosts.vars ∧ d.q ∈ h.ghosts.vars := by
  simp only [SGhosted.vars, SumMachineR.ghosts, List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨⟨_, ⟨d, hd, Or.inl rfl⟩, rfl⟩, ⟨_, ⟨d, hd, Or.inr rfl⟩, rfl⟩⟩

theorem sum_ghost_stepR (h : SumMachineR) (hg : sghostOk h.ghosts = true)
    {ρ ρg : Nat → Nat} (hag : Agree h.ghosts.vars ρg ρ) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    evalC (sView h.plain ρg M ι κ).1 (sView h.plain ρg M ι κ).2 h.s.f.m.assume = evalC (sView h.s ρ M ι κ).1 (sView h.s ρ M ι κ).2 h.s.f.m.assume
      ∧ Agree h.ghosts.vars (sNext h.plain ρg M ι κ).1 (sNext h.s ρ M ι κ).1
      ∧ (sNext h.plain ρg M ι κ).2 = (sNext h.s ρ M ι κ).2 := by
  obtain ⟨_, hn, _, ha, hf, hs, _, hw, he, hq, _⟩ := sghostOk_parts h.ghosts hg
  have hX : Agree h.ghosts.vars (withInputs h.s.f.m.inputs ρg ι) (withInputs h.s.f.m.inputs ρ ι) := fun i hi => by
    simp only [withInputs]; split
    · rfl
    · exact hag i hi
  have hQ : Agree h.ghosts.vars (decideQ h.plain (withInputs h.s.f.m.inputs ρg ι) (withCarried h.s M κ))
      (decideQ h.s (withInputs h.s.f.m.inputs ρ ι) (withCarried h.s M κ)) := by
    intro v hv
    rw [decideQ_of, decideQ_of]
    show (match lookup (fun q => q.1 == v) (h.s.qflags ++ h.sums.map (fun d => (d.q, [d.k], sumBodyR h.s d))) with
      | some q => if ∀ k, holdsC (atKeys (withInputs h.s.f.m.inputs ρg ι) q.2.1 k) (withCarried h.s M κ) q.2.2 then 1 else 0
      | none => withInputs h.s.f.m.inputs ρg ι v) = _
    rw [lookup_append]
    cases hl : lookup (fun q => q.1 == v) h.s.qflags with
    | some q => exact ite_all_congr (fun i hi _ => hX i (avoids_occ (hq q (lookup_some hl).1) hi)) (fun _ _ => rfl)
    | none =>
      have hl2 : lookup (fun q => q.1 == v) (h.sums.map (fun d => (d.q, [d.k], sumBodyR h.s d))) = none := lookup_none (fun x hx => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
        simp only [beq_eq_false_iff_ne]; intro he'; exact hv (by rw [← he']; exact (ghosts_varsR h hd).2))
      simp only [hl2]; exact hX v hv
  have hD : Agree h.ghosts.vars (decideFlags h.s.f.flags (decideQ h.plain (withInputs h.s.f.m.inputs ρg ι) (withCarried h.s M κ)) (withCarried h.s M κ))
      (decideFlags h.s.f.flags (decideQ h.s (withInputs h.s.f.m.inputs ρ ι) (withCarried h.s M κ)) (withCarried h.s M κ)) :=
    decide_agree_on hf (withCarried h.s M κ) hQ
  refine ⟨?_, fun i hi => ?_, ?_⟩
  · show evalC (decideFlags h.s.f.flags (decideQ h.plain (withInputs h.s.f.m.inputs ρg ι) (withCarried h.s M κ)) (withCarried h.s M κ)) _ h.s.f.m.assume = _
    exact congrC _ _ _ _ (fun i hi => hD i (avoids_occ ha hi))
  · have hvi : i ∉ h.sums.map (fun d => d.v) := fun hm => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm; exact hi (ghosts_varsR h hd).1
    show applyS (h.s.f.m.step ++ h.sums.map (fun d => (d.v, sumNextR h.s d))) (decideFlags h.s.f.flags (decideQ h.plain (withInputs h.s.f.m.inputs ρg ι) (withCarried h.s M κ)) (withCarried h.s M κ)) (withCarried h.s M κ) i = _
    rw [applyS_append_other (by simpa using hvi)]
    simp only [sNext, sView, applyS]
    cases hst : assoc h.s.f.m.step i with
    | none => exact hD i hi
    | some e =>
      have hm : (i, e) ∈ h.s.f.m.step := by
        simp only [assoc, Option.map_eq_some_iff] at hst
        obtain ⟨q, hq', rfl⟩ := hst
        obtain ⟨hqm, hqv⟩ := lookup_some hq'
        simp only [beq_iff_eq] at hqv
        rw [← hqv]; exact hqm
      exact congrE _ _ _ e (fun j hj => hD j (avoidsE_occ (hs (i, e) hm) hj))
  · funext mp key
    show everyMaps h.s (decideFlags h.s.f.flags (decideQ h.plain (withInputs h.s.f.m.inputs ρg ι) (withCarried h.s M κ)) (withCarried h.s M κ)) (withCarried h.s M κ) mp key
      = everyMaps h.s (decideFlags h.s.f.flags (decideQ h.s (withInputs h.s.f.m.inputs ρ ι) (withCarried h.s M κ)) (withCarried h.s M κ)) (withCarried h.s M κ) mp key
    simp only [everyMaps]
    cases hl : lookup (fun w => w.1 == mp) h.s.every with
    | some w => exact congrE _ _ _ w.2.2 (fun j hj => upd_agree hD w.2.1 key j (avoidsE_occ (he w (lookup_some hl).1) hj))
    | none =>
      simp only [writeMaps]
      cases hl2 : lookup (fun w => w.1 == mp) h.s.f.m.writes with
      | none => rfl
      | some w =>
        obtain ⟨h1, h2⟩ := hw w (lookup_some hl2).1
        simp only [congrE _ _ _ w.2.1 (fun j hj => hD j (avoidsE_occ h1 hj)), congrE _ _ _ w.2.2 (fun j hj => hD j (avoidsE_occ h2 hj))]

theorem sum_projectR (h : SumMachineR) (hg : sghostOk h.ghosts = true)
    {ps : List SEntry} {covers : List (List (List VDef × Tree) × Option (List VDef × Tree))}
    (hl : checkSMachine h.plain ps = true) (hc : checkSumsR h ps covers = true) :
    ∀ {ρ M}, SReach h.s ρ M → ∃ ρg, SReach h.plain ρg M ∧ Agree h.ghosts.vars ρg ρ := by
  intro ρ M hr
  induction hr with
  | start ρ M hM h0 hfa hpf =>
    refine ⟨applyS h.plain.f.m.init ρ M, SReach.start ρ M hM h0 hfa hpf, fun i hi => ?_⟩
    have hvi : i ∉ h.sums.map (fun d => d.v) := fun hm => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm; exact hi (ghosts_varsR h hd).1
    show applyS (h.s.f.m.init ++ h.sums.map (fun d => (d.v, E.const 0))) ρ M i = applyS h.s.f.m.init ρ M i
    exact applyS_append_other (by simpa using hvi) ρ M
  | step ρ M ι κ _ ha ih =>
    obtain ⟨ρg, hrg, hag⟩ := ih
    obtain ⟨hA, hS, hW⟩ := sum_ghost_stepR h hg hag M ι κ
    refine ⟨_, ?_, hS⟩
    rw [← hW]
    refine SReach.step ρg M ι κ hrg ?_
    rw [sum_allowedR h hl hc ρg M hrg ι κ, hA]; exact ha

theorem sum_project_lawsR (h : SumMachineR) (hg : sghostOk h.ghosts = true)
    (ps : List SEntry) {covers : List (List (List VDef × Tree) × Option (List VDef × Tree))}
    (hl : checkSMachine h.plain ps = true) (hc : checkSumsR h ps covers = true) :
    ∀ ρ M, SReach h.s ρ M → ∀ e ∈ ps, avoids h.ghosts.vars e.law.holds = true → e.Holds ρ M := by
  intro ρ M hr e he hav
  obtain ⟨ρg, hrg, hag⟩ := sum_projectR h hg hl hc hr
  exact sentry_transfer (V := h.ghosts.vars) (MS := []) hav (by simp [avoidsMaps]) (fun i hi => (hag i hi).symm) (fun _ _ => rfl)
    (smachine_sound h.plain ps hl ρg M hrg e he)

theorem sum_lawsR (h : SumMachineR) (ps : List SEntry)
    (covers : List (List (List VDef × Tree) × Option (List VDef × Tree)))
    (hl : checkSMachine h.plain ps = true) (hc : checkSumsR h ps covers = true) :
    ∀ ρ M, SReach h.plain ρ M → (∀ d ∈ h.sums, IsSum (gAt d.g M) (ρ d.v)) ∧ ∀ e ∈ ps, e.Holds ρ M :=
  sum_cellsR h hl hc

structure SumRunR (h : SumMachineR) where
  st : Nat → (Nat → Nat) × (Nat → Nat → Nat)
  req : Nat → SRequest
  start : SReach h.plain (st 0).1 (st 0).2
  allowed : ∀ n, evalC (sView h.plain (st n).1 (st n).2 (req n).1 (req n).2).1 (sView h.plain (st n).1 (st n).2 (req n).1 (req n).2).2 h.s.f.m.assume = true
  next : ∀ n, st (n + 1) = sNext h.plain (st n).1 (st n).2 (req n).1 (req n).2

def SumRunR.plain {h : SumMachineR} {ps : List SEntry} {covers : List (List (List VDef × Tree) × Option (List VDef × Tree))}
    (hl : checkSMachine h.plain ps = true) (hc : checkSumsR h ps covers = true) (run : SumRunR h) : SRun h.plain :=
  have reach : ∀ n, SReach h.plain (run.st n).1 (run.st n).2 := fun n => by
    induction n with
    | zero => exact run.start
    | succ n ih =>
      rw [run.next n]
      exact SReach.step _ _ _ _ ih (by rw [sum_allowedR h hl hc _ _ ih]; exact run.allowed n)
  ⟨run.st, run.req, run.start, fun n => by rw [sum_allowedR h hl hc _ _ (reach n)]; exact run.allowed n, run.next⟩

theorem sumleads_soundR (h : SumMachineR) (covers : List (List (List VDef × Tree) × Option (List VDef × Tree)))
    (ps : List SEntry) (l : Live) (sp cp : SProof) (hp : List SProof)
    (hc : checkSumsR h ps covers = true) (hl : checkSMachine h.plain ps = true) (hok : sliveOk h.plain l = true)
    (hs : checkSKStep h.plain ps (sliveStep l l.pend (liveStayC l) sp) = true) (hcv : checkSKStep h.plain ps (sliveStep l l.pend (liveCoverC l) cp) = true)
    (hh : sliveHelpsOk h.plain ps l hp = true) (run : SumRunR h)
    (fair : ∀ x ∈ l.helps, ∀ n, ∃ m, n ≤ m ∧ ∀ p ∈ x.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 l.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 l.to = true :=
  sleads_sound h.plain ps l sp cp hp hl hok hs hcv hh (run.plain hl hc) fair

theorem sumleads_wf_soundR (h : SumMachineR) (covers : List (List (List VDef × Tree) × Option (List VDef × Tree)))
    (ps : List SEntry) (l : Live) (sp cp : SProof) (hp : List SProof) (ap : List (List (Nat × E) × SProof × List E))
    (hc : checkSumsR h ps covers = true) (hl : checkSMachine h.plain ps = true) (hok : sliveOk h.plain l = true)
    (hs : checkSKStep h.plain ps (sliveStep l l.pend (liveStayC l) sp) = true) (hcv : checkSKStep h.plain ps (sliveStep l l.pend (liveCoverC l) cp) = true)
    (hh : sliveHelpsOk h.plain ps l hp = true) (ha : sliveAllowsOkA h.plain ps l ap h.s.f.m.assume = true) (run : SumRunR h)
    (fair : ∀ x ∈ l.helps, ∀ n, (∀ m, n ≤ m → ∃ ι κ, (∀ p ∈ x.2, ι p.1 = evalE (run.st m).1 (run.st m).2 p.2)
        ∧ evalC (sView h.plain (run.st m).1 (run.st m).2 ι κ).1 (sView h.plain (run.st m).1 (run.st m).2 ι κ).2 h.s.f.m.assume = true) →
      ∃ m, n ≤ m ∧ ∀ p ∈ x.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 l.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 l.to = true :=
  sleads_wf_soundA h.plain ps l sp cp hp ap h.s.f.m.assume hl hok hs hcv hh ha (run.plain hl hc) fair

theorem sumleads_sf_soundR (h : SumMachineR) (covers : List (List (List VDef × Tree) × Option (List VDef × Tree)))
    (ps : List SEntry) (l : Live) (lv : List Nat) (sp cp : SProof) (hp : List SProof) (ap : List (List (Nat × E) × SProof × List E))
    (hc : checkSumsR h ps covers = true) (hl : checkSMachine h.plain ps = true) (hok : sliveOk h.plain l = true)
    (hs : checkSKStep h.plain ps (sliveStep l l.pend (liveStaySC l) sp) = true) (hcv : checkSKStep h.plain ps (sliveStep l l.pend (liveCoverC l) cp) = true)
    (hh : sliveHelpsOkS h.plain ps l lv hp = true) (ha : sliveAllowsOkA h.plain ps l ap h.s.f.m.assume = true) (run : SumRunR h)
    (fair : ∀ x ∈ l.helps, (∀ n, ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 x.1 = true ∧ ∃ ι κ, (∀ p ∈ x.2, ι p.1 = evalE (run.st m).1 (run.st m).2 p.2)
        ∧ evalC (sView h.plain (run.st m).1 (run.st m).2 ι κ).1 (sView h.plain (run.st m).1 (run.st m).2 ι κ).2 h.s.f.m.assume = true) →
      ∀ n, ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 x.1 = true ∧ ∀ p ∈ x.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 l.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 l.to = true :=
  sleads_sf_soundA h.plain ps l lv sp cp hp ap h.s.f.m.assume hl hok hs hcv hh ha (run.plain hl hc) fair

/-! Concrete `decide +kernel` sanity checks (1 positive + 4 syntactic mutant rejections) -/

-- Variables: 0=op, 1=id, 2=val, 3=limit, 4=k$w, 5=S, 6=k$S, 7=?cells$S, 8=w?cells$S, 9=x$S. Map: 0=M.
def exBase (writeVal : E) : SMachine :=
  { f := ⟨{ inputs := [0, 1, 2, 3], init := [], step := [], maps0 := [(0, 0)], writes := [], pre := trueC, assume := trueC }, []⟩,
    carried := [], every := [(0, 4, writeVal)], qflags := [], wits := [], facts := [], pfacts := [] }

-- Good put/clear: if op = 1 then 0 else if op = 0 ∧ k$w = id then val else M[k$w]
def goodWrite : E :=
  .ite (.eq (.var 0) (.const 1)) (.const 0)
    (.ite (.and (.eq (.var 0) (.const 0)) (.eq (.var 4) (.var 1))) (.var 2) (.get 0 (.var 4)))

def goodDecl (reset : Option C) : SumDeclR :=
  { v := 5, k := 6, g := .get 0 (.var 6), cs := [.var 1], reset := reset, q := 7, w := 8, x := 9 }

-- Positive syntactic check: sumOkR accepts good put/clear with reset = (op = 1).
example : sumOkR ⟨exBase goodWrite, [goodDecl (some (.eq (.var 0) (.const 1)))]⟩ = true := by decide +kernel

-- Mutant 1 (key-dependent guard): reset reads k$S (var 6), x$S (var 9), or k$w (var 4) -> sumOkR = false.
example : sumOkR ⟨exBase goodWrite, [goodDecl (some (.lt (.var 6) (.var 3)))]⟩ = false := by decide +kernel
example : sumOkR ⟨exBase goodWrite, [goodDecl (some (.lt (.var 9) (.var 3)))]⟩ = false := by decide +kernel
example : sumOkR ⟨exBase goodWrite, [goodDecl (some (.lt (.var 4) (.var 3)))]⟩ = false := by decide +kernel

-- Mutant 4 (guard reading summed cell): reset reads M[id] = 0 -> sumOkR = false.
example : sumOkR ⟨exBase goodWrite, [goodDecl (some (.and (.eq (.var 0) (.const 1)) (.eq (.get 0 (.var 1)) (.const 0))))]⟩ = false := by decide +kernel

-- Mutant 4b (guard reading summed cell via flag): flag 10 := M[id] = 0, reset = (flag 10 = 1) -> sumOkR = false.
def flagReadBase : SMachine :=
  { f := ⟨{ inputs := [0, 1, 2, 3], init := [], step := [], maps0 := [(0, 0)], writes := [], pre := trueC, assume := trueC },
          [(10, .and (.eq (.var 0) (.const 1)) (.eq (.get 0 (.var 1)) (.const 0)))]⟩,
    carried := [], every := [(0, 4, goodWrite)], qflags := [], wits := [], facts := [], pfacts := [] }
example : sumOkR ⟨flagReadBase, [goodDecl (some (.eq (.var 10) (.const 1)))]⟩ = false := by decide +kernel

end SumReset
end Kern

#print axioms Kern.isSum_reset
#print axioms Kern.SumReset.sum_stepR
#print axioms Kern.SumReset.sum_cellsR
#print axioms Kern.SumReset.sum_holdsR
#print axioms Kern.SumReset.sum_allowedR
#print axioms Kern.SumReset.sum_lawsR
#print axioms Kern.SumReset.sum_project_lawsR
#print axioms Kern.SumReset.sumleads_soundR
#print axioms Kern.SumReset.sumleads_wf_soundR
#print axioms Kern.SumReset.sumleads_sf_soundR

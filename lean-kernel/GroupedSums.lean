import Sums
/-!
Trusted kernel extension for parameter-indexed grouped sums and observer-key elimination
(totals filtered by a key read from the row, e.g. per-tag memory charges or per-subject
message counts).

Two minimal, orthogonal trusted rules on top of `Sums.lean` and `Sets.lean`:
  1. `ParamSumMachine`: generalizes `SumMachine` (`Sums.lean`) in two exact places:
     - `gOkEP ps k`: allows immutable parameter variables `p ∈ ps` inside the integrand `d.g`
       (when `ps = []`, identical to `Sums.lean`'s `gOkE`);
     - `psumStartGoal`: replaces the closed concrete check `evalE (fun _ => 0) ... == 0`
       with a 1-goal kernel certificate `[s.f.m.pre, ¬(atStartE s d.g = 0)]`, certifying that
       the integrand is 0 at every key at start under every parameter valuation satisfying `pre`.
  2. `observer_elim` (`sreach_rebind` + `guardLaw`): for any fresh variable `obs` untouched by
     an `SMachine` `s` (`observerOk s obs = true`) and any group-key term `grp` avoiding `obs`,
     proving `∀ k. grp(k) = obs ⇒ L(k)` (or `grp = obs ⇒ L` for scalar laws) on `s` entails
     `L` on `s`.

Combining (1) and (2) gives `grouped_sum_sound`: a grouped sum indexed by a fresh observer
parameter `obs` proves pointwise row-grouped laws on the unmodified source machine `s`, with
zero ghost maps and zero changes to `Kernel.lean`, `Sets.lean`, or `Sums.lean`.

Native TypeScript twin: `kernel/grouped-sum.ts`.
-/

namespace Kern.GroupedSums
open Classical

/-! ## Piece 1: Parameter-indexed sums (`ParamSumMachine`) -/

-- Integrand admissibility: reads maps only at key `k`, constants, arithmetic/`ite`, and
-- immutable parameters listed in `ps`. When `ps = []`, identical to `Sums.lean`'s `gOkE`.
mutual
def gOkEP (ps : List Nat) (k : Nat) : E → Bool
  | .var i => ps.contains i
  | .const _ => true
  | .add a b => gOkEP ps k a && gOkEP ps k b
  | .sub a b => gOkEP ps k a && gOkEP ps k b
  | .mul _ a => gOkEP ps k a
  | .min a b => gOkEP ps k a && gOkEP ps k b
  | .max a b => gOkEP ps k a && gOkEP ps k b
  | .prod a b => gOkEP ps k a && gOkEP ps k b
  | .ite c t f => gOkCP ps k c && gOkEP ps k t && gOkEP ps k f
  | .get _ key => match key with
    | .var i => i == k
    | _ => false
  | .tup a b => gOkEP ps k a && gOkEP ps k b
  | .proj _ a => gOkEP ps k a

def gOkCP (ps : List Nat) (k : Nat) : C → Bool
  | .le a b => gOkEP ps k a && gOkEP ps k b
  | .lt a b => gOkEP ps k a && gOkEP ps k b
  | .eq a b => gOkEP ps k a && gOkEP ps k b
  | .and a b => gOkCP ps k a && gOkCP ps k b
  | .or a b => gOkCP ps k a && gOkCP ps k b
  | .not a => gOkCP ps k a
end

/-- Value of a parameterized integrand at key `key` under parameter valuation `ρ` and maps `M`. -/
def gAtP (g : E) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (key : Nat) : Nat :=
  evalE ρ (fun mp _ => M mp key) g

mutual
theorem g_sliceEP (ps : List Nat) (k : Nat) (ρ ρ' : Nat → Nat) (M : Nat → Nat → Nat)
    (hp : ∀ p ∈ ps, ρ p = ρ' p) : (e : E) → gOkEP ps k e = true →
    evalE ρ M e = evalE ρ' (fun mp _ => M mp (ρ k)) e
  | .var i, h => by
    simp only [gOkEP, List.contains_iff_mem] at h
    exact hp i h
  | .const _, _ => rfl
  | .add a b, h => by
    simp only [gOkEP, Bool.and_eq_true] at h
    simp only [evalE, g_sliceEP ps k ρ ρ' M hp a h.1, g_sliceEP ps k ρ ρ' M hp b h.2]
  | .sub a b, h => by
    simp only [gOkEP, Bool.and_eq_true] at h
    simp only [evalE, g_sliceEP ps k ρ ρ' M hp a h.1, g_sliceEP ps k ρ ρ' M hp b h.2]
  | .mul _ a, h => by
    simp only [gOkEP] at h
    simp only [evalE, g_sliceEP ps k ρ ρ' M hp a h]
  | .min a b, h => by
    simp only [gOkEP, Bool.and_eq_true] at h
    simp only [evalE, g_sliceEP ps k ρ ρ' M hp a h.1, g_sliceEP ps k ρ ρ' M hp b h.2]
  | .max a b, h => by
    simp only [gOkEP, Bool.and_eq_true] at h
    simp only [evalE, g_sliceEP ps k ρ ρ' M hp a h.1, g_sliceEP ps k ρ ρ' M hp b h.2]
  | .prod a b, h => by
    simp only [gOkEP, Bool.and_eq_true] at h
    simp only [evalE, g_sliceEP ps k ρ ρ' M hp a h.1, g_sliceEP ps k ρ ρ' M hp b h.2]
  | .ite c t f, h => by
    simp only [gOkEP, Bool.and_eq_true] at h
    simp only [evalE, g_sliceCP ps k ρ ρ' M hp c h.1.1, g_sliceEP ps k ρ ρ' M hp t h.1.2,
      g_sliceEP ps k ρ ρ' M hp f h.2]
  | .get m key, h => by
    cases key <;> simp_all [gOkEP, evalE]
  | .tup a b, h => by
    simp only [gOkEP, Bool.and_eq_true] at h
    simp only [evalE, g_sliceEP ps k ρ ρ' M hp a h.1, g_sliceEP ps k ρ ρ' M hp b h.2]
  | .proj _ a, h => by
    simp only [gOkEP] at h
    simp only [evalE, g_sliceEP ps k ρ ρ' M hp a h]

theorem g_sliceCP (ps : List Nat) (k : Nat) (ρ ρ' : Nat → Nat) (M : Nat → Nat → Nat)
    (hp : ∀ p ∈ ps, ρ p = ρ' p) : (c : C) → gOkCP ps k c = true →
    evalC ρ M c = evalC ρ' (fun mp _ => M mp (ρ k)) c
  | .le a b, h => by
    simp only [gOkCP, Bool.and_eq_true] at h
    simp only [evalC, g_sliceEP ps k ρ ρ' M hp a h.1, g_sliceEP ps k ρ ρ' M hp b h.2]
  | .lt a b, h => by
    simp only [gOkCP, Bool.and_eq_true] at h
    simp only [evalC, g_sliceEP ps k ρ ρ' M hp a h.1, g_sliceEP ps k ρ ρ' M hp b h.2]
  | .eq a b, h => by
    simp only [gOkCP, Bool.and_eq_true] at h
    simp only [evalC, g_sliceEP ps k ρ ρ' M hp a h.1, g_sliceEP ps k ρ ρ' M hp b h.2]
  | .and a b, h => by
    simp only [gOkCP, Bool.and_eq_true] at h
    simp only [evalC, g_sliceCP ps k ρ ρ' M hp a h.1, g_sliceCP ps k ρ ρ' M hp b h.2]
  | .or a b, h => by
    simp only [gOkCP, Bool.and_eq_true] at h
    simp only [evalC, g_sliceCP ps k ρ ρ' M hp a h.1, g_sliceCP ps k ρ ρ' M hp b h.2]
  | .not a, h => by
    simp only [gOkCP] at h
    simp only [evalC, g_sliceCP ps k ρ ρ' M hp a h]
end

theorem gAtP_eval {ps : List Nat} {k : Nat} {g : E} (hg : gOkEP ps k g = true)
    {ρ ρ' : Nat → Nat} (hp : ∀ p ∈ ps, ρ p = ρ' p) (M : Nat → Nat → Nat) :
    evalE ρ M g = gAtP g ρ' M (ρ k) :=
  g_sliceEP ps k ρ ρ' M hp g hg

theorem gAtP_congr_maps {g : E} {ρ : Nat → Nat} {M M' : Nat → Nat → Nat} {key : Nat}
    (h : ∀ mp, occME mp g = true → M mp key = M' mp key) :
    gAtP g ρ M key = gAtP g ρ M' key :=
  congrME ρ _ _ g (fun mp hmp => funext fun _ => h mp hmp)

theorem gAtP_congr_env {ps : List Nat} {k : Nat} {g : E} (hg : gOkEP ps k g = true)
    {ρ ρ' : Nat → Nat} (hp : ∀ p ∈ ps, ρ p = ρ' p) (M : Nat → Nat → Nat) (key : Nat) :
    gAtP g ρ M key = gAtP g ρ' M key :=
  g_sliceEP ps k ρ ρ' (fun mp _ => M mp key) hp g hg

-- Replace every map read `get mp _` with its constant start value `startVal s mp`,
-- preserving parameter variables `var p` for the `S @init` goal.
mutual
def atStartE (s : SMachine) : E → E
  | .var i => .var i
  | .const n => .const n
  | .add a b => .add (atStartE s a) (atStartE s b)
  | .sub a b => .sub (atStartE s a) (atStartE s b)
  | .mul k a => .mul k (atStartE s a)
  | .min a b => .min (atStartE s a) (atStartE s b)
  | .max a b => .max (atStartE s a) (atStartE s b)
  | .prod a b => .prod (atStartE s a) (atStartE s b)
  | .ite c t f => .ite (atStartC s c) (atStartE s t) (atStartE s f)
  | .get mp _ => .const (startVal s mp)
  | .tup a b => .tup (atStartE s a) (atStartE s b)
  | .proj i a => .proj i (atStartE s a)

def atStartC (s : SMachine) : C → C
  | .le a b => .le (atStartE s a) (atStartE s b)
  | .lt a b => .lt (atStartE s a) (atStartE s b)
  | .eq a b => .eq (atStartE s a) (atStartE s b)
  | .and a b => .and (atStartC s a) (atStartC s b)
  | .or a b => .or (atStartC s a) (atStartC s b)
  | .not a => .not (atStartC s a)
end

mutual
theorem atStartE_eval (s : SMachine) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (key : Nat) :
    (e : E) → (∀ mp, mp ∈ mapsE e → M mp key = startVal s mp) →
    evalE ρ (fun mp _ => M mp key) e = evalE ρ M (atStartE s e)
  | .var _, _ => rfl
  | .const _, _ => rfl
  | .add a b, h => by
    simp only [atStartE, evalE]
    rw [atStartE_eval s ρ M key a (fun mp hm => h mp (by simp [mapsE, hm])),
        atStartE_eval s ρ M key b (fun mp hm => h mp (by simp [mapsE, hm]))]
  | .sub a b, h => by
    simp only [atStartE, evalE]
    rw [atStartE_eval s ρ M key a (fun mp hm => h mp (by simp [mapsE, hm])),
        atStartE_eval s ρ M key b (fun mp hm => h mp (by simp [mapsE, hm]))]
  | .mul _ a, h => by
    simp only [atStartE, evalE]
    rw [atStartE_eval s ρ M key a (fun mp hm => h mp (by simp [mapsE, hm]))]
  | .min a b, h => by
    simp only [atStartE, evalE]
    rw [atStartE_eval s ρ M key a (fun mp hm => h mp (by simp [mapsE, hm])),
        atStartE_eval s ρ M key b (fun mp hm => h mp (by simp [mapsE, hm]))]
  | .max a b, h => by
    simp only [atStartE, evalE]
    rw [atStartE_eval s ρ M key a (fun mp hm => h mp (by simp [mapsE, hm])),
        atStartE_eval s ρ M key b (fun mp hm => h mp (by simp [mapsE, hm]))]
  | .prod a b, h => by
    simp only [atStartE, evalE]
    rw [atStartE_eval s ρ M key a (fun mp hm => h mp (by simp [mapsE, hm])),
        atStartE_eval s ρ M key b (fun mp hm => h mp (by simp [mapsE, hm]))]
  | .ite c t f, h => by
    simp only [atStartE, evalE]
    rw [atStartC_eval s ρ M key c (fun mp hm => h mp (by simp [mapsE, hm])),
        atStartE_eval s ρ M key t (fun mp hm => h mp (by simp [mapsE, hm])),
        atStartE_eval s ρ M key f (fun mp hm => h mp (by simp [mapsE, hm]))]
  | .get mp _, h => by
    simp only [atStartE, evalE]
    exact h mp (by simp [mapsE])
  | .tup a b, h => by
    simp only [atStartE, evalE]
    rw [atStartE_eval s ρ M key a (fun mp hm => h mp (by simp [mapsE, hm])),
        atStartE_eval s ρ M key b (fun mp hm => h mp (by simp [mapsE, hm]))]
  | .proj _ a, h => by
    simp only [atStartE, evalE]
    rw [atStartE_eval s ρ M key a (fun mp hm => h mp (by simp [mapsE, hm]))]

theorem atStartC_eval (s : SMachine) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (key : Nat) :
    (c : C) → (∀ mp, mp ∈ mapsC c → M mp key = startVal s mp) →
    evalC ρ (fun mp _ => M mp key) c = evalC ρ M (atStartC s c)
  | .le a b, h => by
    simp only [atStartC, evalC]
    rw [atStartE_eval s ρ M key a (fun mp hm => h mp (by simp [mapsC, hm])),
        atStartE_eval s ρ M key b (fun mp hm => h mp (by simp [mapsC, hm]))]
  | .lt a b, h => by
    simp only [atStartC, evalC]
    rw [atStartE_eval s ρ M key a (fun mp hm => h mp (by simp [mapsC, hm])),
        atStartE_eval s ρ M key b (fun mp hm => h mp (by simp [mapsC, hm]))]
  | .eq a b, h => by
    simp only [atStartC, evalC]
    rw [atStartE_eval s ρ M key a (fun mp hm => h mp (by simp [mapsC, hm])),
        atStartE_eval s ρ M key b (fun mp hm => h mp (by simp [mapsC, hm]))]
  | .and a b, h => by
    simp only [atStartC, evalC]
    rw [atStartC_eval s ρ M key a (fun mp hm => h mp (by simp [mapsC, hm])),
        atStartC_eval s ρ M key b (fun mp hm => h mp (by simp [mapsC, hm]))]
  | .or a b, h => by
    simp only [atStartC, evalC]
    rw [atStartC_eval s ρ M key a (fun mp hm => h mp (by simp [mapsC, hm])),
        atStartC_eval s ρ M key b (fun mp hm => h mp (by simp [mapsC, hm]))]
  | .not a, h => by
    simp only [atStartC, evalC]
    rw [atStartC_eval s ρ M key a (fun mp hm => h mp (by simp [mapsC, hm]))]
end

/-! ### Parameterized sum declarations and plain-machine lowering -/

structure ParamSumDecl where
  v  : Nat          -- sum state variable
  k  : Nat          -- summation key variable
  ps : List Nat     -- immutable parameters read by `g` (e.g. `[obs]` for grouped sums)
  g  : E            -- integrand at key `k`
  cs : List E       -- finite cover keys
  q  : Nat          -- quantified flag (`cells$S`)
  w  : Nat          -- witness for `q`
  x  : Nat          -- cover goal key variable

structure ParamSumMachine where
  s    : SMachine
  sums : List ParamSumDecl

def pgHere (d : ParamSumDecl) (t : E) : E := substE [(d.k, t)] d.g
def pgAfter (s : SMachine) (d : ParamSumDecl) (t : E) : E := substRE [(d.k, t)] (postRd s) d.g
def psumNext (s : SMachine) (d : ParamSumDecl) : E :=
  .sub (.add (.var d.v) (dTermE (pgAfter s d) d.cs)) (dTermE (pgHere d) d.cs)
def psumFact (d : ParamSumDecl) : C := .le (dTermE (pgHere d) d.cs) (.var d.v)
def psumBody (s : SMachine) (d : ParamSumDecl) : C :=
  .le (dTermE (pgHere d) (.var d.k :: d.cs.map (inlineE s.f.flags))) (.var d.v)

def psumsC : List ParamSumDecl → C
  | [] => trueC
  | d :: ds => .and (.and (psumFact d) (.eq (.var d.q) (.const 1))) (psumsC ds)

def ParamSumMachine.plain (h : ParamSumMachine) : SMachine :=
  { h.s with
    f := ⟨{ h.s.f.m with
      init := h.s.f.m.init ++ h.sums.map (fun d => (d.v, .const 0)),
      step := h.s.f.m.step ++ h.sums.map (fun d => (d.v, psumNext h.s d)),
      assume := .and h.s.f.m.assume (psumsC h.sums) }, h.s.f.flags⟩,
    qflags := h.s.qflags ++ h.sums.map (fun d => (d.q, [d.k], psumBody h.s d)),
    wits := h.s.wits ++ h.sums.map (fun d => (d.q, [d.w])) }

def pcoverWs (s : SMachine) (d : ParamSumDecl) : List (Nat × Nat × E) :=
  s.every.filter (fun w => occME w.1 d.g)

def pcellLaws (ps : List SEntry) (d : ParamSumDecl) : List C := ps.filterMap fun e =>
  match e.law.key with
  | some kv =>
      if e.keys2.isEmpty && gOkCP d.ps kv e.law.holds && !d.ps.contains kv
          && (mapsC e.law.holds).all (fun mp => (mapsE d.g).contains mp)
      then some (substC [(kv, .var d.x)] e.law.holds) else none
  | none => none

def psumStartGoal (s : SMachine) (d : ParamSumDecl) : List C :=
  [s.f.m.pre, .not (.eq (atStartE s d.g) (.const 0))]

def psumCoverGoal (s : SMachine) (ps : List SEntry) (d : ParamSumDecl) (w : Nat × Nat × E) : List C :=
  [inlineC s.f.flags s.f.m.assume] ++ pcellLaws ps d
    ++ d.cs.map (fun c => .not (.eq (.var d.x) (inlineE s.f.flags c)))
    ++ [.not (.eq (substE [(w.2.1, .var d.x)] (inlineE s.f.flags w.2.2)) (.get w.1 (.var d.x)))]

/-- Static immutability check on every parameter `p ∈ d.ps`: never written by `init`, `step`,
inputs, flags, quantified flags, witnesses, sum vars, or bound as `d.k`/`d.x`. -/
def paramImmutable (h : ParamSumMachine) (d : ParamSumDecl) (p : Nat) : Bool :=
  let s := h.s
  !(s.f.m.inputs ++ flagVars s.f.flags ++ h.plain.qVars ++ h.plain.wVars
      ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1) ++ h.sums.map (·.v)).contains p
    && p != d.k && p != d.x

def paramSumOk1 (h : ParamSumMachine) (d : ParamSumDecl) : Bool :=
  let s := h.s
  gOkEP d.ps d.k d.g
    && d.ps.all (paramImmutable h d)
    && (mapsE d.g).all (fun mp => (s.f.m.maps0.map (·.1)).contains mp)
    && avoidsMapsE s.carried d.g
    && s.f.m.writes.all (fun w => !occME w.1 d.g || d.cs.any (fun c => beqE c w.2.1))
    && (pcoverWs s d).all (fun w => s.f.flags.all (fun p => !occC w.2.1 p.2)
        && !(flagVars s.f.flags).contains w.2.1
        && avoidsE [d.x] (inlineE s.f.flags w.2.2) && d.x != w.2.1)
    && d.cs.all (fun c => avoidsE [d.k] c && avoidsE [d.x] (inlineE s.f.flags c))
    && avoids [d.x] (inlineC s.f.flags s.f.m.assume)
    && !(s.f.m.inputs ++ flagVars s.f.flags ++ h.plain.qVars ++ h.plain.wVars
        ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains d.v
    && d.v != d.k

def paramSumOk (h : ParamSumMachine) : Bool :=
  distinct (h.sums.map (·.v)) && h.sums.all (paramSumOk1 h)

/-- Full check of parameterized sums: static checks, a kernel proof tree for each sum's
`S @init` goal, and a kernel proof tree for each `every`-write `@cover` goal. -/
def checkParamSums (h : ParamSumMachine) (ps : List SEntry)
    (inits : List (List VDef × Tree))
    (covers : List (List (List VDef × Tree))) : Bool :=
  paramSumOk h
    && inits.length == h.sums.length
    && (h.sums.zip inits).all (fun p => checkGoal ⟨p.2.1, psumStartGoal h.s p.1⟩ p.2.2)
    && covers.length == h.sums.length
    && (h.sums.zip covers).all (fun p =>
        (pcoverWs h.s p.1).length == p.2.length
        && ((pcoverWs h.s p.1).zip p.2).all (fun x =>
            checkGoal ⟨x.2.1, psumCoverGoal h.s ps p.1 x.1⟩ x.2.2))

/-! ### Unpacking checks and immutability lemmas -/

theorem paramImmutable_parts {h : ParamSumMachine} {d : ParamSumDecl} {p : Nat}
    (hp : paramImmutable h d p = true) :
    p ∉ h.s.f.m.inputs ++ flagVars h.s.f.flags ++ h.plain.qVars ++ h.plain.wVars
        ++ h.s.f.m.init.map (·.1) ++ h.s.f.m.step.map (·.1) ++ h.sums.map (·.v)
      ∧ p ≠ d.k ∧ p ≠ d.x := by
  simp only [paramImmutable, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  exact ⟨by simpa using h1, h2, h3⟩

theorem paramSumOk1_parts {h : ParamSumMachine} {d : ParamSumDecl} (hd : paramSumOk1 h d = true) :
    gOkEP d.ps d.k d.g = true
    ∧ (∀ p ∈ d.ps, paramImmutable h d p = true)
    ∧ (∀ mp ∈ mapsE d.g, mp ∈ h.s.f.m.maps0.map (·.1))
    ∧ avoidsMapsE h.s.carried d.g = true
    ∧ (∀ w ∈ h.s.f.m.writes, occME w.1 d.g = true → ∃ c ∈ d.cs, beqE c w.2.1 = true)
    ∧ (∀ w ∈ pcoverWs h.s d, (∀ p ∈ h.s.f.flags, occC w.2.1 p.2 = false)
        ∧ w.2.1 ∉ flagVars h.s.f.flags
        ∧ avoidsE [d.x] (inlineE h.s.f.flags w.2.2) = true ∧ d.x ≠ w.2.1)
    ∧ (∀ c ∈ d.cs, avoidsE [d.k] c = true ∧ avoidsE [d.x] (inlineE h.s.f.flags c) = true)
    ∧ avoids [d.x] (inlineC h.s.f.flags h.s.f.m.assume) = true
    ∧ d.v ∉ h.s.f.m.inputs ++ flagVars h.s.f.flags ++ h.plain.qVars ++ h.plain.wVars
        ++ h.s.f.m.init.map (·.1) ++ h.s.f.m.step.map (·.1)
    ∧ d.v ≠ d.k := by
  simp only [paramSumOk1, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.not_eq_true',
    bne_iff_ne, ne_eq, Bool.or_eq_true, List.contains_iff_mem] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hg, hps⟩, hm⟩, hc⟩, hw⟩, hev⟩, hcs⟩, ha⟩, hv⟩, hvk⟩ := hd
  refine ⟨hg, hps, hm, hc, fun w hw' ho => ?_, fun w hw' => ?_, hcs, ha, ?_, hvk⟩
  · rcases hw w hw' with h1 | h1
    · simp [h1] at ho
    · exact h1
  · obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hev w hw'
    exact ⟨fun p hp => by simpa using h1 p hp, by simpa using h2, h3, h4⟩
  · intro hm'; simp_all

theorem paramSumOk_parts {h : ParamSumMachine} (hok : paramSumOk h = true) :
    distinct (h.sums.map (·.v)) = true ∧ ∀ d ∈ h.sums, paramSumOk1 h d = true := by
  simp only [paramSumOk, Bool.and_eq_true, List.all_eq_true] at hok; exact hok

theorem checkParamSums_parts {h : ParamSumMachine} {ps : List SEntry}
    {inits : List (List VDef × Tree)} {covers : List (List (List VDef × Tree))}
    (hc : checkParamSums h ps inits covers = true) :
    paramSumOk h = true
    ∧ (∀ d ∈ h.sums, ∃ t : List VDef × Tree, checkGoal ⟨t.1, psumStartGoal h.s d⟩ t.2 = true)
    ∧ (∀ d ∈ h.sums, ∀ w ∈ pcoverWs h.s d,
        ∃ t : List VDef × Tree, checkGoal ⟨t.1, psumCoverGoal h.s ps d w⟩ t.2 = true) := by
  simp only [checkParamSums, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨hok, hilen⟩, hiall⟩, hclen⟩, hcall⟩ := hc
  refine ⟨hok, fun d hd => ?_, fun d hd w hw => ?_⟩
  · obtain ⟨t, ht⟩ := zip_cover h.sums inits hilen.symm d hd
    exact ⟨t, hiall _ ht⟩
  · obtain ⟨cl, hcl⟩ := zip_cover h.sums covers hclen.symm d hd
    obtain ⟨hl2, hall2⟩ := hcall _ hcl
    obtain ⟨t, ht⟩ := zip_cover (pcoverWs h.s d) cl hl2 w hw
    exact ⟨t, hall2 _ ht⟩

theorem passoc_sums (F : ParamSumDecl → E) {ds : List ParamSumDecl}
    (hd : distinct (ds.map (·.v)) = true) {d : ParamSumDecl} (hm : d ∈ ds) :
    assoc (ds.map (fun d => (d.v, F d))) d.v = some (F d) := by
  have hd' : distinct ((ds.map (fun d => (d.v, F d))).map (·.1)) = true := by
    rw [List.map_map]; exact hd
  have := lookup_unique_fst hd' (List.mem_map_of_mem (f := fun d => (d.v, F d)) hm)
  simp only [assoc, this, Option.map_some]

theorem pview_v (h : ParamSumMachine) {v : Nat}
    (hv : v ∉ h.s.f.m.inputs ++ flagVars h.s.f.flags ++ h.plain.qVars ++ h.plain.wVars
        ++ h.s.f.m.init.map (·.1) ++ h.s.f.m.step.map (·.1))
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    (sView h.plain ρ M ι κ).1 v = ρ v := by
  simp only [List.mem_append, not_or] at hv
  show decideFlags h.s.f.flags
    (decideQ h.plain (withInputs h.s.f.m.inputs ρ ι) (withCarried h.s M κ))
    (withCarried h.s M κ) v = ρ v
  rw [decide_other hv.1.1.1.1.2, decideQ_other hv.1.1.1.2, withInputs_other hv.1.1.1.1.1]

theorem param_init (h : ParamSumMachine) {d : ParamSumDecl} {p : Nat}
    (hp : paramImmutable h d p = true) (ρ : Nat → Nat) (M : Nat → Nat → Nat) :
    applyS h.plain.f.m.init ρ M p = ρ p := by
  obtain ⟨hmem, _, _⟩ := paramImmutable_parts hp
  simp only [List.mem_append, not_or] at hmem
  apply applyS_other
  show p ∉ (h.s.f.m.init ++ h.sums.map (fun d => (d.v, E.const 0))).map (·.1)
  simp only [List.map_append, List.map_map, List.mem_append, not_or]
  exact ⟨hmem.1.1.2, hmem.2⟩

theorem param_view (h : ParamSumMachine) {d : ParamSumDecl} {p : Nat}
    (hp : paramImmutable h d p = true)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    (sView h.plain ρ M ι κ).1 p = ρ p := by
  obtain ⟨hmem, _, _⟩ := paramImmutable_parts hp
  exact pview_v h (fun hm => hmem (List.mem_append_left _ hm)) ρ M ι κ

theorem param_next (h : ParamSumMachine) {d : ParamSumDecl} {p : Nat}
    (hp : paramImmutable h d p = true)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    (sNext h.plain ρ M ι κ).1 p = ρ p := by
  obtain ⟨hmem, _, _⟩ := paramImmutable_parts hp
  simp only [List.mem_append, not_or] at hmem
  show applyS (h.s.f.m.step ++ h.sums.map (fun d => (d.v, psumNext h.s d)))
    (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 p = ρ p
  rw [applyS_other]
  · exact param_view h hp ρ M ι κ
  · simp only [List.map_append, List.map_map, List.mem_append, not_or]
    exact ⟨hmem.1.2, hmem.2⟩

theorem pgHere_eval {d : ParamSumDecl} (hg : gOkEP d.ps d.k d.g = true)
    (hpk : ∀ p ∈ d.ps, p ≠ d.k) {W ρ : Nat → Nat} (hp : ∀ p ∈ d.ps, W p = ρ p)
    (N : Nat → Nat → Nat) (t : E) :
    evalE W N (pgHere d t) = gAtP d.g ρ N (evalE W N t) := by
  rw [pgHere, subst_evalE, applyS_single]
  have h1 : ∀ p ∈ d.ps, upd W d.k (evalE W N t) p = ρ p := fun p hpm => by
    simp only [upd, hpk p hpm, ite_false]; exact hp p hpm
  rw [gAtP_eval hg h1, upd_at]

theorem pgAfter_eval (h : ParamSumMachine) {d : ParamSumDecl} (hg : gOkEP d.ps d.k d.g = true)
    (hpk : ∀ p ∈ d.ps, p ≠ d.k) {W ρ : Nat → Nat} (hp : ∀ p ∈ d.ps, W p = ρ p)
    (N : Nat → Nat → Nat) (t : E) :
    evalE W N (pgAfter h.s d t) = gAtP d.g ρ (everyMaps h.s W N) (evalE W N t) := by
  rw [pgAfter, substR_evalE_on [(d.k, t)] (postRd h.s) W N (everyMaps h.s W N) []
      (fun m key _ => postRd_eval ⟨h.s, []⟩ W N m key) d.g (by simp [avoidsMapsE]),
    applyS_single]
  have h1 : ∀ p ∈ d.ps, upd W d.k (evalE W N t) p = ρ p := fun p hpm => by
    simp only [upd, hpk p hpm, ite_false]; exact hp p hpm
  rw [gAtP_eval hg h1, upd_at]

theorem gAtP_carried (h : ParamSumMachine) {d : ParamSumDecl} (hc : avoidsMapsE h.s.carried d.g = true)
    (ρ : Nat → Nat) (M κ : Nat → Nat → Nat) :
    gAtP d.g ρ (withCarried h.s M κ) = gAtP d.g ρ M := by
  funext key
  apply gAtP_congr_maps; intro mp hmp
  have hnc : mp ∉ h.s.carried := avoidsMapsE_occ hc hmp
  simp [withCarried, hnc]

theorem pcellLaw_holds {ps : List SEntry} {d : ParamSumDecl} {c : C} (hc : c ∈ pcellLaws ps d)
    {carried : List Nat} (hcar : ∀ e ∈ ps, avoidsMaps carried e.law.holds = true)
    {ρ : Nat → Nat} {M : Nat → Nat → Nat} (hlaws : ∀ e ∈ ps, e.Holds ρ M)
    (W : Nat → Nat) (N : Nat → Nat → Nat)
    (hW : ∀ p ∈ d.ps, W p = ρ p)
    (hN : ∀ mp, mp ∉ carried → N mp (W d.x) = M mp (W d.x)) : evalC W N c = true := by
  obtain ⟨e, he, hsome⟩ := List.mem_filterMap.mp hc
  cases hk : e.law.key with
  | none => simp [hk] at hsome
  | some kv =>
    simp only [hk] at hsome
    split at hsome
    · rename_i hif
      simp only [Option.some.injEq] at hsome
      subst hsome
      simp only [Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true'] at hif
      obtain ⟨⟨⟨hk2, hg⟩, hkv⟩, _⟩ := hif
      have hl := hlaws e he
      simp only [SEntry.Holds, hk2, holdsOver, MLaw.Holds, hk] at hl
      have h1 := hl (W d.x)
      have hupd1 : ∀ p ∈ d.ps, upd ρ kv (W d.x) p = ρ p := fun p hp => by
        have hne : p ≠ kv := fun heq => by
          subst heq; rw [List.contains_iff_mem.mpr hp] at hkv; cases hkv
        simp [upd, hne]
      have hupd2 : ∀ p ∈ d.ps, upd W kv (W d.x) p = ρ p := fun p hp => by
        have hne : p ≠ kv := fun heq => by
          subst heq; rw [List.contains_iff_mem.mpr hp] at hkv; cases hkv
        simp [upd, hne, hW p hp]
      rw [g_sliceCP d.ps kv _ ρ M hupd1 _ hg] at h1
      rw [subst_evalC, applyS_single]
      simp only [evalE]
      rw [g_sliceCP d.ps kv _ ρ N hupd2 _ hg]
      simp only [upd_at] at h1 ⊢
      rw [congrMC _ _ _ _ (fun mp hmp => funext fun _ => hN mp (avoidsMaps_occ (hcar e he) hmp))]
      exact h1
    · simp at hsome

/-! ### Exactness of parameterized sums across start and step -/

section param_exact
variable (h : ParamSumMachine)

theorem param_sum_start {ps : List SEntry} {inits : List (List VDef × Tree)}
    {covers : List (List (List VDef × Tree))}
    (hc : checkParamSums h ps inits covers = true)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (hM : StartMaps h.plain.f.m M) (hpre : evalC ρ M h.plain.f.m.pre = true) :
    ∀ d ∈ h.sums, IsSum (gAtP d.g (applyS h.plain.f.m.init ρ M) M) (applyS h.plain.f.m.init ρ M d.v) := by
  obtain ⟨hok, hinit, _⟩ := checkParamSums_parts hc
  obtain ⟨hdist, hall⟩ := paramSumOk_parts hok
  intro d hd
  obtain ⟨hg, hps, hm, _, _, _, _, _, hv, _⟩ := paramSumOk1_parts (hall d hd)
  obtain ⟨t, ht⟩ := hinit d hd
  have hval : applyS h.plain.f.m.init ρ M d.v = 0 := by
    show applyS (h.s.f.m.init ++ h.sums.map (fun d => (d.v, E.const 0))) ρ M d.v = 0
    simp only [applyS]
    rw [assoc_after (fun hm' => hv (by simp [hm'])), passoc_sums (fun _ => E.const 0) hdist hd]
    rfl
  have hzero : evalE ρ M (atStartE h.s d.g) = 0 := by
    apply Decidable.byContradiction; intro hne
    apply sound ⟨t.1, psumStartGoal h.s d⟩ t.2 ht ρ M
    intro c hcm
    simp only [psumStartGoal, List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl
    · exact hpre
    · simp [evalC, evalE, hne]
  rw [hval]
  refine isSum_zero (fun key => ?_)
  rw [gAtP_congr_env hg (fun p hp => param_init h (hps p hp) ρ M) M key]
  rw [gAtP, atStartE_eval h.s ρ M key d.g (fun mp hmp => ?_)]
  · exact hzero
  · obtain ⟨p, hp, hpe⟩ := List.mem_map.mp (hm mp hmp)
    cases hl : lookup (fun p => p.1 == mp) h.s.f.m.maps0 with
    | none => exact absurd (lookup_none_all hl p hp) (by simp [hpe])
    | some p0 =>
      obtain ⟨hp0, hp0e⟩ := lookup_some hl
      simp only [beq_iff_eq] at hp0e
      simp only [startVal, hl, Option.map_some, Option.getD_some]
      rw [← hp0e]; exact hM p0 hp0 key

theorem param_sum_step {ps : List SEntry} {inits : List (List VDef × Tree)}
    {covers : List (List (List VDef × Tree))}
    (hL : checkSMachine h.plain ps = true) (hc : checkParamSums h ps inits covers = true)
    {ρ : Nat → Nat} {M : Nat → Nat → Nat}
    (hsum : ∀ d ∈ h.sums, IsSum (gAtP d.g ρ M) (ρ d.v))
    (hlaws : ∀ e ∈ ps, e.Holds ρ M) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (ha : evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.s.f.m.assume = true) :
    ∀ d ∈ h.sums, IsSum (gAtP d.g (sNext h.plain ρ M ι κ).1 (sNext h.plain ρ M ι κ).2)
      ((sNext h.plain ρ M ι κ).1 d.v) := by
  obtain ⟨hok, _, hcov⟩ := checkParamSums_parts hc
  obtain ⟨hdist, hall⟩ := paramSumOk_parts hok
  intro d hd
  obtain ⟨hg, hps, _, hcar, hwr, hev, hcs, hax, hv, _⟩ := paramSumOk1_parts (hall d hd)
  let X := decideQ h.plain (withInputs h.s.f.m.inputs ρ ι) (withCarried h.s M κ)
  let N := withCarried h.s M κ
  let V := decideFlags h.s.f.flags X N
  have hV : (sView h.plain ρ M ι κ).1 = V := rfl
  let M' := everyMaps h.s V N
  have hM' : (sNext h.plain ρ M ι κ).2 = M' := rfl
  let cs' := d.cs.map (evalE V N)
  have hpk : ∀ p ∈ d.ps, p ≠ d.k := fun p hp => (paramImmutable_parts (hps p hp)).2.1
  have hVp : ∀ p ∈ d.ps, V p = ρ p := fun p hp => param_view h (hps p hp) ρ M ι κ
  have hXp : ∀ p ∈ d.ps, X p = ρ p := fun p hp => by
    obtain ⟨hmem, _, _⟩ := paramImmutable_parts (hps p hp)
    simp only [List.mem_append, not_or] at hmem
    show decideQ h.plain (withInputs h.s.f.m.inputs ρ ι) N p = ρ p
    rw [decideQ_other hmem.1.1.1.1.2, withInputs_other hmem.1.1.1.1.1.1]
  have hag : ∀ key, key ∉ cs' → gAtP d.g ρ M' key = gAtP d.g ρ M key := by
    intro key hkey
    apply gAtP_congr_maps; intro mp hmp
    have hNM : N mp key = M mp key := by
      have hnc : mp ∉ h.s.carried := avoidsMapsE_occ hcar hmp
      simp [N, withCarried, hnc]
    simp only [M', everyMaps]
    cases hl : lookup (fun w => w.1 == mp) h.s.every with
    | some w =>
      obtain ⟨hwm, hw1⟩ := lookup_some hl
      simp only [beq_iff_eq] at hw1
      have hwc : w ∈ pcoverWs h.s d := List.mem_filter.mpr ⟨hwm, by rw [hw1]; exact hmp⟩
      obtain ⟨t, ht⟩ := hcov d hd w hwc
      obtain ⟨hfl, hbf, hxv, _⟩ := hev w hwc
      show evalE (upd V w.2.1 key) N w.2.2 = M mp key
      apply Decidable.byContradiction; intro hne
      apply sound ⟨t.1, psumCoverGoal h.s ps d w⟩ t.2 ht (upd X d.x key) N
      intro c hcm
      simp only [psumCoverGoal, List.mem_append, List.mem_singleton, List.mem_map] at hcm
      rcases hcm with ((rfl | hcl) | ⟨c0, hc0, rfl⟩) | rfl
      · rw [congrC _ X N _ (fun i hi => by
            have hne' : i ≠ d.x := fun he => avoids_occ hax hi (by simp [he])
            simp [upd, hne']), inline_evalC]
        exact ha
      · refine pcellLaw_holds hcl (carried := h.s.carried)
            (fun e he => (slaws_avoid hL e.law (List.mem_map_of_mem he)).2) hlaws _ N
            (fun p hp => by
              have hpx : p ≠ d.x := (paramImmutable_parts (hps p hp)).2.2
              simp [upd, hpx, hXp p hp])
            (fun mp hmp => by
              simp [upd_at, N, withCarried, hmp])
      · have hc0' := (hcs c0 hc0).2
        simp only [evalC, evalE, upd_at, Bool.not_eq_true', decide_eq_false_iff_not]
        rw [congrE _ X N _ (fun i hi => by
            have hne' : i ≠ d.x := fun he => avoidsE_occ hc0' hi (by simp [he])
            simp [upd, hne']), inline_evalE]
        intro he; exact hkey (List.mem_map.mpr ⟨c0, hc0, he.symm⟩)
      · simp only [evalC, evalE, Bool.not_eq_true', decide_eq_false_iff_not, upd_at]
        rw [subst_evalE, applyS_single]
        simp only [evalE, upd_at]
        rw [congrE _ (upd X w.2.1 key) N _ (fun i hi => by
            simp only [upd]; by_cases hib : i = w.2.1
            · simp [hib]
            · have hne' : i ≠ d.x := fun he => avoidsE_occ hxv hi (by simp [he])
              simp [hib, hne']),
          inline_evalE, decide_upd hbf (fun p hp => hfl p hp)]
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
        simp only [hne, ite_false]; exact hNM
      | none => exact hNM
  have hold : evalE V N (dTermE (pgHere d) d.cs) = dsum (gAtP d.g ρ M) cs' := by
    rw [dTermE_eval V N d.cs (pgHere d) (gAtP d.g ρ N) (fun t => pgHere_eval hg hpk hVp N t),
      gAtP_carried h hcar]
  have hnew : evalE V N (dTermE (pgAfter h.s d) d.cs) = dsum (gAtP d.g ρ M') cs' :=
    dTermE_eval V N d.cs (pgAfter h.s d) (gAtP d.g ρ M') (fun t => pgAfter_eval h hg hpk hVp N t)
  have hval : (sNext h.plain ρ M ι κ).1 d.v =
      ρ d.v + dsum (gAtP d.g ρ M') cs' - dsum (gAtP d.g ρ M) cs' := by
    show applyS (h.s.f.m.step ++ h.sums.map (fun d => (d.v, psumNext h.s d))) V N d.v = _
    simp only [applyS]
    rw [assoc_after (fun hm => hv (by simp [hm])), passoc_sums (psumNext h.s) hdist hd]
    simp only [psumNext, evalE, hold, hnew]
    rw [← hV, pview_v h hv ρ M ι κ]
  have hfn : gAtP d.g (sNext h.plain ρ M ι κ).1 M' = gAtP d.g ρ M' :=
    funext fun key => gAtP_congr_env hg (fun p hp => param_next h (hps p hp) ρ M ι κ) M' key
  rw [hval, hM', hfn]
  exact isSum_change cs' (hsum d hd) hag

theorem pq_mem {d : ParamSumDecl} (hd : d ∈ h.sums) :
    (d.q, [d.k], psumBody h.s d) ∈ h.plain.qflags :=
  List.mem_append_right _ (List.mem_map.mpr ⟨d, hd, rfl⟩)

theorem param_sum_facts {ps : List SEntry} {inits : List (List VDef × Tree)}
    {covers : List (List (List VDef × Tree))}
    (hc : checkParamSums h ps inits covers = true) (hs : sOk h.plain = true)
    {ρ : Nat → Nat} {M : Nat → Nat → Nat}
    (hsum : ∀ d ∈ h.sums, IsSum (gAtP d.g ρ M) (ρ d.v)) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 (psumsC h.sums) = true := by
  obtain ⟨hok, _, _⟩ := checkParamSums_parts hc
  obtain ⟨_, hall⟩ := paramSumOk_parts hok
  obtain ⟨_, hqd, _, _, hdx, _, _⟩ := sOk_parts h.plain hs
  let N := withCarried h.s M κ
  let Wi := withInputs h.s.f.m.inputs ρ ι
  have one : ∀ d ∈ h.sums,
      evalC (sView h.plain ρ M ι κ).1 N (.and (psumFact d) (.eq (.var d.q) (.const 1))) = true := by
    intro d hd
    obtain ⟨hg, hps, _, hcar, _, _, _, _, hv, hvk⟩ := paramSumOk1_parts (hall d hd)
    have hvi : d.v ∉ h.s.f.m.inputs := fun hm => hv (by simp [hm])
    have hpk : ∀ p ∈ d.ps, p ≠ d.k := fun p hp => (paramImmutable_parts (hps p hp)).2.1
    have hVp : ∀ p ∈ d.ps, (sView h.plain ρ M ι κ).1 p = ρ p :=
      fun p hp => param_view h (hps p hp) ρ M ι κ
    simp only [evalC, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · show decide (evalE _ N (dTermE (pgHere d) d.cs) ≤ (sView h.plain ρ M ι κ).1 d.v) = true
      apply decide_eq_true
      rw [dTermE_eval _ N d.cs (pgHere d) (gAtP d.g ρ N) (fun t => pgHere_eval hg hpk hVp N t),
        gAtP_carried h hcar, pview_v h hv ρ M ι κ]
      exact dsum_le (hsum d hd) _
    · have hqv : d.q ∈ h.plain.qVars := List.mem_map_of_mem (pq_mem h hd)
      have hqf : d.q ∉ flagVars h.s.f.flags := fun hm =>
        (distinct_append hdx).2.2 d.q
          (by simp only [SMachine.extVars, List.mem_append]; exact Or.inl (Or.inr hqv)) hm
      show decideFlags h.s.f.flags (decideQ h.plain Wi N) N d.q = 1
      rw [decide_other hqf, decideQ_of, lookup_unique hqd (pq_mem h hd)]
      simp only
      have hallk : ∀ key, holdsC (atKeys Wi [d.k] key) N (psumBody h.s d) := by
        intro key
        rw [← evalC_iff]
        show decide (evalE _ N (dTermE (pgHere d) (.var d.k :: d.cs.map (inlineE h.s.f.flags)))
            ≤ atKeys Wi [d.k] key d.v) = true
        apply decide_eq_true
        have hkp : ∀ p ∈ d.ps, atKeys Wi [d.k] key p = ρ p := fun p hp => by
          obtain ⟨hmem, hne, _⟩ := paramImmutable_parts (hps p hp)
          have hpi : p ∉ h.s.f.m.inputs := fun hm => hmem (by simp [hm])
          rw [atKeys_out (by simpa using hne)]
          exact withInputs_other hpi ρ ι
        rw [dTermE_eval _ N _ (pgHere d) (gAtP d.g ρ N) (fun t => pgHere_eval hg hpk hkp N t),
          gAtP_carried h hcar, atKeys_out (show d.v ∉ [d.k] by simpa using hvk)]
        show _ ≤ withInputs h.s.f.m.inputs ρ ι d.v
        rw [withInputs_other hvi]
        exact dsum_le (hsum d hd) _
      simp [hallk]
  have all : ∀ ds : List ParamSumDecl, (∀ d ∈ ds, d ∈ h.sums) →
      evalC (sView h.plain ρ M ι κ).1 N (psumsC ds) = true := by
    intro ds
    induction ds with
    | nil => intro _; rfl
    | cons d ds ih =>
      intro hm
      have h1 := one d (hm d List.mem_cons_self)
      have h2 := ih (fun d' hd' => hm d' (List.mem_cons_of_mem _ hd'))
      show (evalC _ N (.and (psumFact d) (.eq (.var d.q) (.const 1))) && evalC _ N (psumsC ds)) = true
      rw [h1, h2]; rfl
  exact all h.sums (fun _ hd => hd)

theorem param_sum_assume {ps : List SEntry} {inits : List (List VDef × Tree)}
    {covers : List (List (List VDef × Tree))}
    (hc : checkParamSums h ps inits covers = true) (hs : sOk h.plain = true)
    {ρ : Nat → Nat} {M : Nat → Nat → Nat}
    (hsum : ∀ d ∈ h.sums, IsSum (gAtP d.g ρ M) (ρ d.v)) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.plain.f.m.assume
      = evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.s.f.m.assume := by
  show (evalC _ _ h.s.f.m.assume && evalC _ _ (psumsC h.sums)) = _
  rw [param_sum_facts h hc hs hsum ι κ, Bool.and_true]

/-- **Parameterized sum soundness**: in every reachable state of `h.plain`, every parameterized
sum variable holds the exact sum of its integrand at the current parameter valuation `ρ`, and
every law in `ps` holds. -/
theorem param_sum_cells {ps : List SEntry} {inits : List (List VDef × Tree)}
    {covers : List (List (List VDef × Tree))}
    (hl : checkSMachine h.plain ps = true) (hc : checkParamSums h ps inits covers = true) :
    ∀ ρ M, SReach h.plain ρ M →
      (∀ d ∈ h.sums, IsSum (gAtP d.g ρ M) (ρ d.v)) ∧ ∀ e ∈ ps, e.Holds ρ M := by
  intro ρ M hr
  induction hr with
  | start ρ M hM h0 hfa hpf =>
    exact ⟨param_sum_start h hc ρ M hM h0,
      smachine_sound h.plain ps hl _ _ (SReach.start ρ M hM h0 hfa hpf)⟩
  | step ρ M ι κ hr' ha ih =>
    have ha0 : evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.s.f.m.assume = true := by
      have : evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2
          (.and h.s.f.m.assume (psumsC h.sums)) = true := ha
      simp only [evalC, Bool.and_eq_true] at this; exact this.1
    exact ⟨param_sum_step h hl hc ih.1 ih.2 ι κ ha0,
      smachine_sound h.plain ps hl _ _ (SReach.step ρ M ι κ hr' ha)⟩

theorem param_sum_holds {ps : List SEntry} {inits : List (List VDef × Tree)}
    {covers : List (List (List VDef × Tree))}
    (hl : checkSMachine h.plain ps = true) (hc : checkParamSums h ps inits covers = true) :
    ∀ ρ M, SReach h.plain ρ M → ∀ d ∈ h.sums, IsSum (gAtP d.g ρ M) (ρ d.v) :=
  fun ρ M hr => (param_sum_cells h hl hc ρ M hr).1

theorem param_sum_allowed {ps : List SEntry} {inits : List (List VDef × Tree)}
    {covers : List (List (List VDef × Tree))}
    (hl : checkSMachine h.plain ps = true) (hc : checkParamSums h ps inits covers = true) :
    ∀ ρ M, SReach h.plain ρ M → ∀ ι κ,
      evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.plain.f.m.assume
      = evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.s.f.m.assume :=
  fun ρ M hr ι κ => param_sum_assume h hc (sOk_of hl) (param_sum_holds h hl hc ρ M hr) ι κ

end param_exact

/-! ### Projection to the source machine when the rule reads none of its sums -/

def ParamSumMachine.ghosts (h : ParamSumMachine) : SGhosted :=
  ⟨h.s, h.sums.flatMap (fun d => [(d.v, .const 0, .var d.v), (d.q, .const 0, .var d.q)])⟩

theorem pghosts_vars (h : ParamSumMachine) {d : ParamSumDecl} (hd : d ∈ h.sums) :
    d.v ∈ h.ghosts.vars ∧ d.q ∈ h.ghosts.vars := by
  simp only [SGhosted.vars, ParamSumMachine.ghosts, List.mem_map, List.mem_flatMap,
    List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨⟨_, ⟨d, hd, Or.inl rfl⟩, rfl⟩, ⟨_, ⟨d, hd, Or.inr rfl⟩, rfl⟩⟩

section param_project
variable (h : ParamSumMachine) (hg : sghostOk h.ghosts = true)
include hg

theorem param_sum_ghost_step {ρ ρg : Nat → Nat} (hag : Agree h.ghosts.vars ρg ρ)
    (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    evalC (sView h.plain ρg M ι κ).1 (sView h.plain ρg M ι κ).2 h.s.f.m.assume
      = evalC (sView h.s ρ M ι κ).1 (sView h.s ρ M ι κ).2 h.s.f.m.assume
      ∧ Agree h.ghosts.vars (sNext h.plain ρg M ι κ).1 (sNext h.s ρ M ι κ).1
      ∧ (sNext h.plain ρg M ι κ).2 = (sNext h.s ρ M ι κ).2 := by
  obtain ⟨_, _, _, ha, hf, hs, _, hw, he, hq, _⟩ := sghostOk_parts h.ghosts hg
  have hX : Agree h.ghosts.vars (withInputs h.s.f.m.inputs ρg ι) (withInputs h.s.f.m.inputs ρ ι) :=
    fun i hi => by
      simp only [withInputs]; split
      · rfl
      · exact hag i hi
  have hQ : Agree h.ghosts.vars
      (decideQ h.plain (withInputs h.s.f.m.inputs ρg ι) (withCarried h.s M κ))
      (decideQ h.s (withInputs h.s.f.m.inputs ρ ι) (withCarried h.s M κ)) := by
    intro v hv
    rw [decideQ_of, decideQ_of]
    show (match lookup (fun q => q.1 == v)
        (h.s.qflags ++ h.sums.map (fun d => (d.q, [d.k], psumBody h.s d))) with
      | some q => if ∀ k, holdsC (atKeys (withInputs h.s.f.m.inputs ρg ι) q.2.1 k)
            (withCarried h.s M κ) q.2.2 then 1 else 0
      | none => withInputs h.s.f.m.inputs ρg ι v) = _
    rw [lookup_append]
    cases hl : lookup (fun q => q.1 == v) h.s.qflags with
    | some q =>
      simp only
      exact ite_all_congr (fun i hi _ => hX i (avoids_occ (hq q (lookup_some hl).1) hi)) (fun _ _ => rfl)
    | none =>
      have hl2 : lookup (fun q => q.1 == v)
          (h.sums.map (fun d => (d.q, [d.k], psumBody h.s d))) = none :=
        lookup_none (fun x hx => by
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
          simp only [beq_eq_false_iff_ne]
          intro he'; exact hv (by rw [← he']; exact (pghosts_vars h hd).2))
      simp only [hl2]; exact hX v hv
  have hD : Agree h.ghosts.vars
      (decideFlags h.s.f.flags (decideQ h.plain (withInputs h.s.f.m.inputs ρg ι) (withCarried h.s M κ)) (withCarried h.s M κ))
      (decideFlags h.s.f.flags (decideQ h.s (withInputs h.s.f.m.inputs ρ ι) (withCarried h.s M κ)) (withCarried h.s M κ)) :=
    decide_agree_on hf (withCarried h.s M κ) hQ
  refine ⟨?_, fun i hi => ?_, ?_⟩
  · show evalC (decideFlags h.s.f.flags (decideQ h.plain (withInputs h.s.f.m.inputs ρg ι) (withCarried h.s M κ)) (withCarried h.s M κ)) _ h.s.f.m.assume = _
    exact congrC _ _ _ _ (fun i hi => hD i (avoids_occ ha hi))
  · have hvi : i ∉ h.sums.map (fun d => d.v) := fun hm => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm; exact hi (pghosts_vars h hd).1
    show applyS (h.s.f.m.step ++ h.sums.map (fun d => (d.v, psumNext h.s d))) (decideFlags h.s.f.flags (decideQ h.plain (withInputs h.s.f.m.inputs ρg ι) (withCarried h.s M κ)) (withCarried h.s M κ)) (withCarried h.s M κ) i = _
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
    | some w =>
      exact congrE _ _ _ w.2.2 (fun j hj => upd_agree hD w.2.1 key j (avoidsE_occ (he w (lookup_some hl).1) hj))
    | none =>
      simp only [writeMaps]
      cases hl2 : lookup (fun w => w.1 == mp) h.s.f.m.writes with
      | none => rfl
      | some w =>
        obtain ⟨h1, h2⟩ := hw w (lookup_some hl2).1
        simp only [congrE _ _ _ w.2.1 (fun j hj => hD j (avoidsE_occ h1 hj)),
          congrE _ _ _ w.2.2 (fun j hj => hD j (avoidsE_occ h2 hj))]

theorem param_sum_project {ps : List SEntry} {inits : List (List VDef × Tree)}
    {covers : List (List (List VDef × Tree))}
    (hl : checkSMachine h.plain ps = true) (hc : checkParamSums h ps inits covers = true) :
    ∀ {ρ M}, SReach h.s ρ M → ∃ ρg, SReach h.plain ρg M ∧ Agree h.ghosts.vars ρg ρ := by
  intro ρ M hr
  induction hr with
  | start ρ M hM h0 hfa hpf =>
    refine ⟨applyS h.plain.f.m.init ρ M, SReach.start ρ M hM h0 hfa hpf, fun i hi => ?_⟩
    have hvi : i ∉ h.sums.map (fun d => d.v) := fun hm => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm; exact hi (pghosts_vars h hd).1
    show applyS (h.s.f.m.init ++ h.sums.map (fun d => (d.v, E.const 0))) ρ M i
      = applyS h.s.f.m.init ρ M i
    exact applyS_append_other (by simpa using hvi) ρ M
  | step ρ M ι κ _ ha ih =>
    obtain ⟨ρg, hrg, hag⟩ := ih
    obtain ⟨hA, hS, hW⟩ := param_sum_ghost_step h hg hag M ι κ
    refine ⟨_, ?_, hS⟩
    rw [← hW]
    refine SReach.step ρg M ι κ hrg ?_
    rw [param_sum_allowed h hl hc ρg M hrg ι κ, hA]; exact ha

theorem param_sum_project_laws (ps : List SEntry) {inits : List (List VDef × Tree)}
    {covers : List (List (List VDef × Tree))}
    (hl : checkSMachine h.plain ps = true) (hc : checkParamSums h ps inits covers = true) :
    ∀ ρ M, SReach h.s ρ M → ∀ e ∈ ps, avoids h.ghosts.vars e.law.holds = true → e.Holds ρ M := by
  intro ρ M hr e he hav
  obtain ⟨ρg, hrg, hag⟩ := param_sum_project h hg hl hc hr
  exact sentry_transfer (V := h.ghosts.vars) (MS := []) hav (by simp [avoidsMaps])
    (fun i hi => (hag i hi).symm) (fun _ _ => rfl)
    (smachine_sound h.plain ps hl ρg M hrg e he)

end param_project

/-! ## Piece 2: Observer-key elimination (full `SMachine`) -/

/-- `obs` is an unconstrained fresh observer parameter of `s`: never read or written by `s`,
its preconditions, flags, quantified flags, `every` writes, facts, or multi-key facts. -/
def observerOk (s : SMachine) (obs : Nat) : Bool :=
  !(s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains obs
    && !occC obs s.f.m.pre
    && s.f.m.init.all (fun p => !occE obs p.2)
    && skFresh s obs

private theorem mlaw_holds_upd_fresh {l : MLaw} {obs : Nat} (ho : occC obs l.holds = false)
    {ρ : Nat → Nat} {M : Nat → Nat → Nat} (g : Nat) (h : l.Holds ρ M) :
    l.Holds (upd ρ obs g) M := by
  cases hk : l.key with
  | none =>
    simp only [MLaw.Holds, hk] at h ⊢
    rw [congrC _ ρ M _ (fun i hi => by
      have hne : i ≠ obs := fun he => by rw [he, ho] at hi; cases hi
      simp [upd, hne])]
    exact h
  | some kv =>
    simp only [MLaw.Holds, hk] at h ⊢
    intro v
    rw [congrC _ (upd ρ kv v) M _ (fun i hi => by
      have hne : i ≠ obs := fun he => by rw [he, ho] at hi; cases hi
      simp only [upd]
      by_cases hik : i = kv <;> simp [hik, hne])]
    exact h v

private theorem holdsOver_upd_fresh {l : MLaw} {obs : Nat} (ho : occC obs l.holds = false)
    (M : Nat → Nat → Nat) : ∀ (ks : List Nat) (ρ : Nat → Nat) (g : Nat),
    holdsOver l M ks ρ → holdsOver l M ks (upd ρ obs g)
  | [], ρ, g, h => mlaw_holds_upd_fresh ho g h
  | k :: ks, ρ, g, h => by
    intro w
    have h1 := holdsOver_upd_fresh ho M ks (upd ρ k w) g (h w)
    have heq : upd (upd ρ obs g) k w = upd (upd ρ k w) obs g ∨ k = obs := by
      by_cases hko : k = obs
      · exact Or.inr hko
      · refine Or.inl (funext fun i => ?_)
        simp only [upd]
        by_cases hik : i = k
        · subst hik; simp [hko]
        · simp [hik]
    rcases heq with he | rfl
    · rw [he]; exact h1
    · have : upd (upd ρ k g) k w = upd ρ k w := by
        funext i; simp only [upd]; by_cases hi : i = k <;> simp [hi]
      rw [this]; exact h w

/-- Any reachable state of `s` remains reachable under any rebinding of a fresh observer `obs`.
Works for arbitrary `SMachine` (including `qflags`, `carried`, `every`, `facts`, `pfacts`). -/
theorem sreach_rebind (s : SMachine) (obs : Nat) (hok : observerOk s obs = true) :
    ∀ {ρ M}, SReach s ρ M → ∀ g, SReach s (upd ρ obs g) M := by
  simp only [observerOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨hmem, hpre⟩, hinit⟩, hsk⟩ := hok
  have hnot : obs ∉ s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1) :=
    fun hm => by rw [List.contains_iff_mem.mpr hm] at hmem; cases hmem
  obtain ⟨hfl, hqf, hass, hst, hwr, hev, hfa⟩ := skFresh_parts hsk
  have hpfa := skFresh_pfacts hsk
  have hni : obs ∉ s.f.m.inputs := fun hm => hnot (by simp [SMachine.extVars, hm])
  have hnq : obs ∉ s.qVars := fun hm => hnot (by simp [SMachine.extVars, hm])
  have hnf : obs ∉ flagVars s.f.flags := fun hm => hnot (by simp [hm])
  have hninit : obs ∉ s.f.m.init.map (·.1) := fun hm => hnot (by simp [hm])
  have hnstep : obs ∉ s.f.m.step.map (·.1) := fun hm => hnot (by simp [hm])
  intro ρ M hr
  induction hr with
  | start ρ M hM h0 hfacts hpfacts =>
    intro g
    rw [← applyS_upd hninit hinit ρ M g]
    apply SReach.start (upd ρ obs g) M hM
    · rw [congrC _ ρ M _ (fun i hi => by
        have hne : i ≠ obs := fun he => by rw [he, hpre] at hi; cases hi
        simp [upd, hne])]
      exact h0
    · intro l hl
      exact mlaw_holds_upd_fresh (hfa l hl) g (hfacts l hl)
    · intro p hp
      exact holdsOver_upd_fresh (hpfa p hp) M p.2 ρ g (hpfacts p hp)
  | step ρ M ι κ _ ha ih =>
    intro g
    have hv := sView_upd hni hnq hnf hqf hfl ρ M ι κ g
    have hn := sNext_upd hni hnq hnf hqf hfl hnstep hst hwr hev ρ M ι κ g
    have ha' : evalC (sView s (upd ρ obs g) M ι κ).1 (sView s (upd ρ obs g) M ι κ).2 s.f.m.assume = true := by
      rw [hv]
      rw [congrC _ (sView s ρ M ι κ).1 _ _ (fun i hi => by
        have hne : i ≠ obs := fun he => by rw [he, hass] at hi; cases hi
        simp [upd, hne])]
      exact ha
    have hstep := SReach.step (upd ρ obs g) M ι κ (ih g) ha'
    simpa only [hn] using hstep

/-- Guard a law `l` by `grp = obs` (the exact form proved on the observer-extended machine). -/
def guardLaw (l : MLaw) (obs : Nat) (grp : E) : MLaw :=
  ⟨.or (.not (.eq grp (.var obs))) l.holds, l.key⟩

/-- **Observer-key elimination**: if `obs` is fresh for `s`, `grp`, and `l`, and `grp = obs ⇒ l`
holds in every reachable state of `s`, then the unguarded law `l` holds in every reachable state
of `s` (by instantiating `obs := evalE (upd ρ kv v) M grp` for each key `v`). -/
theorem observer_elim (s : SMachine) (obs : Nat) (grp : E) (l : MLaw)
    (hok : observerOk s obs = true)
    (hkey : l.key ≠ some obs)
    (hgrp : occE obs grp = false)
    (hlo : occC obs l.holds = false)
    (hguard : ∀ ρ M, SReach s ρ M → (guardLaw l obs grp).Holds ρ M) :
    ∀ ρ M, SReach s ρ M → l.Holds ρ M := by
  intro ρ M hr
  cases hk : l.key with
  | none =>
    let g := evalE ρ M grp
    have hr' := sreach_rebind s obs hok hr g
    have hg := hguard (upd ρ obs g) M hr'
    simp only [guardLaw, MLaw.Holds, hk, evalC, evalE, Bool.or_eq_true, Bool.not_eq_true'] at hg ⊢
    have hge : evalE (upd ρ obs g) M grp = g :=
      congrE _ ρ M grp (fun i hi => by
        have hne : i ≠ obs := fun he => by rw [he, hgrp] at hi; cases hi
        simp [upd, hne])
    have hob : upd ρ obs g obs = g := upd_at ρ obs g
    rcases hg with hne | hold
    · exact absurd (hge.trans hob.symm) (of_decide_eq_false hne)
    · rw [← congrC (upd ρ obs g) ρ M l.holds (fun i hi => by
        have hne : i ≠ obs := fun he => by rw [he, hlo] at hi; cases hi
        simp [upd, hne])]
      exact hold
  | some kv =>
    have hkv : kv ≠ obs := fun he => hkey (by rw [hk, he])
    simp only [MLaw.Holds, hk]
    intro v
    let g := evalE (upd ρ kv v) M grp
    have hr' := sreach_rebind s obs hok hr g
    have hg := hguard (upd ρ obs g) M hr'
    simp only [guardLaw, MLaw.Holds, hk] at hg
    have hgv := hg v
    simp only [evalC, evalE, Bool.or_eq_true, Bool.not_eq_true'] at hgv
    have hge : evalE (upd (upd ρ obs g) kv v) M grp = g :=
      congrE _ (upd ρ kv v) M grp (fun i hi => by
        have hne : i ≠ obs := fun he => by rw [he, hgrp] at hi; cases hi
        simp only [upd]
        by_cases hik : i = kv <;> simp [hik, hne])
    have hob : upd (upd ρ obs g) kv v obs = g := by
      simp [upd, Ne.symm hkv]
    rcases hgv with hne | hold
    · exact absurd (hge.trans hob.symm) (of_decide_eq_false hne)
    · rw [← congrC (upd (upd ρ obs g) kv v) (upd ρ kv v) M l.holds (fun i hi => by
        have hne : i ≠ obs := fun he => by rw [he, hlo] at hi; cases hi
        simp only [upd]
        by_cases hik : i = kv <;> simp [hik, hne])]
      exact hold

/-! ## Combined end-to-end soundness theorem -/

/-- **Grouped-sum soundness (end-to-end)**:
Given an original machine `h.s`, parameterized sums `h.sums` (which may read the fresh observer
parameter `obs`), and a checked family `ps` on `h.plain` containing `guardLaw l obs grp`
(avoiding sum ghosts), the exact unmodified target law `l` holds in every reachable state of
the unmodified source machine `h.s`. -/
theorem grouped_sum_sound (h : ParamSumMachine) (ps : List SEntry)
    (inits : List (List VDef × Tree)) (covers : List (List (List VDef × Tree)))
    (obs : Nat) (grp : E) (l : MLaw) (e : SEntry)
    (hl : checkSMachine h.plain ps = true)
    (hc : checkParamSums h ps inits covers = true)
    (hg : sghostOk h.ghosts = true)
    (hobs : observerOk h.s obs = true)
    (hkey : l.key ≠ some obs)
    (hgrp : occE obs grp = false)
    (hlo : occC obs l.holds = false)
    (he : e ∈ ps)
    (heq : e.law = guardLaw l obs grp)
    (hav : avoids h.ghosts.vars e.law.holds = true) :
    ∀ ρ M, SReach h.s ρ M → l.Holds ρ M := by
  apply observer_elim h.s obs grp l hobs hkey hgrp hlo
  intro ρ M hr
  have hproj := param_sum_project_laws h hg ps hl hc ρ M hr e he hav
  rw [← heq]
  exact e.holds_law hproj

end Kern.GroupedSums

#print axioms Kern.GroupedSums.param_sum_cells
#print axioms Kern.GroupedSums.param_sum_holds
#print axioms Kern.GroupedSums.param_sum_allowed
#print axioms Kern.GroupedSums.param_sum_project_laws
#print axioms Kern.GroupedSums.sreach_rebind
#print axioms Kern.GroupedSums.observer_elim
#print axioms Kern.GroupedSums.grouped_sum_sound

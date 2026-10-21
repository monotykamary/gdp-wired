import Sets
import Cyclic

/-!
Bridge: a cyclic proof of one of today's rules is a proof about the rule. Lean 4.34.0, core only, on top of
`Sets.lean` and `Cyclic.lean`.

`cyclic_sound` says what a cyclic proof's nodes say about any maps that meet its facts. core/cyclic.ts's instances say a
rule in those terms, and this file says them back: what an instance's facts and nodes are is a function of the rule's
own syntax here, a check (`cycMOk`) compares the exported proof against it, and a theorem carries the node to the rule's
own meaning.

Machines (`machineNodes`). A run of an `SMachine` (Sets.lean's `SReach`, with no flag that holds at every key) is put
as maps over time: each state variable and input x as a map x@ whose cell u is x's value at time u (an input, the
request taken at u), each map M (and each map a request carries) as a map M@ whose cell u + k·Ω is M's cell k at time u,
Ω above the run's length T, so that u < Ω and the pair decodes (u = (u + k·Ω) % Ω, k = (u + k·Ω) / Ω) at every key k.
The facts are the start and each step (flags inlined), each map's start and step (a write at one key read at the key
the fact names), the functions' facts, and conditions that hold of every natural (`natC`). `cyc_machine_sound`: if the
exported facts are among those, the node's hypotheses among the precondition, t ≤ T and T < Ω, and its conclusion the
law at time t, then the law holds in every reachable state, at every value of its keys.
-/

namespace Kern
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! Lists and terms -/

theorem not_mem_of_not_contains {l : List Nat} {a : Nat} (h : (!l.contains a) = true) : a ∉ l := fun hm => by
  rw [List.contains_iff_mem.mpr hm] at h; exact absurd h (by decide)

-- A condition true of every natural: 0 ≤ e, and conjunctions of those.
def natC : C → Bool
  | .le a _ => beqE a (.const 0)
  | .and a b => natC a && natC b
  | _ => false

theorem natC_true {ρ : Nat → Nat} {M : Nat → Nat → Nat} : ∀ c, natC c = true → evalC ρ M c = true
  | .le a b, h => by simp only [natC] at h; rw [beqE_eq h]; simp [evalC, evalE]
  | .and a b, h => by
    simp only [natC, Bool.and_eq_true] at h; simp only [evalC, natC_true a h.1, natC_true b h.2, Bool.and_self]
  | .lt _ _, h => by simp [natC] at h
  | .eq _ _, h => by simp [natC] at h
  | .or _ _, h => by simp [natC] at h
  | .not _, h => by simp [natC] at h

-- A list of conditions as their conjunction, as TypeScript's `and` and the exporter write it.
def andL : List C → C
  | [] => trueC
  | [a] => a
  | a :: b :: rest => .and a (andL (b :: rest))

theorem andL_true {ρ : Nat → Nat} {M : Nat → Nat → Nat} : ∀ l : List C, (∀ c ∈ l, evalC ρ M c = true) → evalC ρ M (andL l) = true
  | [], _ => by simp [andL, trueC, evalC, evalE]
  | [a], h => by simpa [andL] using h a (by simp)
  | a :: b :: rest, h => by
    simp only [andL, evalC, Bool.and_eq_true]
    exact ⟨h a (by simp), andL_true (b :: rest) (fun c hc => h c (List.mem_cons_of_mem _ hc))⟩

theorem evalE_ite_eq (ρ : Nat → Nat) (M : Nat → Nat → Nat) (a b t f : E) :
    evalE ρ M (.ite (.eq a b) t f) = if evalE ρ M a = evalE ρ M b then evalE ρ M t else evalE ρ M f := by
  show (if evalC ρ M (.eq a b) = true then evalE ρ M t else evalE ρ M f) = _
  by_cases h : evalE ρ M a = evalE ρ M b
  · rw [if_pos ((evalC_iff ρ M (.eq a b)).mpr h), if_pos h]
  · rw [if_neg (fun hc => h ((evalC_iff ρ M (.eq a b)).mp hc)), if_neg h]

theorem impl_true {ρ : Nat → Nat} {M : Nat → Nat → Nat} {a b : C} (h : evalC ρ M a = true → evalC ρ M b = true) :
    evalC ρ M (.or (.not a) b) = true := by
  cases ha : evalC ρ M a with
  | false => simp [evalC, ha]
  | true => simp [evalC, ha, h ha]

theorem congr2E {ρ ρ' : Nat → Nat} {M M' : Nat → Nat → Nat} (e : E) (hv : ∀ i, occE i e = true → ρ i = ρ' i)
    (hm : ∀ m, occME m e = true → M m = M' m) : evalE ρ M e = evalE ρ' M' e := by
  rw [congrE ρ ρ' M e hv, congrME ρ' M M' e hm]
theorem congr2C {ρ ρ' : Nat → Nat} {M M' : Nat → Nat → Nat} (c : C) (hv : ∀ i, occC i c = true → ρ i = ρ' i)
    (hm : ∀ m, occMC m c = true → M m = M' m) : evalC ρ M c = evalC ρ' M' c := by
  rw [congrC ρ ρ' M c hv, congrMC ρ' M M' c hm]

-- Every read at the term `fr` read at `to` instead (core/cyclic.ts's readsAt): the same wherever the two are equal.
mutual
def readsAtE (fr to : E) : E → E
  | .var i => .var i
  | .const n => .const n
  | .add a b => .add (readsAtE fr to a) (readsAtE fr to b)
  | .sub a b => .sub (readsAtE fr to a) (readsAtE fr to b)
  | .mul k a => .mul k (readsAtE fr to a)
  | .min a b => .min (readsAtE fr to a) (readsAtE fr to b)
  | .max a b => .max (readsAtE fr to a) (readsAtE fr to b)
  | .prod a b => .prod (readsAtE fr to a) (readsAtE fr to b)
  | .ite c t f => .ite (readsAtC fr to c) (readsAtE fr to t) (readsAtE fr to f)
  | .get m key => if beqE key fr then .get m to else .get m (readsAtE fr to key)
def readsAtC (fr to : E) : C → C
  | .le a b => .le (readsAtE fr to a) (readsAtE fr to b)
  | .lt a b => .lt (readsAtE fr to a) (readsAtE fr to b)
  | .eq a b => .eq (readsAtE fr to a) (readsAtE fr to b)
  | .and a b => .and (readsAtC fr to a) (readsAtC fr to b)
  | .or a b => .or (readsAtC fr to a) (readsAtC fr to b)
  | .not a => .not (readsAtC fr to a)
end

section
variable {ρ : Nat → Nat} {M : Nat → Nat → Nat} {fr to : E} (h : evalE ρ M to = evalE ρ M fr)
include h
mutual
theorem readsAt_evalE : (e : E) → evalE ρ M (readsAtE fr to e) = evalE ρ M e
  | .var _ => rfl
  | .const _ => rfl
  | .add a b => by simp only [readsAtE, evalE, readsAt_evalE a, readsAt_evalE b]
  | .sub a b => by simp only [readsAtE, evalE, readsAt_evalE a, readsAt_evalE b]
  | .mul k a => by simp only [readsAtE, evalE, readsAt_evalE a]
  | .min a b => by simp only [readsAtE, evalE, readsAt_evalE a, readsAt_evalE b]
  | .max a b => by simp only [readsAtE, evalE, readsAt_evalE a, readsAt_evalE b]
  | .prod a b => by simp only [readsAtE, evalE, readsAt_evalE a, readsAt_evalE b]
  | .ite c t f => by simp only [readsAtE, evalE, readsAt_evalC c, readsAt_evalE t, readsAt_evalE f]
  | .get m key => by
    simp only [readsAtE]
    split
    · rename_i hb; simp only [evalE, h, beqE_eq hb]
    · simp only [evalE, readsAt_evalE key]
theorem readsAt_evalC : (c : C) → evalC ρ M (readsAtC fr to c) = evalC ρ M c
  | .le a b => by simp only [readsAtC, evalC, readsAt_evalE a, readsAt_evalE b]
  | .lt a b => by simp only [readsAtC, evalC, readsAt_evalE a, readsAt_evalE b]
  | .eq a b => by simp only [readsAtC, evalC, readsAt_evalE a, readsAt_evalE b]
  | .and a b => by simp only [readsAtC, evalC, readsAt_evalC a, readsAt_evalC b]
  | .or a b => by simp only [readsAtC, evalC, readsAt_evalC a, readsAt_evalC b]
  | .not a => by simp only [readsAtC, evalC, readsAt_evalC a]
end
end

theorem applyS_getD (σ : List (Nat × E)) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (i : Nat) :
    applyS σ ρ M i = evalE ρ M ((assoc σ i).getD (.var i)) := by
  simp only [applyS]; cases assoc σ i <;> rfl

theorem assoc_some_mem {σ : List (Nat × E)} {i : Nat} {e : E} (h : assoc σ i = some e) : (i, e) ∈ σ := by
  simp only [assoc, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  obtain ⟨hm, hq⟩ := lookup_some hp
  have : p.1 = i := by simpa using hq
  rw [← this]; exact hm

theorem pair_mod {u T : Nat} (h : u ≤ T) (kv : Nat) : (u + kv * (T + 1)) % (T + 1) = u := by
  rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt (by omega)
theorem pair_div {u T : Nat} (h : u ≤ T) (kv : Nat) : (u + kv * (T + 1)) / (T + 1) = kv := by
  rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]

/-! The encoding (core/cyclic.ts's machineNodes) as a function of the machine -/

-- The variables a machine's facts and nodes add (a fact's time and key, the run's length, Ω, a node's time), and the
-- maps over time: each state variable and input's, each map's.
structure CycEnc where
  u : Nat
  k : Nat
  T : Nat
  om : Nat
  t : Nat
  vtr : List (Nat × Nat)
  mtr : List (Nat × Nat)

def CycEnc.special (ce : CycEnc) : List Nat := [ce.u, ce.k, ce.T, ce.om, ce.t]
def CycEnc.tm (ce : CycEnc) : List Nat := ce.vtr.map (·.2) ++ ce.mtr.map (·.2)

-- A term at time w: each state variable and input read from its map at w, each map's cell k from its map at w + k·Ω.
def cycσ (ce : CycEnc) (w : E) : List (Nat × E) := ce.vtr.map fun p => (p.1, .get p.2 w)
def cycRd (ce : CycEnc) (w : E) : Nat → E → E := fun m key =>
  match lookup (fun p => p.1 == m) ce.mtr with
  | some p => .get p.2 (.add w (.prod key (.var ce.om)))
  | none => .get m key
def trE (ce : CycEnc) (w : E) : E → E := substRE (cycσ ce w) (cycRd ce w)
def trC (ce : CycEnc) (w : E) : C → C := substRC (cycσ ce w) (cycRd ce w)

def cycStepped (ce : CycEnc) : C := .and (.le (.const 1) (.var ce.u)) (.le (.var ce.u) (.var ce.T))
def cycPrev (ce : CycEnc) : E := .sub (.var ce.u) (.const 1)
def cycCell (ce : CycEnc) (m : Nat) (w : E) : E := cycRd ce w m (.var ce.k)
def cycStepTerm (s : SMachine) (x : Nat) : E := (assoc s.f.m.step x).getD (.var x)

def cycStart (s : SMachine) (ce : CycEnc) : Fact :=
  ⟨[ce.u], .or (.not (.le (.var ce.u) (.const 0))) (andL (trueC :: s.f.m.init.map fun p => .eq (trE ce (.var ce.u) (.var p.1)) p.2))⟩
def cycStep (s : SMachine) (ce : CycEnc) (withAssume : Bool) : Fact :=
  ⟨[ce.u], .or (.not (cycStepped ce)) (andL (trueC :: ((if withAssume then [trC ce (cycPrev ce) (inlineC s.f.flags s.f.m.assume)] else [])
    ++ s.f.m.init.map fun p => .eq (trE ce (.var ce.u) (.var p.1)) (trE ce (cycPrev ce) (inlineE s.f.flags (cycStepTerm s p.1))))))⟩
-- A map's cell k after a step: a write at every key, its value at k; a write at one key, where k is the key, its value
-- read at k; else the cell before.
def cycNext (s : SMachine) (ce : CycEnc) (m : Nat) : E :=
  match lookup (fun w => w.1 == m) s.every with
  | some w => trE ce (cycPrev ce) (inlineE s.f.flags (substE [(w.2.1, .var ce.k)] w.2.2))
  | none => match lookup (fun w => w.1 == m) s.f.m.writes with
    | some w => .ite (.eq (.var ce.k) (trE ce (cycPrev ce) (inlineE s.f.flags w.2.1)))
        (trE ce (cycPrev ce) (readsAtE (inlineE s.f.flags w.2.1) (.var ce.k) (inlineE s.f.flags w.2.2))) (cycCell ce m (cycPrev ce))
    | none => cycCell ce m (cycPrev ce)
def cycMapFacts (s : SMachine) (ce : CycEnc) : List Fact := s.f.m.maps0.flatMap fun p =>
  [⟨[ce.u, ce.k], .or (.not (.le (.var ce.u) (.const 0))) (.eq (cycCell ce p.1 (.var ce.u)) (.const p.2))⟩,
   ⟨[ce.u, ce.k], .or (.not (cycStepped ce)) (.eq (cycCell ce p.1 (.var ce.u)) (cycNext s ce p.1))⟩]
-- The functions' facts, each with its further keys.
def cycGiven (s : SMachine) : List (MLaw × List Nat) := s.facts.map (fun l => (l, [])) ++ s.pfacts
def cycFnFacts (s : SMachine) : List Fact := (cycGiven s).map fun p => ⟨p.1.key.toList ++ p.2, p.1.holds⟩
-- The step with the assumption and without it (core/cyclic.ts leaves it out when the machine has none).
def cycCanon (s : SMachine) (ce : CycEnc) : List Fact :=
  cycStart s ce :: cycStep s ce true :: cycStep s ce false :: (cycMapFacts s ce ++ cycFnFacts s)

/-! The check -/

def cycZ (ce : CycEnc) (keys : List Nat) : List Nat := ce.special ++ keys
def cycP (s : SMachine) (ce : CycEnc) (keys : List Nat) : List Nat := cycZ ce keys ++ ce.vtr.map (·.1) ++ flagVars s.f.flags

-- The encoding fits the machine: every variable a step changes has its map over time, every map a step or a request
-- changes has its own, those maps are fresh, and the added variables are apart from the machine's.
def cycShapeOk (s : SMachine) (ce : CycEnc) (keys : List Nat) : Bool :=
  s.qflags.isEmpty && flagsOk s.f.flags && distinct ce.special && distinct ce.tm
    && (cycZ ce keys).all (fun z => !(ce.vtr.map (·.1)).contains z && !(flagVars s.f.flags).contains z)
    && keys.all (fun z => !ce.special.contains z)
    && ce.tm.all (fun m => !(ce.mtr.map (·.1)).contains m)
    && s.f.m.init.all (fun p => (ce.vtr.map (·.1)).contains p.1 && !s.f.m.inputs.contains p.1)
    && s.f.m.step.all (fun p => (ce.vtr.map (·.1)).contains p.1)
    && s.f.m.inputs.all (fun x => (ce.vtr.map (·.1)).contains x)
    && distinct (s.f.m.init.map (·.1))
    && s.f.m.maps0.all (fun p => (ce.mtr.map (·.1)).contains p.1 && !s.carried.contains p.1)
    && s.carried.all (fun m => (ce.mtr.map (·.1)).contains m)
    && s.f.m.writes.all (fun w => (ce.mtr.map (·.1)).contains w.1)
    && s.every.all (fun w => (ce.mtr.map (·.1)).contains w.1)

-- The machine's terms read none of the added variables nor the maps over time; what is read at the start (the start
-- terms, the precondition, the functions' facts) reads no variable a step changes either.
def cycTermsOk (s : SMachine) (ce : CycEnc) (keys : List Nat) : Bool :=
  s.f.flags.all (fun p => avoids (cycZ ce keys) p.2 && avoidsMaps ce.tm p.2)
    && s.f.m.step.all (fun p => avoidsE (cycZ ce keys) p.2 && avoidsMapsE ce.tm p.2)
    && s.f.m.writes.all (fun w => avoidsE (cycZ ce keys) w.2.1 && avoidsMapsE ce.tm w.2.1 && avoidsE (cycZ ce keys) w.2.2 && avoidsMapsE ce.tm w.2.2)
    && s.every.all (fun w => (cycZ ce keys).all (fun z => z == w.2.1 || !occE z w.2.2) && avoidsMapsE ce.tm w.2.2)
    && avoids (cycZ ce keys) s.f.m.assume && avoidsMaps ce.tm s.f.m.assume
    && s.f.m.init.all (fun p => avoidsE (cycP s ce keys) p.2 && avoidsMapsE ce.tm p.2)
    && avoids (cycP s ce keys) s.f.m.pre && avoidsMaps ce.tm s.f.m.pre
    && (cycGiven s).all (fun g => (cycP s ce keys).all (fun z => g.1.key == some z || g.2.contains z || !occC z g.1.holds)
      && avoidsMaps ce.tm g.1.holds)

-- The law reads no added variable, no input, no map over time and no map a request carries.
def cycLawOk (s : SMachine) (ce : CycEnc) (law : C) : Bool :=
  avoids (ce.special ++ s.f.m.inputs) law && avoidsMaps (ce.tm ++ s.carried) law

def factBeq (f g : Fact) : Bool := f.keys == g.keys && beqC f.holds g.holds

-- Each exported fact is one of the encoding's, or true of every natural.
def cycFactsIn (s : SMachine) (ce : CycEnc) (facts : List Fact) : Bool :=
  facts.all fun f => natC f.holds || (cycCanon s ce).any (factBeq f)

-- The node: its conclusion the law at time t, its hypotheses among the precondition, t ≤ T and T < Ω.
def cycNodeOk (s : SMachine) (ce : CycEnc) (law : C) (n : CNode) : Bool :=
  beqC n.concl (trC ce (.var ce.t) law)
    && n.hyps.all (fun h => beqC h s.f.m.pre || beqC h (.le (.var ce.t) (.var ce.T)) || beqC h (.lt (.var ce.T) (.var ce.om)))

def cycMOk (s : SMachine) (ce : CycEnc) (facts : List Fact) (law : C) (keys : List Nat) (n : CNode) : Bool :=
  cycShapeOk s ce keys && cycTermsOk s ce keys && cycLawOk s ce law && cycFactsIn s ce facts && cycNodeOk s ce law n

/-! The checks, as propositions -/

theorem and_parts {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem mem_toList {o : Option Nat} {j : Nat} (h : j ∈ o.toList) : o = some j := by
  cases o <;> simp_all [Option.toList]

theorem isEmpty_nil {α : Type} {l : List α} (h : l.isEmpty = true) : l = [] := by
  cases l
  · rfl
  · simp [List.isEmpty] at h

structure CycShape (s : SMachine) (ce : CycEnc) (keys : List Nat) : Prop where
  q : s.qflags = []
  fl : flagsOk s.f.flags = true
  dsp : distinct ce.special = true
  dtm : distinct ce.tm = true
  zv : ∀ z ∈ cycZ ce keys, z ∉ ce.vtr.map (·.1)
  zf : ∀ z ∈ cycZ ce keys, z ∉ flagVars s.f.flags
  ks : ∀ z ∈ keys, z ∉ ce.special
  tmd : ∀ m ∈ ce.tm, m ∉ ce.mtr.map (·.1)
  initv : ∀ p ∈ s.f.m.init, p.1 ∈ ce.vtr.map (·.1)
  initin : ∀ p ∈ s.f.m.init, p.1 ∉ s.f.m.inputs
  stepv : ∀ p ∈ s.f.m.step, p.1 ∈ ce.vtr.map (·.1)
  inv : ∀ x ∈ s.f.m.inputs, x ∈ ce.vtr.map (·.1)
  dinit : distinct (s.f.m.init.map (·.1)) = true
  m0 : ∀ p ∈ s.f.m.maps0, p.1 ∈ ce.mtr.map (·.1)
  m0c : ∀ p ∈ s.f.m.maps0, p.1 ∉ s.carried
  carm : ∀ m ∈ s.carried, m ∈ ce.mtr.map (·.1)
  wrm : ∀ w ∈ s.f.m.writes, w.1 ∈ ce.mtr.map (·.1)
  evm : ∀ w ∈ s.every, w.1 ∈ ce.mtr.map (·.1)

theorem cycShape_of {s : SMachine} {ce : CycEnc} {keys : List Nat} (h : cycShapeOk s ce keys = true) : CycShape s ce keys := by
  simp only [cycShapeOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hq, hfl⟩, hdsp⟩, hdtm⟩, hz⟩, hks⟩, htm⟩, hinit⟩, hstep⟩, hin⟩, hdi⟩, hm0⟩, hcar⟩, hwr⟩, hev⟩ := h
  have hz' := List.all_eq_true.mp hz
  have hinit' := List.all_eq_true.mp hinit
  have hm0' := List.all_eq_true.mp hm0
  refine ⟨isEmpty_nil hq, hfl, hdsp, hdtm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hdi, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hzm; exact not_mem_of_not_contains (and_parts (hz' z hzm)).1
  · intro z hzm; exact not_mem_of_not_contains (and_parts (hz' z hzm)).2
  · intro z hzm; exact not_mem_of_not_contains (List.all_eq_true.mp hks z hzm)
  · intro m hm; exact not_mem_of_not_contains (List.all_eq_true.mp htm m hm)
  · intro p hp; exact List.contains_iff_mem.mp (and_parts (hinit' p hp)).1
  · intro p hp; exact not_mem_of_not_contains (and_parts (hinit' p hp)).2
  · intro p hp; exact List.contains_iff_mem.mp (List.all_eq_true.mp hstep p hp)
  · intro x hx; exact List.contains_iff_mem.mp (List.all_eq_true.mp hin x hx)
  · intro p hp; exact List.contains_iff_mem.mp (and_parts (hm0' p hp)).1
  · intro p hp; exact not_mem_of_not_contains (and_parts (hm0' p hp)).2
  · intro m hm; exact List.contains_iff_mem.mp (List.all_eq_true.mp hcar m hm)
  · intro w hw; exact List.contains_iff_mem.mp (List.all_eq_true.mp hwr w hw)
  · intro w hw; exact List.contains_iff_mem.mp (List.all_eq_true.mp hev w hw)

structure CycTerms (s : SMachine) (ce : CycEnc) (keys : List Nat) : Prop where
  flz : ∀ p ∈ s.f.flags, avoids (cycZ ce keys) p.2 = true
  flm : ∀ p ∈ s.f.flags, avoidsMaps ce.tm p.2 = true
  stz : ∀ p ∈ s.f.m.step, avoidsE (cycZ ce keys) p.2 = true
  stm : ∀ p ∈ s.f.m.step, avoidsMapsE ce.tm p.2 = true
  wkz : ∀ w ∈ s.f.m.writes, avoidsE (cycZ ce keys) w.2.1 = true
  wkm : ∀ w ∈ s.f.m.writes, avoidsMapsE ce.tm w.2.1 = true
  wvz : ∀ w ∈ s.f.m.writes, avoidsE (cycZ ce keys) w.2.2 = true
  wvm : ∀ w ∈ s.f.m.writes, avoidsMapsE ce.tm w.2.2 = true
  evz : ∀ w ∈ s.every, ∀ z ∈ cycZ ce keys, z ≠ w.2.1 → occE z w.2.2 = false
  evm : ∀ w ∈ s.every, avoidsMapsE ce.tm w.2.2 = true
  asz : avoids (cycZ ce keys) s.f.m.assume = true
  asm : avoidsMaps ce.tm s.f.m.assume = true
  inz : ∀ p ∈ s.f.m.init, avoidsE (cycP s ce keys) p.2 = true
  inm : ∀ p ∈ s.f.m.init, avoidsMapsE ce.tm p.2 = true
  prz : avoids (cycP s ce keys) s.f.m.pre = true
  prm : avoidsMaps ce.tm s.f.m.pre = true
  gz : ∀ g ∈ cycGiven s, ∀ z ∈ cycP s ce keys, g.1.key ≠ some z → z ∉ g.2 → occC z g.1.holds = false
  gm : ∀ g ∈ cycGiven s, avoidsMaps ce.tm g.1.holds = true

theorem cycTerms_of {s : SMachine} {ce : CycEnc} {keys : List Nat} (h : cycTermsOk s ce keys = true) : CycTerms s ce keys := by
  simp only [cycTermsOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hfl, hst⟩, hw⟩, hev⟩, has⟩, ham⟩, hin⟩, hpz⟩, hpm⟩, hg⟩ := h
  have hfl' := List.all_eq_true.mp hfl
  have hst' := List.all_eq_true.mp hst
  have hw' := List.all_eq_true.mp hw
  have hev' := List.all_eq_true.mp hev
  have hin' := List.all_eq_true.mp hin
  have hg' := List.all_eq_true.mp hg
  refine ⟨fun p hp => (and_parts (hfl' p hp)).1, fun p hp => (and_parts (hfl' p hp)).2,
    fun p hp => (and_parts (hst' p hp)).1, fun p hp => (and_parts (hst' p hp)).2,
    fun w hw => (and_parts (and_parts (and_parts (hw' w hw)).1).1).1, fun w hw => (and_parts (and_parts (and_parts (hw' w hw)).1).1).2,
    fun w hw => (and_parts (and_parts (hw' w hw)).1).2, fun w hw => (and_parts (hw' w hw)).2,
    fun w hw z hz hne => ?_, fun w hw => (and_parts (hev' w hw)).2,
    has, ham, fun p hp => (and_parts (hin' p hp)).1, fun p hp => (and_parts (hin' p hp)).2, hpz, hpm,
    fun g hg z hz hk hgs => ?_, fun g hg => (and_parts (hg' g hg)).2⟩
  · have := List.all_eq_true.mp (and_parts (hev' w hw)).1 z hz
    cases hb : (z == w.2.1)
    · rw [hb] at this; simpa using this
    · exact absurd (beq_iff_eq.mp hb) hne
  · have := List.all_eq_true.mp (and_parts (hg' g hg)).1 z hz
    have h1 : (g.1.key == some z) = false := by
      cases hb : (g.1.key == some z)
      · rfl
      · exact absurd (beq_iff_eq.mp hb) hk
    have h2 : g.2.contains z = false := by
      cases hb : g.2.contains z
      · rfl
      · exact absurd (List.contains_iff_mem.mp hb) hgs
    rw [h1, h2] at this; simpa using this

/-! A run, step by step -/

structure CRun where
  ρ0 : Nat → Nat                  -- before the start
  st : Nat → Nat → Nat            -- the state at each time
  mp : Nat → Nat → Nat → Nat      -- the maps at each time
  ι : Nat → Nat → Nat             -- the request taken at each time
  κ : Nat → Nat → Nat → Nat       -- the maps it carries

def CRun.N (s : SMachine) (r : CRun) (u : Nat) : Nat → Nat → Nat := withCarried s (r.mp u) (r.κ u)
def CRun.X (s : SMachine) (r : CRun) (u : Nat) : Nat → Nat := withInputs s.f.m.inputs (r.st u) (r.ι u)
def CRun.V (s : SMachine) (r : CRun) (u : Nat) : Nat → Nat := decideFlags s.f.flags (r.X s u) (r.N s u)

-- A run of T steps from a start SReach allows.
structure CRun.Ok (s : SMachine) (r : CRun) (T : Nat) : Prop where
  maps0 : StartMaps s.f.m (r.mp 0)
  pre : evalC r.ρ0 (r.mp 0) s.f.m.pre = true
  facts : ∀ l ∈ s.facts, l.Holds r.ρ0 (r.mp 0)
  pfacts : s.PFacts r.ρ0 (r.mp 0)
  init : r.st 0 = applyS s.f.m.init r.ρ0 (r.mp 0)
  step : ∀ u, u < T → evalC (r.V s u) (r.N s u) s.f.m.assume = true ∧ r.st (u + 1) = applyS s.f.m.step (r.V s u) (r.N s u)
    ∧ r.mp (u + 1) = everyMaps s (r.V s u) (r.N s u)

-- The run with one more step.
def CRun.snoc (r : CRun) (T : Nat) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) : CRun :=
  ⟨r.ρ0, fun u => if u ≤ T then r.st u else ρ, fun u => if u ≤ T then r.mp u else M,
    fun u => if u < T then r.ι u else ι, fun u => if u < T then r.κ u else κ⟩

theorem decideQ_nil {s : SMachine} (hq : s.qflags = []) (X : Nat → Nat) (N : Nat → Nat → Nat) : decideQ s X N = X := by
  funext v; simp only [decideQ, hq, lookup]

theorem snoc_early {s : SMachine} {r : CRun} {T u : Nat} (hu : u < T) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat)
    (κ : Nat → Nat → Nat) : (r.snoc T ρ M ι κ).N s u = r.N s u ∧ (r.snoc T ρ M ι κ).V s u = r.V s u
      ∧ (r.snoc T ρ M ι κ).st (u + 1) = r.st (u + 1) ∧ (r.snoc T ρ M ι κ).mp (u + 1) = r.mp (u + 1) := by
  have h1 : u ≤ T := Nat.le_of_lt hu
  have h2 : u + 1 ≤ T := hu
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [CRun.V, CRun.X, CRun.N, CRun.snoc, if_pos h1, if_pos hu, if_pos h2]

theorem snoc_zero {r : CRun} {T : Nat} (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    (r.snoc T ρ M ι κ).ρ0 = r.ρ0 ∧ (r.snoc T ρ M ι κ).st 0 = r.st 0 ∧ (r.snoc T ρ M ι κ).mp 0 = r.mp 0 := by
  refine ⟨rfl, ?_, ?_⟩ <;> simp only [CRun.snoc, if_pos (Nat.zero_le T)]

theorem snoc_last {r : CRun} {T : Nat} (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    (r.snoc T ρ M ι κ).st (T + 1) = ρ ∧ (r.snoc T ρ M ι κ).mp (T + 1) = M ∧ (r.snoc T ρ M ι κ).st T = r.st T
      ∧ (r.snoc T ρ M ι κ).mp T = r.mp T ∧ (r.snoc T ρ M ι κ).ι T = ι ∧ (r.snoc T ρ M ι κ).κ T = κ := by
  have h1 : ¬ T + 1 ≤ T := by omega
  have h2 : ¬ T < T := Nat.lt_irrefl T
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [CRun.snoc, if_neg h1, if_neg h2, if_pos (Nat.le_refl T)]

-- A reachable state is the end of a run (no flag holds at every key).
theorem reach_run {s : SMachine} (hq : s.qflags = []) :
    ∀ {ρ M}, SReach s ρ M → ∃ (r : CRun) (T : Nat), r.Ok s T ∧ r.st T = ρ ∧ r.mp T = M := by
  intro ρ M h
  induction h with
  | start ρ M hM hp hf hpf =>
    exact ⟨⟨ρ, fun _ => applyS s.f.m.init ρ M, fun _ => M, fun _ => ρ, fun _ => M⟩, 0,
      ⟨hM, hp, hf, hpf, rfl, fun u hu => absurd hu (Nat.not_lt_zero u)⟩, rfl, rfl⟩
  | step ρ M ι κ _ ha ih =>
    obtain ⟨r, T, hr, hst, hmp⟩ := ih
    have hv : sView s ρ M ι κ = (decideFlags s.f.flags (withInputs s.f.m.inputs ρ ι) (withCarried s M κ), withCarried s M κ) := by
      simp only [sView, decideQ_nil hq]
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := snoc_last (r := r) (T := T) (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2 ι κ
    obtain ⟨z1, z2, z3⟩ := snoc_zero (r := r) (T := T) (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2 ι κ
    have hN : (r.snoc T (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2 ι κ).N s T = (sView s ρ M ι κ).2 := by
      rw [hv, CRun.N, l4, l6, hmp]
    have hV : (r.snoc T (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2 ι κ).V s T = (sView s ρ M ι κ).1 := by
      rw [CRun.V, hN, CRun.X, l3, l5, hst, hv]
    refine ⟨r.snoc T (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2 ι κ, T + 1, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, l1, l2⟩
    · rw [z3]; exact hr.maps0
    · rw [z1, z3]; exact hr.pre
    · rw [z1, z3]; exact hr.facts
    · rw [z1, z3]; exact hr.pfacts
    · rw [z1, z2, z3]; exact hr.init
    · intro u hu
      rcases Nat.lt_or_ge u T with hlt | hge
      · obtain ⟨e1, e2, e3, e4⟩ := snoc_early (s := s) (r := r) hlt (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2 ι κ
        rw [e1, e2, e3, e4]; exact hr.step u hlt
      · have hu' : u = T := by omega
        rw [hu', hV, hN, l1, l2]
        exact ⟨ha, rfl, rfl⟩

section run
variable {s : SMachine} {r : CRun} {T : Nat} (hr : r.Ok s T)
include hr

-- What no step changes keeps its value from before the start.
theorem run_frame : ∀ u, u ≤ T → ∀ i, i ∉ s.f.m.init.map (·.1) → i ∉ s.f.m.step.map (·.1) → i ∉ s.f.m.inputs →
    i ∉ flagVars s.f.flags → r.st u i = r.ρ0 i := by
  intro u
  induction u with
  | zero => intro _ i hi _ _ _; rw [hr.init]; exact applyS_other hi _ _
  | succ u ih =>
    intro hu i hi hs hin hf
    rw [(hr.step u (by omega)).2.1, applyS_other hs, CRun.V, decide_other hf, CRun.X, withInputs_other hin]
    exact ih (by omega) i hi hs hin hf

-- A map no step writes and no request carries keeps its cells.
theorem run_maps {D : List Nat} (hc : ∀ m ∈ s.carried, m ∈ D) (hw : ∀ w ∈ s.f.m.writes, w.1 ∈ D) (he : ∀ w ∈ s.every, w.1 ∈ D) :
    ∀ u, u ≤ T → ∀ m, m ∉ D → r.mp u m = r.mp 0 m := by
  intro u
  induction u with
  | zero => intros; rfl
  | succ u ih =>
    intro hu m hm
    rw [(hr.step u (by omega)).2.2]
    funext key
    have hne : lookup (fun w => w.1 == m) s.every = none :=
      lookup_none (fun w hw' => by simp only [beq_eq_false_iff_ne]; intro h; exact hm (h ▸ he w hw'))
    have hnw : lookup (fun w => w.1 == m) s.f.m.writes = none :=
      lookup_none (fun w hw' => by simp only [beq_eq_false_iff_ne]; intro h; exact hm (h ▸ hw w hw'))
    have hnc : ¬ s.carried.contains m = true := fun h => hm (hc m (List.contains_iff_mem.mp h))
    simp only [everyMaps, hne, writeMaps, hnw, CRun.N, withCarried]
    rw [if_neg hnc]
    exact congrFun (ih (by omega) m hm) key
end run

theorem N_not_carried {s : SMachine} {r : CRun} {u m : Nat} (hm : m ∉ s.carried) : r.N s u m = r.mp u m := by
  simp only [CRun.N, withCarried]
  rw [if_neg (fun h => hm (List.contains_iff_mem.mp h))]

/-! The run as maps over time -/

def cycMaps (s : SMachine) (ce : CycEnc) (r : CRun) (om : Nat) : Nat → Nat → Nat := fun i =>
  match lookup (fun p => p.2 == i) ce.vtr with
  | some p => fun u => r.X s u p.1
  | none => match lookup (fun p => p.2 == i) ce.mtr with
    | some p => fun y => r.N s (y % om) p.1 (y / om)
    | none => r.mp 0 i

-- The maps a step at time u reads, as the encoding gives them: the maps over time as they are, the rest as the run's.
def cycView (s : SMachine) (ce : CycEnc) (r : CRun) (om u : Nat) : Nat → Nat → Nat := fun m =>
  if ce.tm.contains m then cycMaps s ce r om m else r.N s u m

-- The node's environment: t and T the run's length, Ω one above it.
def cycEnv (ce : CycEnc) (T : Nat) (ρ' : Nat → Nat) : Nat → Nat := fun i =>
  if i = ce.t then T else if i = ce.T then T else if i = ce.om then T + 1 else ρ' i

-- An environment a fact is read at: T and Ω as the node's, and from before the start wherever no step reaches.
def EnvOk (s : SMachine) (ce : CycEnc) (keys : List Nat) (r : CRun) (T : Nat) (Q : Nat → Nat) : Prop :=
  Q ce.T = T ∧ Q ce.om = T + 1 ∧ ∀ i, i ∉ cycP s ce keys → Q i = r.ρ0 i

section enc
variable {s : SMachine} {ce : CycEnc} {keys : List Nat} {r : CRun} {T : Nat}

theorem tm_parts (hd : distinct ce.tm = true) :
    distinct (ce.vtr.map (·.2)) = true ∧ distinct (ce.mtr.map (·.2)) = true ∧ ∀ a ∈ ce.vtr.map (·.2), a ∉ ce.mtr.map (·.2) :=
  distinct_append hd

theorem cm_v (hd : distinct ce.tm = true) {om : Nat} {p : Nat × Nat} (hp : p ∈ ce.vtr) :
    cycMaps s ce r om p.2 = fun u => r.X s u p.1 := by
  simp only [cycMaps, lookup_ren (tm_parts hd).1 p hp]

theorem cm_m (hd : distinct ce.tm = true) {om : Nat} {p : Nat × Nat} (hp : p ∈ ce.mtr) :
    cycMaps s ce r om p.2 = fun y => r.N s (y % om) p.1 (y / om) := by
  obtain ⟨_, h2, h3⟩ := tm_parts hd
  have hn : lookup (fun q => q.2 == p.2) ce.vtr = none := lookup_none (fun q hq => by
    simp only [beq_eq_false_iff_ne]; intro he
    exact h3 q.2 (List.mem_map.mpr ⟨q, hq, rfl⟩) (List.mem_map.mpr ⟨p, hp, he.symm⟩))
  simp only [cycMaps, hn, lookup_ren h2 p hp]

theorem cm_o {om i : Nat} (hi : i ∉ ce.tm) : cycMaps s ce r om i = r.mp 0 i := by
  have h1 : lookup (fun q => q.2 == i) ce.vtr = none := lookup_none (fun q hq => by
    simp only [beq_eq_false_iff_ne]; intro he
    exact hi (List.mem_append_left _ (List.mem_map.mpr ⟨q, hq, he⟩)))
  have h2 : lookup (fun q => q.2 == i) ce.mtr = none := lookup_none (fun q hq => by
    simp only [beq_eq_false_iff_ne]; intro he
    exact hi (List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, he⟩)))
  simp only [cycMaps, h1, h2]

theorem cv_N {om u m : Nat} (hm : m ∉ ce.tm) : cycView s ce r om u m = r.N s u m := by
  simp only [cycView]
  rw [if_neg (fun h => hm (List.contains_iff_mem.mp h))]

theorem notP {i : Nat} (h : i ∉ cycP s ce keys) :
    i ∉ ce.special ∧ i ∉ keys ∧ i ∉ ce.vtr.map (·.1) ∧ i ∉ flagVars s.f.flags := by
  simp only [cycP, cycZ, List.mem_append, not_or] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem special_parts (h : distinct ce.special = true) :
    ce.u ≠ ce.T ∧ ce.u ≠ ce.om ∧ ce.k ≠ ce.T ∧ ce.k ≠ ce.om ∧ ce.T ≠ ce.om ∧ ce.t ≠ ce.T ∧ ce.t ≠ ce.om := by
  have h0 : distinct [ce.u, ce.k, ce.T, ce.om, ce.t] = true := h
  obtain ⟨n1, d1⟩ := distinct_cons h0
  obtain ⟨n2, d2⟩ := distinct_cons d1
  obtain ⟨n3, d3⟩ := distinct_cons d2
  obtain ⟨n4, _⟩ := distinct_cons d3
  refine ⟨fun e => n1 (by rw [e]; simp), fun e => n1 (by rw [e]; simp), fun e => n2 (by rw [e]; simp),
    fun e => n2 (by rw [e]; simp), fun e => n3 (by rw [e]; simp), fun e => n3 (by rw [← e]; simp), fun e => n4 (by rw [← e]; simp)⟩

theorem in_special {i : Nat} (h : i = ce.u ∨ i = ce.k ∨ i = ce.T ∨ i = ce.om ∨ i = ce.t) : i ∈ ce.special := by
  simp only [CycEnc.special, List.mem_cons, List.not_mem_nil, or_false]; exact h

-- Flags decided at two frames that agree off Z (and off the flags), over maps that agree off TM.
theorem decide_view {fl : List (Nat × C)} (hfl : flagsOk fl = true) {Z TM : List Nat} (hz : ∀ p ∈ fl, avoids Z p.2 = true)
    (hm : ∀ p ∈ fl, avoidsMaps TM p.2 = true) {Y X : Nat → Nat} {V N : Nat → Nat → Nat}
    (hY : ∀ j, j ∉ Z → j ∉ flagVars fl → Y j = X j) (hV : ∀ m, m ∉ TM → V m = N m) {i : Nat} (hi : i ∉ Z) :
    decideFlags fl Y V i = decideFlags fl X N i := by
  simp only [decideFlags, applyS, assoc_flagSub]
  cases hc : flagOf fl i with
  | none => exact hY i hi (flagOf_none hc)
  | some c =>
    obtain ⟨p, hp, rfl⟩ := flagOf_some hc
    simp only [Option.map_some, evalE]
    rw [congr2C (ρ' := X) (M' := N) p.2 (fun j hj => hY j (avoids_occ (hz p hp) hj) (avoids_occ (List.all_eq_true.mp hfl p hp) hj))
      (fun m hm' => hV m (avoidsMaps_occ (hm p hp) hm'))]

variable (hS : CycShape s ce keys) (hT : CycTerms s ce keys) (hr : r.Ok s T)
include hS hT hr

theorem enc_maps {u : Nat} (hu : u ≤ T) {m : Nat} (hm : m ∉ ce.mtr.map (·.1)) : r.N s u m = r.mp 0 m := by
  rw [N_not_carried (fun h => hm (hS.carm m h))]
  exact run_maps hr hS.carm hS.wrm hS.evm u hu m hm

theorem enc_frame {u : Nat} (hu : u ≤ T) {i : Nat} (hv : i ∉ ce.vtr.map (·.1)) (hf : i ∉ flagVars s.f.flags) :
    r.X s u i = r.ρ0 i := by
  have hin : i ∉ s.f.m.inputs := fun h => hv (hS.inv i h)
  rw [CRun.X, withInputs_other hin]
  exact run_frame hr u hu i (fun h => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact hv (hS.initv p hp))
    (fun h => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact hv (hS.stepv p hp)) hin hf

variable {Q : Nat → Nat} (hQ : EnvOk s ce keys r T Q) {w : E} {u : Nat}
  (hw : evalE Q (cycMaps s ce r (T + 1)) w = u) (hu : u ≤ T)
include hQ hw hu

-- A read of a map at time w: the maps over time read back the run's.
theorem enc_rd : ∀ m key, evalE Q (cycMaps s ce r (T + 1)) (cycRd ce w m key)
    = cycView s ce r (T + 1) u m (evalE Q (cycMaps s ce r (T + 1)) key) := by
  intro m key
  simp only [cycRd]
  split
  · rename_i p hp
    obtain ⟨hpm, hpe⟩ := lookup_some hp
    have hpm' : p.1 = m := by simpa using hpe
    have hmd : m ∈ ce.mtr.map (·.1) := List.mem_map.mpr ⟨p, hpm, hpm'⟩
    have hmt : m ∉ ce.tm := fun h => hS.tmd m h hmd
    rw [cv_N hmt]
    simp only [evalE, cm_m hS.dtm hpm, hw, hQ.2.1, pair_mod hu, pair_div hu, hpm']
  · rename_i hn
    have hmd : m ∉ ce.mtr.map (·.1) := fun h => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
      have := lookup_none_all hn p hp; simp at this
    simp only [evalE, cycView]
    by_cases ht : ce.tm.contains m = true
    · rw [if_pos ht]
    · rw [if_neg ht, cm_o (fun h => ht (List.contains_iff_mem.mpr h)), enc_maps hS hT hr hu hmd]

theorem enc_trE (e : E) : evalE Q (cycMaps s ce r (T + 1)) (trE ce w e)
    = evalE (applyS (cycσ ce w) Q (cycMaps s ce r (T + 1))) (cycView s ce r (T + 1) u) e :=
  substR_evalE (cycσ ce w) (cycRd ce w) Q (cycMaps s ce r (T + 1)) (cycView s ce r (T + 1) u) (enc_rd hS hT hr hQ hw hu) e
theorem enc_trC (c : C) : evalC Q (cycMaps s ce r (T + 1)) (trC ce w c)
    = evalC (applyS (cycσ ce w) Q (cycMaps s ce r (T + 1))) (cycView s ce r (T + 1) u) c :=
  substR_evalC (cycσ ce w) (cycRd ce w) Q (cycMaps s ce r (T + 1)) (cycView s ce r (T + 1) u) (enc_rd hS hT hr hQ hw hu) c

theorem enc_σ_in {i : Nat} (hi : i ∈ ce.vtr.map (·.1)) : applyS (cycσ ce w) Q (cycMaps s ce r (T + 1)) i = r.X s u i := by
  cases h : lookup (fun p => p.1 == i) ce.vtr with
  | none =>
    exfalso; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
    have := lookup_none_all h p hp; simp at this
  | some q =>
    obtain ⟨hq, hqi⟩ := lookup_some h
    have hqi' : q.1 = i := by simpa using hqi
    have ha : assoc (cycσ ce w) i = some (.get q.2 w) := by
      simp only [assoc, cycσ, lookup_map_pred, h, Option.map_some]
    simp only [applyS, ha, evalE, cm_v hS.dtm hq, hw, hqi']

theorem enc_σ_out {i : Nat} (hi : i ∉ ce.vtr.map (·.1)) : applyS (cycσ ce w) Q (cycMaps s ce r (T + 1)) i = Q i := by
  apply applyS_other
  intro h; apply hi
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

-- The frame a traced term reads: the run's state and request at time u, off the added variables and the flags.
theorem enc_Y {i : Nat} (hz : i ∉ cycZ ce keys) (hf : i ∉ flagVars s.f.flags) :
    applyS (cycσ ce w) Q (cycMaps s ce r (T + 1)) i = r.X s u i := by
  by_cases hv : i ∈ ce.vtr.map (·.1)
  · exact enc_σ_in hS hT hr hQ hw hu hv
  · rw [enc_σ_out hS hT hr hQ hw hu hv, hQ.2.2 i (by
      simp only [cycP, List.mem_append, not_or]; exact ⟨⟨hz, hv⟩, hf⟩), enc_frame hS hT hr hu hv hf]

theorem enc_D {i : Nat} (hz : i ∉ cycZ ce keys) :
    decideFlags s.f.flags (applyS (cycσ ce w) Q (cycMaps s ce r (T + 1))) (cycView s ce r (T + 1) u) i = r.V s u i :=
  decide_view hS.fl hT.flz hT.flm (fun _ hj hf => enc_Y hS hT hr hQ hw hu hj hf) (fun m hm => cv_N hm) hz

-- A machine term, its flags inlined, read at the frame of time w: the term at the run's step from u.
theorem enc_inl (e : E) (hz : avoidsE (cycZ ce keys) e = true) (hm : avoidsMapsE ce.tm e = true) :
    evalE (applyS (cycσ ce w) Q (cycMaps s ce r (T + 1))) (cycView s ce r (T + 1) u) (inlineE s.f.flags e) = evalE (r.V s u) (r.N s u) e := by
  rw [inline_evalE]
  exact congr2E e (fun i hi => enc_D hS hT hr hQ hw hu (avoidsE_occ hz hi)) (fun m hm' => cv_N (avoidsMapsE_occ hm hm'))

theorem enc_now (e : E) (hz : avoidsE (cycZ ce keys) e = true) (hm : avoidsMapsE ce.tm e = true) :
    evalE Q (cycMaps s ce r (T + 1)) (trE ce w (inlineE s.f.flags e)) = evalE (r.V s u) (r.N s u) e := by
  rw [enc_trE hS hT hr hQ hw hu, enc_inl hS hT hr hQ hw hu e hz hm]

theorem enc_nowC (c : C) (hz : avoids (cycZ ce keys) c = true) (hm : avoidsMaps ce.tm c = true) :
    evalC Q (cycMaps s ce r (T + 1)) (trC ce w (inlineC s.f.flags c)) = evalC (r.V s u) (r.N s u) c := by
  rw [enc_trC hS hT hr hQ hw hu, inline_evalC]
  exact congr2C c (fun i hi => enc_D hS hT hr hQ hw hu (avoids_occ hz hi)) (fun m hm' => cv_N (avoidsMaps_occ hm hm'))
end enc

/-! The facts hold of the run -/

theorem holds_any (l : MLaw) (M : Nat → Nat → Nat) : ∀ (gs : List Nat) (ρ : Nat → Nat), holdsOver l M gs ρ →
    ∀ X : Nat → Nat, (∀ j, occC j l.holds = true → j ∉ gs → l.key ≠ some j → X j = ρ j) → evalC X M l.holds = true
  | [], ρ, h, X, hX => by
    simp only [holdsOver, MLaw.Holds] at h
    split at h
    · rename_i hk
      rw [congrC X ρ M l.holds (fun j hj => hX j hj (by simp) (by rw [hk]; simp))]; exact h
    · rename_i kv hk
      rw [congrC X (upd ρ kv (X kv)) M l.holds (fun j hj => by
        simp only [upd]
        split
        · rename_i e; rw [e]
        · rename_i e; exact hX j hj (by simp) (by rw [hk]; intro h'; exact e (Option.some.inj h').symm))]
      exact h (X kv)
  | g :: gs, ρ, h, X, hX => by
    simp only [holdsOver] at h
    exact holds_any l M gs (upd ρ g (X g)) (h (X g)) X (fun j hj hgs hk => by
      simp only [upd]
      split
      · rename_i e; rw [e]
      · rename_i e
        exact hX j hj (fun hm => by rcases List.mem_cons.mp hm with h' | h'; exact e h'; exact hgs h') hk)

theorem cycNext_every {s : SMachine} {ce : CycEnc} {m : Nat} {w : Nat × Nat × E} (h : lookup (fun w => w.1 == m) s.every = some w) :
    cycNext s ce m = trE ce (cycPrev ce) (inlineE s.f.flags (substE [(w.2.1, .var ce.k)] w.2.2)) := by
  simp only [cycNext, h]
theorem cycNext_write {s : SMachine} {ce : CycEnc} {m : Nat} {w : Nat × E × E} (he : lookup (fun w => w.1 == m) s.every = none)
    (h : lookup (fun w => w.1 == m) s.f.m.writes = some w) :
    cycNext s ce m = .ite (.eq (.var ce.k) (trE ce (cycPrev ce) (inlineE s.f.flags w.2.1)))
        (trE ce (cycPrev ce) (readsAtE (inlineE s.f.flags w.2.1) (.var ce.k) (inlineE s.f.flags w.2.2))) (cycCell ce m (cycPrev ce)) := by
  simp only [cycNext, he, h]
theorem cycNext_none {s : SMachine} {ce : CycEnc} {m : Nat} (he : lookup (fun w => w.1 == m) s.every = none)
    (h : lookup (fun w => w.1 == m) s.f.m.writes = none) : cycNext s ce m = cycCell ce m (cycPrev ce) := by
  simp only [cycNext, he, h]
theorem everyMaps_every {s : SMachine} {D : Nat → Nat} {N : Nat → Nat → Nat} {m key : Nat} {w : Nat × Nat × E}
    (h : lookup (fun w => w.1 == m) s.every = some w) : everyMaps s D N m key = evalE (upd D w.2.1 key) N w.2.2 := by
  simp only [everyMaps, h]
theorem everyMaps_write {s : SMachine} {D : Nat → Nat} {N : Nat → Nat → Nat} {m key : Nat} {w : Nat × E × E}
    (he : lookup (fun w => w.1 == m) s.every = none) (h : lookup (fun w => w.1 == m) s.f.m.writes = some w) :
    everyMaps s D N m key = if key = evalE D N w.2.1 then evalE D N w.2.2 else N m key := by
  simp only [everyMaps, he, writeMaps, h]
theorem everyMaps_none {s : SMachine} {D : Nat → Nat} {N : Nat → Nat → Nat} {m key : Nat}
    (he : lookup (fun w => w.1 == m) s.every = none) (h : lookup (fun w => w.1 == m) s.f.m.writes = none) :
    everyMaps s D N m key = N m key := by
  simp only [everyMaps, he, writeMaps, h]

section facts
variable {s : SMachine} {ce : CycEnc} {keys : List Nat} {r : CRun} {T : Nat}
  (hS : CycShape s ce keys) (hT : CycTerms s ce keys) (hr : r.Ok s T)
include hS hT hr

theorem stepTerm_avoids {x : Nat} (hx : x ∈ ce.vtr.map (·.1)) :
    avoidsE (cycZ ce keys) (cycStepTerm s x) = true ∧ avoidsMapsE ce.tm (cycStepTerm s x) = true := by
  simp only [cycStepTerm]
  cases h : assoc s.f.m.step x with
  | some e => exact ⟨hT.stz _ (assoc_some_mem h), hT.stm _ (assoc_some_mem h)⟩
  | none =>
    refine ⟨?_, ?_⟩
    · simp only [Option.getD, avoidsE, List.all_eq_true, occE, Bool.not_eq_true', beq_eq_false_iff_ne]
      intro z hz e; subst e; exact hS.zv _ hz hx
    · simp [Option.getD, avoidsMapsE, occME]

theorem given_holds {g : MLaw × List Nat} (hg : g ∈ cycGiven s) : holdsOver g.1 (r.mp 0) g.2 r.ρ0 := by
  simp only [cycGiven, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨l, hl, rfl⟩ | hg
  · exact hr.facts l hl
  · exact hr.pfacts g hg

theorem start_holds {Q : Nat → Nat} (hQ : EnvOk s ce keys r T Q) :
    evalC Q (cycMaps s ce r (T + 1)) (cycStart s ce).holds = true := by
  apply impl_true
  intro h0
  rw [evalC_iff] at h0; simp only [holdsC, evalE] at h0
  have hw : evalE Q (cycMaps s ce r (T + 1)) (.var ce.u) = 0 := by simp only [evalE]; omega
  apply andL_true
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · simp [trueC, evalC, evalE]
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  have ha : assoc s.f.m.init p.1 = some p.2 := by simp only [assoc, lookup_unique hS.dinit hp, Option.map_some]
  rw [evalC_iff]; simp only [holdsC]
  rw [enc_trE hS hT hr hQ hw (Nat.zero_le T)]
  show applyS (cycσ ce (.var ce.u)) Q (cycMaps s ce r (T + 1)) p.1 = _
  rw [enc_σ_in hS hT hr hQ hw (Nat.zero_le T) (hS.initv p hp), CRun.X, withInputs_other (hS.initin p hp), hr.init]
  simp only [applyS, ha]
  exact congr2E p.2 (fun j hj => (hQ.2.2 j (avoidsE_occ (hT.inz p hp) hj)).symm)
    (fun m hm => (cm_o (avoidsMapsE_occ (hT.inm p hp) hm)).symm)

theorem step_holds (b : Bool) {Q : Nat → Nat} (hQ : EnvOk s ce keys r T Q) :
    evalC Q (cycMaps s ce r (T + 1)) (cycStep s ce b).holds = true := by
  apply impl_true
  intro h1
  rw [evalC_iff] at h1; simp only [cycStepped, holdsC, evalE] at h1
  obtain ⟨h1a, h1b⟩ := h1
  have hQT := hQ.1
  obtain ⟨u', hu'⟩ : ∃ u', Q ce.u = u' + 1 := ⟨Q ce.u - 1, by omega⟩
  have hlt : u' < T := by omega
  have hw : evalE Q (cycMaps s ce r (T + 1)) (cycPrev ce) = u' := by simp only [cycPrev, evalE]; omega
  have hw0 : evalE Q (cycMaps s ce r (T + 1)) (.var ce.u) = u' + 1 := hu'
  apply andL_true
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · simp [trueC, evalC, evalE]
  rcases List.mem_append.mp hc with hc | hc
  · cases b
    · simp at hc
    · simp at hc
      subst hc
      rw [enc_nowC hS hT hr hQ hw (Nat.le_of_lt hlt) _ hT.asz hT.asm]
      exact (hr.step u' hlt).1
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    have hx := hS.initv p hp
    rw [evalC_iff]; simp only [holdsC]
    rw [enc_trE hS hT hr hQ hw0 hlt, enc_now hS hT hr hQ hw (Nat.le_of_lt hlt) _ (stepTerm_avoids hS hT hr hx).1 (stepTerm_avoids hS hT hr hx).2]
    show applyS (cycσ ce (.var ce.u)) Q (cycMaps s ce r (T + 1)) p.1 = _
    rw [enc_σ_in hS hT hr hQ hw0 hlt hx, CRun.X, withInputs_other (hS.initin p hp), (hr.step u' hlt).2.1, applyS_getD]
    rfl

theorem mapStart_holds {p : Nat × Nat} (hp : p ∈ s.f.m.maps0) {Q : Nat → Nat} (hQ : EnvOk s ce keys r T Q) :
    evalC Q (cycMaps s ce r (T + 1)) (.or (.not (.le (.var ce.u) (.const 0))) (.eq (cycCell ce p.1 (.var ce.u)) (.const p.2))) = true := by
  apply impl_true
  intro h0
  rw [evalC_iff] at h0; simp only [holdsC, evalE] at h0
  have hw : evalE Q (cycMaps s ce r (T + 1)) (.var ce.u) = 0 := by simp only [evalE]; omega
  rw [evalC_iff]; simp only [holdsC, cycCell]
  rw [enc_rd hS hT hr hQ hw (Nat.zero_le T), cv_N (fun h => hS.tmd _ h (hS.m0 p hp)), N_not_carried (hS.m0c p hp)]
  exact hr.maps0 p hp _

theorem mapStep_holds {p : Nat × Nat} (hp : p ∈ s.f.m.maps0) {Q : Nat → Nat} (hQ : EnvOk s ce keys r T Q) :
    evalC Q (cycMaps s ce r (T + 1)) (.or (.not (cycStepped ce)) (.eq (cycCell ce p.1 (.var ce.u)) (cycNext s ce p.1))) = true := by
  apply impl_true
  intro h1
  rw [evalC_iff] at h1; simp only [cycStepped, holdsC, evalE] at h1
  obtain ⟨h1a, h1b⟩ := h1
  have hQT := hQ.1
  obtain ⟨u', hu'⟩ : ∃ u', Q ce.u = u' + 1 := ⟨Q ce.u - 1, by omega⟩
  have hlt : u' < T := by omega
  have hw : evalE Q (cycMaps s ce r (T + 1)) (cycPrev ce) = u' := by simp only [cycPrev, evalE]; omega
  have hw0 : evalE Q (cycMaps s ce r (T + 1)) (.var ce.u) = u' + 1 := hu'
  have hk : evalE Q (cycMaps s ce r (T + 1)) (.var ce.k) = Q ce.k := rfl
  have hmt : p.1 ∉ ce.tm := fun h => hS.tmd _ h (hS.m0 p hp)
  have hsp := special_parts hS.dsp
  have hkZ : ce.k ∈ cycZ ce keys := List.mem_append_left _ (in_special (Or.inr (Or.inl rfl)))
  -- the frame of time u' at k: the fact's own key
  have hYk : applyS (cycσ ce (cycPrev ce)) Q (cycMaps s ce r (T + 1)) ce.k = Q ce.k :=
    enc_σ_out hS hT hr hQ hw (Nat.le_of_lt hlt) (hS.zv _ hkZ)
  rw [evalC_iff]; simp only [holdsC, cycCell]
  rw [enc_rd hS hT hr hQ hw0 hlt, cv_N hmt, N_not_carried (hS.m0c p hp), (hr.step u' hlt).2.2, hk]
  by_cases hev : ∃ w, lookup (fun w => w.1 == p.1) s.every = some w
  · obtain ⟨w, he⟩ := hev
    obtain ⟨hwm, _⟩ := lookup_some he
    rw [cycNext_every he, everyMaps_every he, enc_trE hS hT hr hQ hw (Nat.le_of_lt hlt), inline_evalE, subst_evalE, applyS_single]
    have hD : evalE (decideFlags s.f.flags (applyS (cycσ ce (cycPrev ce)) Q (cycMaps s ce r (T + 1))) (cycView s ce r (T + 1) u'))
        (cycView s ce r (T + 1) u') (.var ce.k) = Q ce.k := by
      show decideFlags s.f.flags (applyS (cycσ ce (cycPrev ce)) Q (cycMaps s ce r (T + 1))) (cycView s ce r (T + 1) u') ce.k = Q ce.k
      rw [decide_other (hS.zf _ hkZ), hYk]
    rw [hD]
    refine congr2E w.2.2 (fun j hj => ?_) (fun m hm => (cv_N (avoidsMapsE_occ (hT.evm w hwm) hm)).symm)
    simp only [upd]
    split
    · rfl
    · rename_i hne
      have hjz : j ∉ cycZ ce keys := fun hz => by
        have := hT.evz w hwm j hz hne; rw [this] at hj; exact absurd hj (by decide)
      exact (enc_D hS hT hr hQ hw (Nat.le_of_lt hlt) hjz).symm
  · have he : lookup (fun w => w.1 == p.1) s.every = none := by
      cases h : lookup (fun w => w.1 == p.1) s.every
      · rfl
      · exact absurd ⟨_, h⟩ hev
    by_cases hwr' : ∃ w, lookup (fun w => w.1 == p.1) s.f.m.writes = some w
    · obtain ⟨w, hwr⟩ := hwr'
      obtain ⟨hwm, _⟩ := lookup_some hwr
      rw [cycNext_write he hwr, everyMaps_write he hwr]
      rw [evalE_ite_eq, hk, enc_now hS hT hr hQ hw (Nat.le_of_lt hlt) _ (hT.wkz w hwm) (hT.wkm w hwm)]
      by_cases hkk : Q ce.k = evalE (r.V s u') (r.N s u') w.2.1
      · rw [if_pos hkk, if_pos hkk, enc_trE hS hT hr hQ hw (Nat.le_of_lt hlt), readsAt_evalE]
        · exact (enc_inl hS hT hr hQ hw (Nat.le_of_lt hlt) _ (hT.wvz w hwm) (hT.wvm w hwm)).symm
        · show applyS (cycσ ce (cycPrev ce)) Q (cycMaps s ce r (T + 1)) ce.k = _
          rw [hYk, enc_inl hS hT hr hQ hw (Nat.le_of_lt hlt) _ (hT.wkz w hwm) (hT.wkm w hwm)]
          exact hkk
      · rw [if_neg hkk, if_neg hkk, cycCell, enc_rd hS hT hr hQ hw (Nat.le_of_lt hlt), cv_N hmt, hk]
    · have hwr : lookup (fun w => w.1 == p.1) s.f.m.writes = none := by
        cases h : lookup (fun w => w.1 == p.1) s.f.m.writes
        · rfl
        · exact absurd ⟨_, h⟩ hwr'
      rw [cycNext_none he hwr, everyMaps_none he hwr, cycCell, enc_rd hS hT hr hQ hw (Nat.le_of_lt hlt), cv_N hmt, hk]

theorem fn_holds {g : MLaw × List Nat} (hg : g ∈ cycGiven s) (X : Nat → Nat)
    (hX : ∀ j, j ∉ cycP s ce keys → j ∉ g.1.key.toList ++ g.2 → X j = r.ρ0 j) :
    evalC X (cycMaps s ce r (T + 1)) g.1.holds = true := by
  rw [congrMC X (cycMaps s ce r (T + 1)) (r.mp 0) _ (fun m hm => cm_o (avoidsMaps_occ (hT.gm g hg) hm))]
  apply holds_any g.1 (r.mp 0) g.2 r.ρ0 (given_holds hS hT hr hg) X
  intro j hj hgs hk
  apply hX j
  · intro hP; have := hT.gz g hg j hP hk hgs; rw [this] at hj; exact absurd hj (by decide)
  · intro hm
    rcases List.mem_append.mp hm with h | h
    · exact hk (mem_toList h)
    · exact hgs h

theorem canon_holds {g : Fact} (hg : g ∈ cycCanon s ce) {Q : Nat → Nat} (hQ : EnvOk s ce keys r T Q) (vals : Nat → Nat) :
    evalC (override g.keys vals Q) (cycMaps s ce r (T + 1)) g.holds = true := by
  have hsp := special_parts hS.dsp
  have hov : ∀ ks : List Nat, (∀ x ∈ ks, x = ce.u ∨ x = ce.k) → EnvOk s ce keys r T (override ks vals Q) := by
    intro ks hks
    refine ⟨?_, ?_, ?_⟩
    · simp only [override]
      rw [if_neg (fun h => by
        rcases hks _ (List.contains_iff_mem.mp h) with e | e
        · exact hsp.1 e.symm
        · exact hsp.2.2.1 e.symm)]
      exact hQ.1
    · simp only [override]
      rw [if_neg (fun h => by
        rcases hks _ (List.contains_iff_mem.mp h) with e | e
        · exact hsp.2.1 e.symm
        · exact hsp.2.2.2.1 e.symm)]
      exact hQ.2.1
    · intro i hi
      simp only [override]
      rw [if_neg (fun h => by
        rcases hks _ (List.contains_iff_mem.mp h) with e | e
        · exact (notP hi).1 (in_special (Or.inl e))
        · exact (notP hi).1 (in_special (Or.inr (Or.inl e))))]
      exact hQ.2.2 i hi
  simp only [cycCanon, List.mem_cons, List.mem_append] at hg
  rcases hg with rfl | rfl | rfl | hg | hg
  · exact start_holds hS hT hr (hov [ce.u] (by simp))
  · exact step_holds hS hT hr true (hov [ce.u] (by simp))
  · exact step_holds hS hT hr false (hov [ce.u] (by simp))
  · simp only [cycMapFacts, List.mem_flatMap, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
    obtain ⟨p, hp, rfl | rfl⟩ := hg
    · exact mapStart_holds hS hT hr hp (hov [ce.u, ce.k] (by simp))
    · exact mapStep_holds hS hT hr hp (hov [ce.u, ce.k] (by simp))
  · simp only [cycFnFacts, List.mem_map] at hg
    obtain ⟨q, hq, rfl⟩ := hg
    exact fn_holds hS hT hr hq _ (fun j hjP hjk => by
      simp only [override]
      rw [if_neg (fun h => hjk (List.contains_iff_mem.mp h))]
      exact hQ.2.2 j hjP)
end facts

/-! The bridge for machines -/

/-- A cyclic proof of a machine law, checked against the machine's encoding (`cycMOk`): the law holds in every state
the machine reaches, at every value of its keys. -/
theorem cyc_machine_sound (s : SMachine) (ce : CycEnc) (facts : List Fact) (nodes : List CNode) (hc : checkCyclic facts nodes = true)
    (law : C) (keys : List Nat) (n : CNode) (hn : n ∈ nodes) (hok : cycMOk s ce facts law keys n = true) :
    ∀ ρ M, SReach s ρ M → ∀ ρ' : Nat → Nat, (∀ i, i ∉ keys → ρ' i = ρ i) → evalC ρ' M law = true := by
  simp only [cycMOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨hsh, hte⟩, hlaw⟩, hfa⟩, hnd⟩ := hok
  have hS := cycShape_of hsh
  have hT := cycTerms_of hte
  simp only [cycNodeOk, Bool.and_eq_true] at hnd
  simp only [cycLawOk, Bool.and_eq_true] at hlaw
  intro ρ M hreach ρ' hρ'
  obtain ⟨r, T, hr, hst, hmp⟩ := reach_run hS.q hreach
  have hsp := special_parts hS.dsp
  have hnot : ∀ i, i ∉ ce.special → cycEnv ce T ρ' i = ρ' i := fun i hi => by
    simp only [cycEnv]
    rw [if_neg (fun e => hi (in_special (Or.inr (Or.inr (Or.inr (Or.inr e)))))),
      if_neg (fun e => hi (in_special (Or.inr (Or.inr (Or.inl e))))), if_neg (fun e => hi (in_special (Or.inr (Or.inr (Or.inr (Or.inl e))))))]
  have hEnv : EnvOk s ce keys r T (cycEnv ce T ρ') := by
    refine ⟨by simp [cycEnv], by simp [cycEnv, Ne.symm hsp.2.2.2.2.2.2, Ne.symm hsp.2.2.2.2.1], ?_⟩
    intro i hi
    obtain ⟨h1, h2, h3, h4⟩ := notP hi
    rw [hnot i h1, hρ' i h2, ← hst]
    exact run_frame hr T (Nat.le_refl T) i (fun h => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact h3 (hS.initv p hp))
      (fun h => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact h3 (hS.stepv p hp)) (fun h => h3 (hS.inv i h)) h4
  have hF : FactsHold facts (cycEnv ce T ρ') (cycMaps s ce r (T + 1)) := by
    intro f hf vals
    have hfi := List.all_eq_true.mp hfa f hf
    simp only [Bool.or_eq_true] at hfi
    rcases hfi with hnc | hcan
    · exact natC_true _ hnc
    · obtain ⟨g, hg, hb⟩ := List.any_eq_true.mp hcan
      simp only [factBeq, Bool.and_eq_true, beq_iff_eq] at hb
      rw [hb.1, beqC_eq hb.2]
      exact canon_holds hS hT hr hg hEnv vals
  have htT : cycEnv ce T ρ' ce.t = T := by simp [cycEnv]
  have hH : ∀ c ∈ n.hyps, evalC (cycEnv ce T ρ') (cycMaps s ce r (T + 1)) c = true := by
    intro c hc
    have h := List.all_eq_true.mp hnd.2 c hc
    simp only [Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · rw [beqC_eq h, congr2C (ρ' := r.ρ0) (M' := r.mp 0) _ (fun j hj => hEnv.2.2 j (avoids_occ hT.prz hj))
        (fun m hm => cm_o (avoidsMaps_occ hT.prm hm))]
      exact hr.pre
    · rw [beqC_eq h, evalC_iff]; simp only [holdsC, evalE, htT, hEnv.1] <;> omega
    · rw [beqC_eq h, evalC_iff]; simp only [holdsC, evalE, hEnv.1, hEnv.2.1] <;> omega
  have hc0 := cyclic_sound facts nodes hc (cycMaps s ce r (T + 1)) (cycEnv ce T ρ') hF n hn hH
  have htT' : evalE (cycEnv ce T ρ') (cycMaps s ce r (T + 1)) (.var ce.t) = T := htT
  rw [beqC_eq hnd.1, enc_trC hS hT hr hEnv htT' (Nat.le_refl T)] at hc0
  rw [congr2C (ρ' := applyS (cycσ ce (.var ce.t)) (cycEnv ce T ρ') (cycMaps s ce r (T + 1))) (M' := cycView s ce r (T + 1) T) law
    (fun j hj => ?_) (fun m hm => ?_)]
  · exact hc0
  · have hj' := avoids_occ hlaw.1 hj
    have hjs : j ∉ ce.special := fun h => hj' (List.mem_append_left _ h)
    have hji : j ∉ s.f.m.inputs := fun h => hj' (List.mem_append_right _ h)
    by_cases hv : j ∈ ce.vtr.map (·.1)
    · rw [enc_σ_in hS hT hr hEnv htT' (Nat.le_refl T) hv, CRun.X, withInputs_other hji, hst]
      exact hρ' j (fun hk => hS.zv j (List.mem_append_right _ hk) hv)
    · rw [enc_σ_out hS hT hr hEnv htT' (Nat.le_refl T) hv, hnot j hjs]
  · have hm' := avoidsMaps_occ hlaw.2 hm
    rw [cv_N (fun h => hm' (List.mem_append_left _ h)), N_not_carried (fun h => hm' (List.mem_append_right _ h)), hmp]

-- The same as a law of the machine about every value of its keys (Sets.lean's `holdsOver`).
theorem cyc_machine_holds {M : Nat → Nat → Nat} {ρ : Nat → Nat} {law : C} {key : Option Nat} {gs : List Nat}
    (h : ∀ ρ' : Nat → Nat, (∀ i, i ∉ key.toList ++ gs → ρ' i = ρ i) → evalC ρ' M law = true) : holdsOver ⟨law, key⟩ M gs ρ := by
  induction gs generalizing ρ with
  | nil =>
    cases key with
    | none => simp only [holdsOver, MLaw.Holds]; exact h ρ (fun _ _ => rfl)
    | some kv =>
      simp only [holdsOver, MLaw.Holds]
      intro v
      exact h _ (fun i hi => by
        simp only [upd]
        rw [if_neg (fun e => hi (by simp [Option.toList, e]))])
  | cons g gs ih =>
    simp only [holdsOver]
    intro v
    apply ih
    intro ρ' hρ'
    apply h
    intro i hi
    rw [hρ' i (fun hm => hi (by
      rcases List.mem_append.mp hm with h1 | h1
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h1)))]
    simp only [upd]
    rw [if_neg (fun e => hi (List.mem_append_right _ (by rw [e]; exact List.mem_cons_self)))]

/-! Recurrences (`recurNodes`) -/

-- A recurrence's values: f(0) is `zero`, f(n + 1) is `next` with x read as n and prev as f(n), the rest of the
-- environment (the further arguments) as given.
def recF (zero next : E) (x prev : Nat) (env : Nat → Nat) (maps : Nat → Nat → Nat) : Nat → Nat
  | 0 => evalE env maps zero
  | n + 1 => evalE (upd (upd env x n) prev (recF zero next x prev env maps n)) maps next

-- The maps with one of them replaced.
def withMap (maps : Nat → Nat → Nat) (f : Nat) (g : Nat → Nat) : Nat → Nat → Nat := fun m => if m = f then g else maps m

-- The function's map, the recurrence's x and prev, the step fact's key.
structure RecEnc where
  f : Nat
  x : Nat
  prev : Nat
  k : Nat

-- The recurrence's two equations as recurNodes states them: f(0) = zero, and at every k, f(k + 1) = next(k, f(k)).
def recFacts (re : RecEnc) (zero next : E) : List Fact :=
  [⟨[], .eq (.get re.f (.const 0)) zero⟩,
   ⟨[re.k], .eq (.get re.f (.add (.var re.k) (.const 1))) (substE [(re.x, .var re.k), (re.prev, .get re.f (.var re.k))] next)⟩]

-- The exported facts are the equations, facts given about other functions (`given`), or true of every natural; the
-- recurrence reads its own values only through prev, and nothing given reads them.
def recOk (re : RecEnc) (zero next : E) (given facts : List Fact) : Bool :=
  !occME re.f zero && !occME re.f next && !occE re.k next && re.x != re.prev && re.k != re.x && re.k != re.prev
    && given.all (fun g => !occMC re.f g.holds)
    && facts.all (fun g => natC g.holds || (recFacts re zero next ++ given).any (factBeq g))

theorem override_nil (vals env : Nat → Nat) : override [] vals env = env := by
  funext i; simp [override]

theorem rec_facts {re : RecEnc} {zero next : E} {given facts : List Fact} (hok : recOk re zero next given facts = true)
    (maps : Nat → Nat → Nat) (env : Nat → Nat) (hg : FactsHold given env maps) :
    FactsHold facts env (withMap maps re.f (recF zero next re.x re.prev env maps)) := by
  simp only [recOk, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hz, hn⟩, hk⟩, hxp⟩, hkx⟩, hkp⟩, hgv⟩, hfa⟩ := hok
  have hM : ∀ e : E, occME re.f e = false → ∀ ρ, evalE ρ (withMap maps re.f (recF zero next re.x re.prev env maps)) e = evalE ρ maps e :=
    fun e he ρ => congrME ρ _ maps e (fun m hm => by
      simp only [withMap]; rw [if_neg (fun h => by rw [h, he] at hm; exact absurd hm (by decide))])
  intro f hf vals
  have hfi := List.all_eq_true.mp hfa f hf
  simp only [Bool.or_eq_true] at hfi
  rcases hfi with hnc | hcan
  · exact natC_true _ hnc
  obtain ⟨g, hg', hb⟩ := List.any_eq_true.mp hcan
  simp only [factBeq, Bool.and_eq_true, beq_iff_eq] at hb
  rw [hb.1, beqC_eq hb.2]
  simp only [recFacts, List.cons_append, List.nil_append, List.mem_cons] at hg'
  rcases hg' with rfl | rfl | hg'
  · show evalC (override [] vals env) _ (.eq (.get re.f (.const 0)) zero) = true
    rw [override_nil, evalC_iff]
    show withMap maps re.f (recF zero next re.x re.prev env maps) re.f 0 = evalE env _ zero
    rw [hM zero hz env]
    simp only [withMap, if_pos (rfl : re.f = re.f), ite_true, recF]
  · show evalC (override [re.k] vals env) _ (.eq (.get re.f (.add (.var re.k) (.const 1)))
      (substE [(re.x, .var re.k), (re.prev, .get re.f (.var re.k))] next)) = true
    rw [evalC_iff]
    show withMap maps re.f (recF zero next re.x re.prev env maps) re.f (override [re.k] vals env re.k + 1) = _
    rw [subst_evalE, hM next hn]
    simp only [withMap, if_pos (rfl : re.f = re.f), ite_true, recF]
    refine congrE _ _ maps next (fun j hj => ?_)
    have hjk : j ≠ re.k := fun h => by rw [h, hk] at hj; exact absurd hj (by decide)
    simp only [upd, applyS, assoc, lookup]
    by_cases hjp : j = re.prev
    · subst hjp
      simp [hxp, Ne.symm hxp, evalE, withMap]
    · by_cases hjx : j = re.x
      · subst hjx
        simp [evalE, hxp]
      · have h1 : (re.x == j) = false := by simpa using Ne.symm hjx
        have h2 : (re.prev == j) = false := by simpa using Ne.symm hjp
        simp only [hjp, hjx, if_false, h1, h2, Bool.false_eq_true, Option.map_none, override]
        rw [if_neg (fun h => hjk (by simpa using h))]
  · rw [congrMC _ _ maps g.holds (fun m hm => by
      simp only [withMap]
      rw [if_neg (fun h => by
        have := List.all_eq_true.mp hgv g hg'; rw [h] at hm; rw [hm] at this; exact absurd this (by decide))])]
    exact hg g hg' vals

/-- A cyclic proof of a recurrence's lemmas and laws between two points (`recurNodes`), checked against its equations
(`recOk`): every node holds of the recurrence's values (`recF`), at every environment where the facts given about the
functions it reads hold. -/
theorem cyc_recur_sound (re : RecEnc) (zero next : E) (given facts : List Fact) (nodes : List CNode)
    (hc : checkCyclic facts nodes = true) (hok : recOk re zero next given facts = true) (maps : Nat → Nat → Nat) (env : Nat → Nat)
    (hg : FactsHold given env maps) : ∀ n ∈ nodes, (∀ c ∈ n.hyps, evalC env (withMap maps re.f (recF zero next re.x re.prev env maps)) c = true) →
      evalC env (withMap maps re.f (recF zero next re.x re.prev env maps)) n.concl = true :=
  cyclic_sound facts nodes hc _ env (rec_facts hok maps env hg)

theorem assoc_map_kv {α : Type} (l : List α) (k : α → Nat) (g : α → E) (y : Nat) :
    assoc (l.map fun a => (k a, g a)) y = (lookup (fun a => k a == y) l).map g := by
  simp only [assoc, lookup_map_pred, Option.map_map]; rfl

theorem holds_of_eq {ρ : Nat → Nat} {M : Nat → Nat → Nat} {a b : E} (h : evalE ρ M a = evalE ρ M b) : evalC ρ M (.eq a b) = true :=
  (evalC_iff ρ M (.eq a b)).mpr h
theorem holds_of_lt {ρ : Nat → Nat} {M : Nat → Nat → Nat} {a b : E} (h : evalE ρ M a < evalE ρ M b) : evalC ρ M (.lt a b) = true :=
  (evalC_iff ρ M (.lt a b)).mpr h

theorem holds_of_le {ρ : Nat → Nat} {M : Nat → Nat → Nat} {a b : E} (h : evalE ρ M a ≤ evalE ρ M b) : evalC ρ M (.le a b) = true :=
  (evalC_iff ρ M (.le a b)).mpr h
theorem and_true2 {ρ : Nat → Nat} {M : Nat → Nat → Nat} {a b : C} (ha : evalC ρ M a = true) (hb : evalC ρ M b = true) :
    evalC ρ M (.and a b) = true := by simp [evalC, ha, hb]

/-! Folds over trees (`foldNodes`) -/

def BTree.size : BTree → Nat
  | .leaf _ => 1
  | .node _ l r => l.size + r.size + 1
-- The inputs a leaf or node carries.
def BTree.req : BTree → Nat → Nat
  | .leaf ι => ι
  | .node ι _ _ => ι
-- The subtrees in post-order: each node after its children, so its right child just before it and its left child just
-- before its right subtree (foldNodes' table, children numbered below their parent).
def BTree.flat : BTree → List BTree
  | .leaf ι => [.leaf ι]
  | .node ι l r => l.flat ++ r.flat ++ [.node ι l r]

theorem flat_length : ∀ t : BTree, t.flat.length = t.size
  | .leaf _ => rfl
  | .node _ l r => by simp [BTree.flat, BTree.size, flat_length l, flat_length r]; omega

theorem size_pos : ∀ t : BTree, 1 ≤ t.size
  | .leaf _ => by simp [BTree.size]
  | .node _ l r => by simp [BTree.size]

theorem flat_last : ∀ t : BTree, t.flat[t.size - 1]? = some t
  | .leaf _ => rfl
  | .node ι l r => by
    simp only [BTree.flat, BTree.size]
    rw [List.getElem?_append_right (by simp [flat_length])]
    simp [flat_length]

theorem flat_node : ∀ (t : BTree) (i : Nat) (ι : Nat → Nat) (l r : BTree), t.flat[i]? = some (.node ι l r) →
    l.size + r.size ≤ i ∧ t.flat[i - 1]? = some r ∧ t.flat[i - 1 - r.size]? = some l
  | .leaf _, i, ι, l, r, h => by
    cases i with
    | zero => simp [BTree.flat] at h
    | succ i => simp [BTree.flat] at h
  | .node ι' l' r', i, ι, l, r, h => by
    have hl := flat_length l'
    have hr := flat_length r'
    have pl := size_pos l'
    have pr := size_pos r'
    have pl2 := size_pos l
    simp only [BTree.flat] at h ⊢
    rcases Nat.lt_or_ge i l'.size with h1 | h1
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by omega)] at h
      obtain ⟨b, e1, e2⟩ := flat_node l' i ι l r h
      refine ⟨b, ?_, ?_⟩
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by omega), e1]
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by omega), e2]
    · rcases Nat.lt_or_ge i (l'.size + r'.size) with h2 | h2
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega), hl] at h
        obtain ⟨b, e1, e2⟩ := flat_node r' (i - l'.size) ι l r h
        refine ⟨by omega, ?_, ?_⟩
        · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega), hl,
            show i - 1 - l'.size = i - l'.size - 1 by omega]
          exact e1
        · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega), hl,
            show i - 1 - r.size - l'.size = i - l'.size - 1 - r.size by omega]
          exact e2
      · rw [List.getElem?_append_right (by simp; omega)] at h
        simp only [List.length_append, hl, hr] at h
        rcases Nat.lt_or_ge i (l'.size + r'.size + 1) with h3 | h3
        · have hi : i - (l'.size + r'.size) = 0 := by omega
          rw [hi] at h
          simp only [List.getElem?_cons_zero, Option.some.injEq, BTree.node.injEq] at h
          obtain ⟨_, hll, hrr⟩ := h
          subst hll
          subst hrr
          refine ⟨by omega, ?_, ?_⟩
          · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega), hl,
              show i - 1 - l'.size = r'.size - 1 by omega, ← hr]
            rw [hr]; exact flat_last r'
          · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by omega),
              show i - 1 - r'.size = l'.size - 1 by omega]
            exact flat_last l'
        · rw [List.getElem?_eq_none (by simp; omega)] at h
          exact absurd h (by simp)

theorem flat_allowed {f : Fold} {ρ : Nat → Nat} {maps : Nat → Nat → Nat} : ∀ t : BTree, Allowed f ρ maps t →
    ∀ s ∈ t.flat, Allowed f ρ maps s
  | .leaf ι, h, s, hs => by simp [BTree.flat] at hs; rw [hs]; exact h
  | .node ι l r, h, s, hs => by
    simp only [BTree.flat, List.mem_append, List.mem_singleton] at hs
    rcases hs with (hs | hs) | hs
    · exact flat_allowed l h.2.1 s hs
    · exact flat_allowed r h.2.2 s hs
    · rw [hs]; exact h

-- The table's variables (a node's number n, the tree's size N) and maps (each node's kind and children, and each
-- state variable and input's value at each node).
structure FoldEnc where
  n : Nat
  N : Nat
  kind : Nat
  left : Nat
  right : Nat
  vtr : List (Nat × Nat)

def foldσ (fe : FoldEnc) (w : E) : List (Nat × E) := fe.vtr.map fun p => (p.1, .get p.2 w)
-- A node's frame: its inputs, and each copy read at the child's number.
def foldNodeσ (f : Fold) (fe : FoldEnc) : List (Nat × E) :=
  f.inputs.map (fun i => (i, substE (foldσ fe (.var fe.n)) (.var i)))
    ++ f.state.map (fun e => (e.2.1, substE (foldσ fe (.get fe.left (.var fe.n))) (.var e.1)))
    ++ f.state.map (fun e => (e.2.2, substE (foldσ fe (.get fe.right (.var fe.n))) (.var e.1)))

-- foldNodes' table fact: below the size, a leaf's values from its inputs, a node's from its children's, numbered below
-- it (with the assumption at each, or without when the fold has none).
def foldTable (f : Fold) (fe : FoldEnc) (withAssume : Bool) : Fact :=
  ⟨[fe.n], .or (.not (.lt (.var fe.n) (.var fe.N))) (.and (.le (.get fe.kind (.var fe.n)) (.const 1)) (.and
    (.or (.not (.eq (.get fe.kind (.var fe.n)) (.const 0))) (andL (trueC :: ((if withAssume then [substC (foldσ fe (.var fe.n)) f.assume] else [])
      ++ f.leaf.map fun p => .eq (substE (foldσ fe (.var fe.n)) (.var p.1)) (substE (foldσ fe (.var fe.n)) p.2)))))
    (.or (.not (.eq (.get fe.kind (.var fe.n)) (.const 1))) (andL (.lt (.get fe.left (.var fe.n)) (.var fe.n) :: .lt (.get fe.right (.var fe.n)) (.var fe.n)
      :: ((if withAssume then [substC (foldσ fe (.var fe.n)) f.assume] else [])
      ++ f.leaf.map fun p => .eq (substE (foldσ fe (.var fe.n)) (.var p.1)) (substE (foldNodeσ f fe) ((assoc f.node p.1).getD (.var p.1)))))))))⟩

def foldCopies (f : Fold) : List Nat := f.state.map (·.2.1) ++ f.state.map (·.2.2)
def foldTM (fe : FoldEnc) : List Nat := [fe.kind, fe.left, fe.right] ++ fe.vtr.map (·.2)
def foldNot (f : Fold) (fe : FoldEnc) : List Nat := f.state.map (·.1) ++ foldCopies f ++ [fe.n, fe.N]

-- The table fits the fold: names apart, every input and state variable with its map, leaf and node set the state
-- variables, leaves and the assumption read no state variable or copy, nodes no state variable, the precondition
-- params alone, the law no input or copy; none reads the added variables or maps.
def foldShapeOk (f : Fold) (fe : FoldEnc) : Bool :=
  copiesOk f && distinct (f.inputs ++ f.state.map (·.1) ++ foldCopies f ++ [fe.n, fe.N]) && distinct (f.leaf.map (·.1))
    && f.leaf.all (fun p => (f.state.map (·.1)).contains p.1 && (f.node.map (·.1)).contains p.1)
    && f.node.all (fun p => (f.state.map (·.1)).contains p.1)
    && distinct (foldTM fe) && (f.inputs ++ f.state.map (·.1)).all (fun x => (fe.vtr.map (·.1)).contains x)
    && !(fe.vtr.map (·.1)).contains fe.n && !(fe.vtr.map (·.1)).contains fe.N
def foldTermsOk (f : Fold) (fe : FoldEnc) (law : C) : Bool :=
  f.leaf.all (fun p => avoidsE (foldNot f fe) p.2 && avoidsMapsE (foldTM fe) p.2)
    && f.node.all (fun p => avoidsE (f.state.map (·.1) ++ [fe.n, fe.N]) p.2 && avoidsMapsE (foldTM fe) p.2)
    && avoids (foldNot f fe) f.assume && avoidsMaps (foldTM fe) f.assume
    && avoids (f.inputs ++ foldNot f fe) f.pre && avoidsMaps (foldTM fe) f.pre
    && avoids (f.inputs ++ foldCopies f ++ [fe.n, fe.N]) law && avoidsMaps (foldTM fe) law
def foldOk (f : Fold) (fe : FoldEnc) (facts : List Fact) (law : C) (nd : CNode) : Bool :=
  foldShapeOk f fe && foldTermsOk f fe law
    && facts.all (fun g => natC g.holds || [foldTable f fe true, foldTable f fe false].any (factBeq g))
    && beqC nd.concl (substC (foldσ fe (.var fe.n)) law)
    && nd.hyps.all (fun h => beqC h f.pre || beqC h (.lt (.var fe.n) (.var fe.N)))

-- The tree as foldNodes' table.
def foldMaps (f : Fold) (fe : FoldEnc) (ρ : Nat → Nat) (maps : Nat → Nat → Nat) (t : BTree) : Nat → Nat → Nat := fun i =>
  if i = fe.kind then fun j => match t.flat[j]? with
    | some (.node _ _ _) => 1
    | _ => 0
  else if i = fe.left then fun j => match t.flat[j]? with
    | some (.node _ _ r) => j - 1 - r.size
    | _ => 0
  else if i = fe.right then fun j => j - 1
  else match lookup (fun p => p.2 == i) fe.vtr with
    | some p => fun j => match t.flat[j]? with
      | some s => foldT f ρ maps s p.1
      | none => 0
    | none => maps i

structure FoldShape (f : Fold) (fe : FoldEnc) : Prop where
  copies : copiesOk f = true
  dvars : distinct (f.inputs ++ f.state.map (·.1) ++ foldCopies f ++ [fe.n, fe.N]) = true
  dleaf : distinct (f.leaf.map (·.1)) = true
  leafst : ∀ p ∈ f.leaf, p.1 ∈ f.state.map (·.1)
  leafnode : ∀ p ∈ f.leaf, p.1 ∈ f.node.map (·.1)
  nodest : ∀ p ∈ f.node, p.1 ∈ f.state.map (·.1)
  dtm : distinct (foldTM fe) = true
  vin : ∀ x ∈ f.inputs, x ∈ fe.vtr.map (·.1)
  vst : ∀ x ∈ f.state.map (·.1), x ∈ fe.vtr.map (·.1)
  vn : fe.n ∉ fe.vtr.map (·.1)
  vN : fe.N ∉ fe.vtr.map (·.1)

theorem foldShape_of {f : Fold} {fe : FoldEnc} (h : foldShapeOk f fe = true) : FoldShape f fe := by
  simp only [foldShapeOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hc, hd⟩, hdl⟩, hl⟩, hn⟩, hdt⟩, hv⟩, hvn⟩, hvN⟩ := h
  refine ⟨hc, hd, hdl, fun p hp => List.contains_iff_mem.mp (and_parts (List.all_eq_true.mp hl p hp)).1,
    fun p hp => List.contains_iff_mem.mp (and_parts (List.all_eq_true.mp hl p hp)).2,
    fun p hp => List.contains_iff_mem.mp (List.all_eq_true.mp hn p hp), hdt,
    fun x hx => List.contains_iff_mem.mp (List.all_eq_true.mp hv x (List.mem_append_left _ hx)),
    fun x hx => List.contains_iff_mem.mp (List.all_eq_true.mp hv x (List.mem_append_right _ hx)),
    not_mem_of_not_contains hvn, not_mem_of_not_contains hvN⟩

section fold
variable {f : Fold} {fe : FoldEnc} {ρ : Nat → Nat} {maps : Nat → Nat → Nat} {t : BTree} (hS : FoldShape f fe)
include hS

theorem fs_parts : fe.kind ≠ fe.left ∧ fe.kind ≠ fe.right ∧ fe.left ≠ fe.right ∧ (∀ a ∈ fe.vtr.map (·.2), a ≠ fe.kind ∧ a ≠ fe.left ∧ a ≠ fe.right)
    ∧ distinct (fe.vtr.map (·.2)) = true := by
  have h := hS.dtm
  simp only [foldTM, List.cons_append, List.nil_append] at h
  obtain ⟨n1, d1⟩ := distinct_cons h
  obtain ⟨n2, d2⟩ := distinct_cons d1
  obtain ⟨n3, d3⟩ := distinct_cons d2
  refine ⟨fun e => n1 (by rw [e]; simp), fun e => n1 (by rw [e]; simp), fun e => n2 (by rw [e]; simp),
    fun a ha => ⟨fun e => n1 (by rw [← e]; simp [ha]), fun e => n2 (by rw [← e]; simp [ha]), fun e => n3 (by rw [← e]; exact ha)⟩, d3⟩

theorem fm_kind (j : Nat) : foldMaps f fe ρ maps t fe.kind j = match t.flat[j]? with
    | some (.node _ _ _) => 1
    | _ => 0 := by
  simp only [foldMaps, if_pos rfl, ite_true]
theorem fm_left (j : Nat) : foldMaps f fe ρ maps t fe.left j = match t.flat[j]? with
    | some (.node _ _ r) => j - 1 - r.size
    | _ => 0 := by
  have := fs_parts hS
  simp only [foldMaps, if_neg (Ne.symm this.1), if_pos rfl, ite_true]
theorem fm_right (j : Nat) : foldMaps f fe ρ maps t fe.right j = j - 1 := by
  have := fs_parts hS
  simp only [foldMaps, if_neg (Ne.symm this.2.1), if_neg (Ne.symm this.2.2.1), if_pos rfl, ite_true]
theorem fm_v {p : Nat × Nat} (hp : p ∈ fe.vtr) (j : Nat) : foldMaps f fe ρ maps t p.2 j = match t.flat[j]? with
    | some s => foldT f ρ maps s p.1
    | none => 0 := by
  obtain ⟨_, _, _, ha, hd⟩ := fs_parts hS
  have h3 := ha p.2 (List.mem_map.mpr ⟨p, hp, rfl⟩)
  simp only [foldMaps, if_neg h3.1, if_neg h3.2.1, if_neg h3.2.2, lookup_ren hd p hp]
theorem fm_o {i : Nat} (hi : i ∉ foldTM fe) : foldMaps f fe ρ maps t i = maps i := by
  have h1 : i ≠ fe.kind := fun e => hi (by simp [foldTM, e])
  have h2 : i ≠ fe.left := fun e => hi (by simp [foldTM, e])
  have h3 : i ≠ fe.right := fun e => hi (by simp [foldTM, e])
  have hn : lookup (fun p => p.2 == i) fe.vtr = none := lookup_none (fun q hq => by
    simp only [beq_eq_false_iff_ne]; intro he
    exact hi (List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, he⟩)))
  simp only [foldMaps, if_neg h1, if_neg h2, if_neg h3, hn]

-- What no leaf or node sets, and no copy: the inputs a node carries, else as before the tree.
theorem foldT_frame {y : Nat} (hy : y ∉ f.state.map (·.1)) (hc : y ∉ foldCopies f) (s : BTree) :
    foldT f ρ maps s y = withInputs f.inputs ρ s.req y := by
  cases s with
  | leaf ι =>
    simp only [foldT, BTree.req]
    exact applyS_other (fun h => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact hy (hS.leafst p hp)) _ _
  | node ι l r =>
    simp only [foldT, BTree.req]
    rw [applyS_other (fun h => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact hy (hS.nodest p hp))]
    exact withChildren_plain f _ _ _ (fun h => hc (List.mem_append_left _ h)) (fun h => hc (List.mem_append_right _ h))

theorem fold_σ_in {Q : Nat → Nat} {w : E} {j : Nat} {s : BTree} (hw : evalE Q (foldMaps f fe ρ maps t) w = j)
    (hs : t.flat[j]? = some s) {x : Nat} (hx : x ∈ fe.vtr.map (·.1)) : applyS (foldσ fe w) Q (foldMaps f fe ρ maps t) x = foldT f ρ maps s x := by
  cases h : lookup (fun p => p.1 == x) fe.vtr with
  | none =>
    exfalso; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have := lookup_none_all h p hp; simp at this
  | some q =>
    obtain ⟨hq, hqx⟩ := lookup_some h
    have hqx' : q.1 = x := by simpa using hqx
    have ha : assoc (foldσ fe w) x = some (.get q.2 w) := by
      simp only [assoc, foldσ, lookup_map_pred, h, Option.map_some]
    simp only [applyS, ha, evalE, fm_v hS hq, hw, hs, hqx']

theorem fold_σ_out {Q : Nat → Nat} {w : E} {x : Nat} (hx : x ∉ fe.vtr.map (·.1)) :
    applyS (foldσ fe w) Q (foldMaps f fe ρ maps t) x = Q x := by
  apply applyS_other
  intro h; apply hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

-- A term that reads no state variable, copy or added variable, at a node's frame: at its inputs.
theorem fold_at {Q : Nat → Nat} (hQ : ∀ i, i ≠ fe.n → i ≠ fe.N → Q i = ρ i) {w : E} {j : Nat} {s : BTree}
    (hw : evalE Q (foldMaps f fe ρ maps t) w = j) (hs : t.flat[j]? = some s) {y : Nat} (hy : y ∉ foldNot f fe) :
    applyS (foldσ fe w) Q (foldMaps f fe ρ maps t) y = withInputs f.inputs ρ s.req y := by
  have hy1 : y ∉ f.state.map (·.1) := fun h => hy (by simp only [foldNot, List.mem_append]; exact Or.inl (Or.inl h))
  have hy2 : y ∉ foldCopies f := fun h => hy (by simp only [foldNot, List.mem_append]; exact Or.inl (Or.inr h))
  have hy3 : y ≠ fe.n := fun e => hy (by simp [foldNot, e])
  have hy4 : y ≠ fe.N := fun e => hy (by simp [foldNot, e])
  by_cases hv : y ∈ fe.vtr.map (·.1)
  · rw [fold_σ_in hS hw hs hv, foldT_frame hS hy1 hy2]
  · rw [fold_σ_out hS hv, hQ y hy3 hy4, withInputs_other (fun h => hv (hS.vin y h))]

theorem dvars_parts : (∀ x ∈ f.inputs, x ∉ foldCopies f) ∧ fe.n ≠ fe.N ∧ (∀ x ∈ f.inputs ++ f.state.map (·.1) ++ foldCopies f, x ≠ fe.n ∧ x ≠ fe.N) := by
  obtain ⟨d1, d2, d3⟩ := distinct_append hS.dvars
  obtain ⟨d4, _, d6⟩ := distinct_append d1
  obtain ⟨_, _, d9⟩ := distinct_append d4
  obtain ⟨n1, _⟩ := distinct_cons d2
  refine ⟨fun x hx hc => d6 x (List.mem_append_left _ hx) hc, fun e => n1 (by rw [e]; simp), fun x hx => ⟨fun e => d3 x hx (by rw [e]; simp), fun e => d3 x hx (by rw [e]; simp)⟩⟩

-- A node's frame, as foldNodeσ reads it from the table: as withChildren reads it from the children.
theorem fold_node {Q : Nat → Nat} (hQ : ∀ i, i ≠ fe.n → i ≠ fe.N → Q i = ρ i) {j : Nat} {ι : Nat → Nat} {l r : BTree}
    (hs : t.flat[j]? = some (.node ι l r)) (hj : Q fe.n = j) {y : Nat} (hy1 : y ∉ f.state.map (·.1)) (hy2 : y ≠ fe.n) (hy3 : y ≠ fe.N) :
    applyS (foldNodeσ f fe) Q (foldMaps f fe ρ maps t) y = withChildren f (withInputs f.inputs ρ ι) (foldT f ρ maps l) (foldT f ρ maps r) y := by
  obtain ⟨_, hr1, hl1⟩ := flat_node t j ι l r hs
  have hwn : evalE Q (foldMaps f fe ρ maps t) (.var fe.n) = j := hj
  have hwl : evalE Q (foldMaps f fe ρ maps t) (.get fe.left (.var fe.n)) = j - 1 - r.size := by
    simp only [evalE, hj, fm_left hS, hs]
  have hwr : evalE Q (foldMaps f fe ρ maps t) (.get fe.right (.var fe.n)) = j - 1 := by
    simp only [evalE, hj, fm_right hS]
  have hcp := (dvars_parts hS).1
  simp only [applyS, foldNodeσ, assoc_append_or, assoc_map_kv, withChildren]
  by_cases hin : y ∈ f.inputs
  · have hl0 : lookup (fun e => e.2.1 == y) f.state = none := lookup_none (fun e he => by
      simp only [beq_eq_false_iff_ne]; intro h; exact hcp y hin (List.mem_append_left _ (List.mem_map.mpr ⟨e, he, h⟩)))
    have hr0 : lookup (fun e => e.2.2 == y) f.state = none := lookup_none (fun e he => by
      simp only [beq_eq_false_iff_ne]; intro h; exact hcp y hin (List.mem_append_right _ (List.mem_map.mpr ⟨e, he, h⟩)))
    have hi0 : (lookup (fun i => i == y) f.inputs).map (fun i => substE (foldσ fe (.var fe.n)) (.var i)) = some (substE (foldσ fe (.var fe.n)) (.var y)) := by
      cases h : lookup (fun i => i == y) f.inputs with
      | none => have := lookup_none_all h y hin; simp at this
      | some i => obtain ⟨_, hi⟩ := lookup_some h; simp only [beq_iff_eq] at hi; simp [hi]
    simp only [hl0, hr0, hi0, Option.some_or]
    rw [subst_evalE]
    show applyS (foldσ fe (.var fe.n)) Q (foldMaps f fe ρ maps t) y = _
    rw [fold_σ_in hS hwn hs (hS.vin y hin), foldT_frame hS hy1 (hcp y hin)]
    rfl
  · have hi0 : lookup (fun i => i == y) f.inputs = none := lookup_none (fun i hi => by
      simp only [beq_eq_false_iff_ne]; intro h; exact hin (h ▸ hi))
    simp only [hi0, Option.map_none, Option.none_or]
    cases hl : lookup (fun e => e.2.1 == y) f.state with
    | some e =>
      obtain ⟨he, _⟩ := lookup_some hl
      simp only [Option.map_some, Option.some_or]
      rw [subst_evalE]
      show applyS (foldσ fe (.get fe.left (.var fe.n))) Q (foldMaps f fe ρ maps t) e.1 = _
      exact fold_σ_in hS hwl hl1 (hS.vst e.1 (List.mem_map.mpr ⟨e, he, rfl⟩))
    | none =>
      simp only [Option.map_none, Option.none_or]
      cases hr : lookup (fun e => e.2.2 == y) f.state with
      | some e =>
        obtain ⟨he, _⟩ := lookup_some hr
        simp only [Option.map_some]
        rw [subst_evalE]
        show applyS (foldσ fe (.get fe.right (.var fe.n))) Q (foldMaps f fe ρ maps t) e.1 = _
        exact fold_σ_in hS hwr hr1 (hS.vst e.1 (List.mem_map.mpr ⟨e, he, rfl⟩))
      | none =>
        simp only [Option.map_none]
        rw [hQ y hy2 hy3, withInputs_other hin]
end fold

structure FoldTerms (f : Fold) (fe : FoldEnc) (law : C) : Prop where
  leafz : ∀ p ∈ f.leaf, avoidsE (foldNot f fe) p.2 = true
  leafm : ∀ p ∈ f.leaf, avoidsMapsE (foldTM fe) p.2 = true
  nodez : ∀ p ∈ f.node, avoidsE (f.state.map (·.1) ++ [fe.n, fe.N]) p.2 = true
  nodem : ∀ p ∈ f.node, avoidsMapsE (foldTM fe) p.2 = true
  asz : avoids (foldNot f fe) f.assume = true
  asm : avoidsMaps (foldTM fe) f.assume = true
  prz : avoids (f.inputs ++ foldNot f fe) f.pre = true
  prm : avoidsMaps (foldTM fe) f.pre = true
  lawz : avoids (f.inputs ++ foldCopies f ++ [fe.n, fe.N]) law = true
  lawm : avoidsMaps (foldTM fe) law = true

theorem foldTerms_of {f : Fold} {fe : FoldEnc} {law : C} (h : foldTermsOk f fe law = true) : FoldTerms f fe law := by
  simp only [foldTermsOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hl, hn⟩, ha⟩, ham⟩, hp⟩, hpm⟩, hz⟩, hzm⟩ := h
  exact ⟨fun p hp => (and_parts (List.all_eq_true.mp hl p hp)).1, fun p hp => (and_parts (List.all_eq_true.mp hl p hp)).2,
    fun p hp => (and_parts (List.all_eq_true.mp hn p hp)).1, fun p hp => (and_parts (List.all_eq_true.mp hn p hp)).2, ha, ham, hp, hpm, hz, hzm⟩

-- The table's fact holds of the tree's table, wherever T and Ω... the size N is the tree's.
theorem table_holds {f : Fold} {fe : FoldEnc} {law : C} {ρ : Nat → Nat} {maps : Nat → Nat → Nat} {t : BTree} (hS : FoldShape f fe)
    (hT : FoldTerms f fe law) (hA : Allowed f ρ maps t) (b : Bool) {Q : Nat → Nat} (hQ : ∀ i, i ≠ fe.n → i ≠ fe.N → Q i = ρ i)
    (hN : Q fe.N = t.size) : evalC Q (foldMaps f fe ρ maps t) (foldTable f fe b).holds = true := by
  apply impl_true
  intro h0
  rw [evalC_iff] at h0; simp only [holdsC, evalE] at h0
  rw [hN, ← flat_length] at h0
  have hs : t.flat[Q fe.n]? = some t.flat[Q fe.n] := List.getElem?_eq_getElem h0
  have hal := flat_allowed t hA _ (List.getElem_mem h0)
  have hw : evalE Q (foldMaps f fe ρ maps t) (.var fe.n) = Q fe.n := rfl
  have hkind : evalE Q (foldMaps f fe ρ maps t) (.get fe.kind (.var fe.n)) = match t.flat[Q fe.n]? with
      | some (.node _ _ _) => 1
      | _ => 0 := by simp only [evalE, fm_kind hS]
  -- the assumption, at the node's own inputs
  have hasm : ∀ (s : BTree), t.flat[Q fe.n]? = some s → evalC (withInputs f.inputs ρ s.req) maps f.assume = true →
      evalC Q (foldMaps f fe ρ maps t) (substC (foldσ fe (.var fe.n)) f.assume) = true := by
    intro s hs' hx
    rw [subst_evalC, congr2C (ρ' := withInputs f.inputs ρ s.req) (M' := maps) f.assume
      (fun y hy => fold_at hS hQ hw hs' (avoids_occ hT.asz hy)) (fun m hm => fm_o hS (avoidsMaps_occ hT.asm hm))]
    exact hx
  generalize t.flat[Q fe.n] = s at hs hal
  cases s with
  | leaf ι =>
    have hk : evalE Q (foldMaps f fe ρ maps t) (.get fe.kind (.var fe.n)) = 0 := by rw [hkind, hs]
    refine and_true2 (holds_of_le (by rw [hk]; simp [evalE])) (and_true2 (impl_true fun _ => ?_) (impl_true fun h1 => ?_))
    · apply andL_true
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · simp [trueC, evalC, evalE]
      rcases List.mem_append.mp hc with hc | hc
      · cases b
        · simp at hc
        · simp at hc; subst hc; exact hasm _ hs hal
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
        apply holds_of_eq
        rw [subst_evalE, subst_evalE]
        show applyS (foldσ fe (.var fe.n)) Q (foldMaps f fe ρ maps t) p.1 = _
        rw [fold_σ_in hS hw hs (hS.vst p.1 (hS.leafst p hp)), congr2E (ρ' := withInputs f.inputs ρ ι) (M' := maps) p.2
          (fun y hy => fold_at hS hQ hw hs (avoidsE_occ (hT.leafz p hp) hy)) (fun m hm => fm_o hS (avoidsMapsE_occ (hT.leafm p hp) hm))]
        simp only [foldT, applyS, assoc, lookup_unique hS.dleaf hp, Option.map_some]
    · rw [evalC_iff] at h1; simp only [holdsC, hk] at h1; simp [evalE] at h1
  | node ι l r =>
    obtain ⟨hb, _, _⟩ := flat_node t (Q fe.n) ι l r hs
    have pl := size_pos l
    have hk : evalE Q (foldMaps f fe ρ maps t) (.get fe.kind (.var fe.n)) = 1 := by rw [hkind, hs]
    refine and_true2 (holds_of_le (by rw [hk]; simp [evalE])) (and_true2 (impl_true fun h1 => ?_) (impl_true fun _ => ?_))
    · rw [evalC_iff] at h1; simp only [holdsC, hk] at h1; simp [evalE] at h1
    · apply andL_true
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · apply holds_of_lt
        have hl' : evalE Q (foldMaps f fe ρ maps t) (.get fe.left (.var fe.n)) = Q fe.n - 1 - r.size := by
          simp only [evalE, fm_left hS, hs]
        rw [hl']; show Q fe.n - 1 - r.size < Q fe.n; omega
      rcases List.mem_cons.mp hc with rfl | hc
      · apply holds_of_lt
        have hr' : evalE Q (foldMaps f fe ρ maps t) (.get fe.right (.var fe.n)) = Q fe.n - 1 := by
          simp only [evalE, fm_right hS]
        rw [hr']; show Q fe.n - 1 < Q fe.n; omega
      rcases List.mem_append.mp hc with hc | hc
      · cases b
        · simp at hc
        · simp at hc; subst hc
          apply hasm _ hs
          show evalC (withInputs f.inputs ρ ι) maps f.assume = true
          rw [← congrC (withChildren f (withInputs f.inputs ρ ι) (foldT f ρ maps l) (foldT f ρ maps r)) _ maps f.assume
            (fun y hy => withChildren_plain f _ _ _
              (fun h => avoids_occ hT.asz hy (by simp only [foldNot, foldCopies, List.mem_append]; exact Or.inl (Or.inr (Or.inl h))))
              (fun h => avoids_occ hT.asz hy (by simp only [foldNot, foldCopies, List.mem_append]; exact Or.inl (Or.inr (Or.inr h)))))]
          exact hal.1
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
        apply holds_of_eq
        rw [subst_evalE, subst_evalE]
        show applyS (foldσ fe (.var fe.n)) Q (foldMaps f fe ρ maps t) p.1 = _
        rw [fold_σ_in hS hw hs (hS.vst p.1 (hS.leafst p hp))]
        simp only [foldT]
        rw [applyS_getD]
        obtain ⟨e, he⟩ : ∃ e, assoc f.node p.1 = some e := by
          cases h : assoc f.node p.1 with
          | some e => exact ⟨e, rfl⟩
          | none =>
            exfalso; obtain ⟨q, hq, hq1⟩ := List.mem_map.mp (hS.leafnode p hp)
            simp only [assoc, Option.map_eq_none_iff] at h
            have := lookup_none_all h q hq; simp [hq1] at this
        have hem := assoc_some_mem he
        rw [he]
        simp only [Option.getD]
        exact congr2E e (fun y hy => (fold_node hS hQ hs rfl (fun h => avoidsE_occ (hT.nodez _ hem) hy (List.mem_append_left _ h))
            (fun h => avoidsE_occ (hT.nodez _ hem) hy (by rw [h]; simp)) (fun h => avoidsE_occ (hT.nodez _ hem) hy (by rw [h]; simp))).symm)
          (fun m hm => (fm_o hS (avoidsMapsE_occ (hT.nodem _ hem) hm)).symm)

def foldEnv (fe : FoldEnc) (t : BTree) (ρ : Nat → Nat) : Nat → Nat := fun i =>
  if i = fe.n then t.size - 1 else if i = fe.N then t.size else ρ i

/-- A cyclic proof of a fold's law over trees as tables (`foldNodes`), checked against the fold's table (`foldOk`): for
params that meet the precondition, the law holds of every tree whose inputs meet the assumption, as `fold_sound` says of
the structural induction. -/
theorem cyc_fold_sound (f : Fold) (fe : FoldEnc) (facts : List Fact) (nodes : List CNode) (hc : checkCyclic facts nodes = true)
    (law : C) (nd : CNode) (hn : nd ∈ nodes) (hok : foldOk f fe facts law nd = true) (maps : Nat → Nat → Nat) (ρ : Nat → Nat)
    (h0 : evalC ρ maps f.pre = true) : ∀ t, Allowed f ρ maps t → evalC (foldT f ρ maps t) maps law = true := by
  intro t hA
  simp only [foldOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨hsh, hte⟩, hfa⟩, hcon⟩, hhy⟩ := hok
  have hS := foldShape_of hsh
  have hT := foldTerms_of hte
  obtain ⟨_, hnN, hx⟩ := dvars_parts hS
  have hE : ∀ i, i ≠ fe.n → i ≠ fe.N → foldEnv fe t ρ i = ρ i := fun i h1 h2 => by simp [foldEnv, h1, h2]
  have hEn : foldEnv fe t ρ fe.n = t.size - 1 := by simp [foldEnv]
  have hEN : foldEnv fe t ρ fe.N = t.size := by simp [foldEnv, Ne.symm hnN]
  have pt := size_pos t
  have hF : FactsHold facts (foldEnv fe t ρ) (foldMaps f fe ρ maps t) := by
    intro g hg vals
    have hgi := List.all_eq_true.mp hfa g hg
    simp only [Bool.or_eq_true] at hgi
    rcases hgi with hnc | hcan
    · exact natC_true _ hnc
    obtain ⟨g', hg', hb⟩ := List.any_eq_true.mp hcan
    simp only [factBeq, Bool.and_eq_true, beq_iff_eq] at hb
    rw [hb.1, beqC_eq hb.2]
    have hk : g'.keys = [fe.n] := by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg'
      rcases hg' with rfl | rfl <;> rfl
    have hQ : ∀ i, i ≠ fe.n → i ≠ fe.N → override g'.keys vals (foldEnv fe t ρ) i = ρ i := fun i h1 h2 => by
      rw [hk]; simp only [override]
      rw [if_neg (fun h => h1 (by simpa using h))]
      exact hE i h1 h2
    have hQN : override g'.keys vals (foldEnv fe t ρ) fe.N = t.size := by
      rw [hk]; simp only [override]
      rw [if_neg (fun h => hnN (by have h' : fe.N = fe.n := by simpa using h
                                   exact h'.symm))]
      exact hEN
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl
    · exact table_holds hS hT hA true hQ hQN
    · exact table_holds hS hT hA false hQ hQN
  have hH : ∀ c ∈ nd.hyps, evalC (foldEnv fe t ρ) (foldMaps f fe ρ maps t) c = true := by
    intro c hc
    have h := List.all_eq_true.mp hhy c hc
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [beqC_eq h, congr2C (ρ' := ρ) (M' := maps) _ (fun y hy => hE y
        (fun e => avoids_occ hT.prz hy (by rw [e]; simp [foldNot])) (fun e => avoids_occ hT.prz hy (by rw [e]; simp [foldNot])))
        (fun m hm => fm_o hS (avoidsMaps_occ hT.prm hm))]
      exact h0
    · rw [beqC_eq h]; apply holds_of_lt; simp only [evalE, hEn, hEN]; omega
  have hc0 := cyclic_sound facts nodes hc (foldMaps f fe ρ maps t) (foldEnv fe t ρ) hF nd hn hH
  have hw : evalE (foldEnv fe t ρ) (foldMaps f fe ρ maps t) (.var fe.n) = t.size - 1 := hEn
  rw [beqC_eq hcon, subst_evalC] at hc0
  refine (congr2C (ρ' := applyS (foldσ fe (.var fe.n)) (foldEnv fe t ρ) (foldMaps f fe ρ maps t)) (M' := foldMaps f fe ρ maps t) law
    (fun y hy => ?_) (fun m hm => (fm_o hS (avoidsMaps_occ hT.lawm hm)).symm)).trans hc0
  have hy' := avoids_occ hT.lawz hy
  have hyi : y ∉ f.inputs := fun h => hy' (List.mem_append_left _ (List.mem_append_left _ h))
  have hyc : y ∉ foldCopies f := fun h => hy' (List.mem_append_left _ (List.mem_append_right _ h))
  have hyn : y ≠ fe.n := fun e => hy' (by rw [e]; simp)
  have hyN : y ≠ fe.N := fun e => hy' (by rw [e]; simp)
  by_cases hv : y ∈ fe.vtr.map (·.1)
  · rw [fold_σ_in hS hw (flat_last t) hv]
  · rw [fold_σ_out hS hv, hE y hyn hyN, foldT_frame hS (fun h => hv (hS.vst y h)) hyc, withInputs_other hyi]

end Kern

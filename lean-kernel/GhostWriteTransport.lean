import GhostMap

/-! One fresh point-written map. Same requests in both directions; no stuttering.
The structural weighted instance at the end builds the entire assigned value
from the *original* parallel writes, not from a proposed transition function. -/
namespace Kern.GhostWrite

abbrev Env := Nat → Nat
abbrev Maps := Nat → Nat → Nat
abbrev State := Env × Maps
abbrev Request := Env × Maps

structure Point where
  map : Nat
  start : Nat
  key : E
  value : E

def aug (s : SMachine) (p : Point) : SGhostedM :=
  ⟨s, [], [(p.map, p.start)], [(p.map, p.key, p.value)], []⟩

-- All scalars, ALL maps except the single new one (including frames,
-- read-only functions and maps not mentioned in the conclusion).
def Off (p : Point) (y x : State) : Prop :=
  y.1 = x.1 ∧ ∀ m, m ≠ p.map → y.2 m = x.2 m

def projection (p : Point) (x : State) : Env × ({m : Nat // m ≠ p.map} → Env) :=
  (x.1, fun m => x.2 m.val)

theorem public_eq {p : Point} {y x : State} (h : Off p y x) : projection p y = projection p x :=
  Prod.ext h.1 (funext fun m => h.2 m.val m.property)

-- This is intentionally labelled. The list stores the latest request first.
-- Unlike a forward simulation that allows zero or more unlabelled steps,
-- Run cannot skip an enabled request or change its carried maps.
inductive Run (s : SMachine) : List Request → State → Prop where
  | start (X : Env) (N : Maps) : StartMaps s.f.m N → evalC X N s.f.m.pre = true →
      (∀ l ∈ s.facts, l.Holds X N) → s.PFacts X N → Run s [] (applyS s.f.m.init X N, N)
  | step {rs x} (q : Request) : Run s rs x →
      evalC (sView s x.1 x.2 q.1 q.2).1 (sView s x.1 x.2 q.1 q.2).2 s.f.m.assume = true →
      Run s (q :: rs) (sNext s x.1 x.2 q.1 q.2)

theorem erase {s rs x} (h : Run s rs x) : SReach s x.1 x.2 := by
  induction h with
  | start X N hm hc hf hp => exact .start X N hm hc hf hp
  | step q _ ha ih => exact .step _ _ q.1 q.2 ih ha

theorem label {s X N} (h : SReach s X N) : ∃ rs, Run s rs (X,N) := by
  induction h with
  | start X N hm hc hf hp => exact ⟨[], .start X N hm hc hf hp⟩
  | step X N I K _ ha ih =>
    obtain ⟨rs, hr⟩ := ih
    exact ⟨(I,K) :: rs, Run.step (x := (X,N)) (I,K) hr ha⟩

section
variable {s : SMachine} {p : Point} (ok : smghostOk (aug s p) = true)
include ok

private theorem lockstep {y x : State} (rel : Off p y x) (q : Request) :
    evalC (sView (aug s p).full y.1 y.2 q.1 q.2).1 (sView (aug s p).full y.1 y.2 q.1 q.2).2 s.f.m.assume =
    evalC (sView s x.1 x.2 q.1 q.2).1 (sView s x.1 x.2 q.1 q.2).2 s.f.m.assume ∧
    Off p (sNext (aug s p).full y.1 y.2 q.1 q.2) (sNext s x.1 x.2 q.1 q.2) := by
  have h := smghost_step (aug s p) ok (ρg := y.1) (ρ := x.1) (Mg := y.2) (M := x.2)
    (fun i _ => congrFun rel.1 i) (fun m hm => rel.2 m (by simpa [aug, SGhostedM.maps] using hm)) q.1 q.2
  exact ⟨h.1, funext (fun i => h.2.1 i (by simp [aug, SGhostedM.vars])),
    fun m hm => h.2.2 m (by simpa [aug, SGhostedM.maps] using hm)⟩

-- The forward start must actually be a start, not merely a reachable state.
private theorem liftStart (X : Env) (N : Maps) (hM : StartMaps s.f.m N)
    (hc : evalC X N s.f.m.pre = true) (hf : ∀ l ∈ s.facts, l.Holds X N) (hp : s.PFacts X N) :
    ∃ y, Run (aug s p).full [] y ∧ Off p y (applyS s.f.m.init X N,N) := by
  let g := aug s p
  let Ng : Maps := fun m => if m = p.map then fun _ => p.start else N m
  have out : ∀ m, m ∉ g.maps → Ng m = N m := by
    intro m hm
    have hn : m ≠ p.map := by simpa [g, aug, SGhostedM.maps] using hm
    simp [Ng, hn]
  obtain ⟨_, _, fresh, _, pre, _, _, _, ini, _, _, _, facts, pfacts⟩ := smghostOk_parts g ok
  have hm : StartMaps g.full.f.m Ng := by
    intro a ha k
    change a ∈ s.f.m.maps0 ++ [(p.map,p.start)] at ha
    rcases List.mem_append.mp ha with ho | hn
    · have hm0 : a.1 ∈ origMaps s := List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_map_of_mem ho)))
      rw [out a.1 (fun h => fresh a.1 h hm0)]
      exact hM a ho k
    · have eq : a = (p.map,p.start) := by simpa using hn
      subst a; simp [Ng]
  have hi : applyS g.full.f.m.init X Ng = applyS s.f.m.init X N := by
    change applyS (s.f.m.init ++ []) X Ng = _
    rw [List.append_nil]
    funext i
    simp only [applyS]
    cases ht : assoc s.f.m.init i with
    | none => rfl
    | some t =>
      have mem : (i,t) ∈ s.f.m.init := by
        simp only [assoc, Option.map_eq_some_iff] at ht
        obtain ⟨a, ha, rfl⟩ := ht
        obtain ⟨hm', he⟩ := lookup_some ha
        simp only [beq_iff_eq] at he
        rw [← he]; exact hm'
      exact evalE_apart (ini (i,t) mem) (fun _ _ => rfl) out
  refine ⟨_, Run.start X Ng hm ?_ ?_ ?_, hi, ?_⟩
  · change evalC X Ng s.f.m.pre = true
    exact (evalC_apart pre (ρ := X) (ρ' := X) (fun _ _ => rfl) out).trans hc
  · intro l hl
    exact holds_transfer (V := []) l (by simp [avoids]) (apartC_parts (facts l hl)).2 (fun _ _ => rfl) out (hf l hl)
  · intro f hf'
    exact holdsOver_maps (apartC_parts (pfacts f hf')).2 out f.2 X (hp f hf')
  · intro m h; exact out m (by simpa [g, aug, SGhostedM.maps] using h)

theorem liftRun {rs x} (h : Run s rs x) : ∃ y, Run (aug s p).full rs y ∧ Off p y x := by
  induction h with
  | start X N hm hc hf hp => exact liftStart ok X N hm hc hf hp
  | step q _ ha ih =>
    obtain ⟨y, hy, rel⟩ := ih
    obtain ⟨eq, hn⟩ := lockstep ok rel q
    exact ⟨_, Run.step q hy (eq.trans ha), hn⟩

theorem projectRun {rs y} (h : Run (aug s p).full rs y) : ∃ x, Run s rs x ∧ Off p y x := by
  induction h with
  | start X N hm hc hf hp =>
    have hm' : StartMaps s.f.m N := fun a ha k => hm a (List.mem_append_left _ ha) k
    refine ⟨_, Run.start X N hm' hc hf hp, ?_, fun _ _ => rfl⟩
    change applyS (s.f.m.init ++ []) X N = _
    rw [List.append_nil]
  | step q _ ha ih =>
    obtain ⟨x, hx, rel⟩ := ih
    obtain ⟨eq, hn⟩ := lockstep ok rel q
    exact ⟨_, Run.step q hx (eq.symm.trans ha), hn⟩

-- For the endpoint-only eliminator reuse the library's SReach lifting theorem.
theorem transport (P : (Env × ({m : Nat // m ≠ p.map} → Env)) → Prop)
    (inv : ∀ y : State, SReach (aug s p).full y.1 y.2 → P (projection p y))
    {X N} (h : SReach s X N) : P (projection p (X,N)) := by
  obtain ⟨Y,T,hr,hx,hm⟩ := smghost_reach (aug s p) ok h
  have rel : Off p (Y,T) (X,N) := ⟨funext (fun i => hx i (by simp [aug, SGhostedM.vars])),
    fun m hn => hm m (by simpa [aug, SGhostedM.maps] using hn)⟩
  rw [← public_eq rel]; exact inv (Y,T) hr
end

/-! Checked write functional. The recipe names columns, not a pre-state term
for their values. Post is constructed by looking up each original point write.
A distinct key *expression* is not evidence that its evaluated key is different. -/
abbrev Write := Nat × E × E

def pointWrite (s : SMachine) (m : Nat) := lookup (fun w : Write => w.1 == m) s.f.m.writes

def post (s : SMachine) (k : E) (m : Nat) : E :=
  match pointWrite s m with
  | none => .get m k
  | some w => if k = w.2.1 then w.2.2 else .ite (.eq k w.2.1) w.2.2 (.get m k)

def noEvery (s : SMachine) (m : Nat) : Prop := lookup (fun w => w.1 == m) s.every = none

theorem post_spec (s : SMachine) (k : E) (m : Nat) (he : noEvery s m) (D : Env) (N : Maps) :
    evalE D N (post s k m) = everyMaps s D N m (evalE D N k) := by
  unfold noEvery at he
  simp only [everyMaps, he, post, writeMaps, pointWrite]
  cases lookup (fun w : Write => w.1 == m) s.f.m.writes with
  | none => rfl
  | some w =>
    by_cases hk : k = w.2.1
    · simp [hk]
    · by_cases ha : evalE D N k = evalE D N w.2.1 <;> simp [hk, evalE, evalC, ha]

structure Recipe where
  point : E
  gates : List (Nat × Nat)
  group : Nat
  weight : Nat
  observer : Nat

def gatesC (read : Nat → E) : List (Nat × Nat) → C → C
  | [], tail => tail
  | (m,n) :: rest, tail => .and (.eq (read m) (.const n)) (gatesC read rest tail)

def contribution (r : Recipe) (read : Nat → E) : E :=
  .ite (gatesC read r.gates (.eq (read r.group) (.var r.observer))) (read r.weight) (.const 0)

def completePoint (s : SMachine) (w : Nat) (r : Recipe) : Point :=
  ⟨w, 0, r.point, contribution r (post s r.point)⟩

def columns (r : Recipe) := r.group :: r.weight :: r.gates.map (·.1)

-- declared is supplied by SOURCE elaboration, never a certificate whitelist.
-- Every field below is a closed syntax test on a concrete packet. A finite
-- `List.all` is used instead of a universal semantic premise about run values.
structure Checked (s : SMachine) (declared : List Nat) (w : Nat) (r : Recipe) : Prop where
  fresh : w ∉ declared
  ok : smghostOk (aug s (completePoint s w r)) = true
  keyApart : apartE [] [w] r.point = true
  valueApart : apartE [] [w] (completePoint s w r).value = true
  rows : (columns r).all (fun m => (pointWrite s m).isSome &&
    (lookup (fun a => a.1 == m) s.every).isNone) = true
  anchor : r.gates.any (fun a => match pointWrite s a.1 with
    | some t => beqE r.point t.2.1 | none => false) = true
  noGhostEvery : noEvery s w
  noGhostPoint : pointWrite s w = none
  obsInput : s.f.m.inputs.contains r.observer = false
  obsFlag : r.observer ∉ flagVars s.f.flags
  obsQ : lookup (fun q => q.1 == r.observer) s.qflags = none
  obsInit : assoc s.f.m.init r.observer = none
  obsStep : assoc s.f.m.step r.observer = none

private theorem Checked.row {s d w r} (h : Checked s d w r) {m} (hm : m ∈ columns r) : noEvery s m := by
  have allRows := List.all_eq_true.mp h.rows m hm
  simp only [Bool.and_eq_true] at allRows
  have hn := allRows.2
  unfold noEvery
  cases he : lookup (fun a => a.1 == m) s.every with
  | none => rfl
  | some a => simp [he] at hn

private theorem gates_congr (D X : Env) (N T : Maps) (f b : Nat → E) (t u : C) :
    ∀ gs : List (Nat × Nat), (∀ a ∈ gs, evalE D N (f a.1) = evalE X T (b a.1)) →
    evalC D N t = evalC X T u → evalC D N (gatesC f gs t) = evalC X T (gatesC b gs u) := by
  intro gs; induction gs with
  | nil => intro _ ht; exact ht
  | cons a gs ih =>
    intro hf ht
    obtain ⟨m,n⟩ := a
    simp only [gatesC, evalC, evalE, hf (m,n) List.mem_cons_self,
      ih (fun a ha => hf a (List.mem_cons_of_mem _ ha)) ht]
    rfl

-- Actual value at the touched point: the contribution on the complete source
-- post-row, with the immutable observer. No ghost update on unchanged keys.
theorem checkedWrite {s d w r} (h : Checked s d w r) (X : Env) (N : Maps) (q : Request) (k : Nat) :
    let v := sView s X N q.1 q.2
    let j := evalE v.1 v.2 r.point
    let sn := sNext s X N q.1 q.2
    let gn := sNext (aug s (completePoint s w r)).full X N q.1 q.2
    gn.2 w k = if k = j then
      evalE X N (contribution r (fun m => .const (sn.2 m j))) else v.2 w k := by
  let v := sView s X N q.1 q.2
  let j := evalE v.1 v.2 r.point
  let R := everyMaps s v.1 v.2
  have obs : v.1 r.observer = X r.observer := by
    change decideFlags _ _ _ _ = _
    rw [decide_other h.obsFlag]
    rw [decideQ_of, h.obsQ]
    exact withInputs_other (by simpa using h.obsInput) _ _
  have cells (m) (hm : m ∈ columns r) : evalE v.1 v.2 (post s r.point m) = R m j :=
    post_spec s r.point m (h.row hm) v.1 v.2
  let fixed : Nat → E := fun m => .const (R m j)
  have gate := gates_congr v.1 X v.2 N (post s r.point) fixed
      (.eq (post s r.point r.group) (.var r.observer)) (.eq (fixed r.group) (.var r.observer))
      r.gates (fun a ha => cells a.1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem ha))))
      (by simp only [fixed, evalC, evalE, cells r.group (by simp [columns]), obs]; rfl)
  have val : evalE v.1 v.2 (contribution r (post s r.point)) = evalE X N (contribution r fixed) := by
    simp only [contribution, evalE, gate, cells r.weight (by simp [columns]), fixed]
  have he := h.noGhostEvery
  unfold noEvery at he
  have hw := h.noGhostPoint
  unfold pointWrite at hw
  change everyMaps (aug s (completePoint s w r)).full v.1 v.2 w k =
    if k = j then evalE X N (contribution r fixed) else v.2 w k
  simp only [everyMaps, aug, SGhostedM.full, List.append_nil, he, writeMaps,
    lookup_append, hw, lookup, completePoint, beq_self_eq_true, ite_true, val, j]

-- The only dependence on the pre-ghost is the ordinary untouched-cell frame.
-- In particular the address and assigned value are equal for ANY two old
-- ghost maps, not just equal on currently reachable or non-removal requests.
noncomputable def assignment (s : SMachine) (p : Point) (x : State) (q : Request) :=
  let v := sView s x.1 x.2 q.1 q.2
  (evalE v.1 v.2 p.key, evalE v.1 v.2 p.value)

theorem assignment_eq {s d w r} (h : Checked s d w r) {y x : State}
    (rel : Off (completePoint s w r) y x) (q : Request) :
    assignment s (completePoint s w r) y q = assignment s (completePoint s w r) x q := by
  let g := aug s (completePoint s w r)
  obtain ⟨_, _, _, _, _, _, hf, hq, _⟩ := smghostOk_parts g h.ok
  let Y := withInputs s.f.m.inputs y.1 q.1
  let X := withInputs s.f.m.inputs x.1 q.1
  let T := withCarried s y.2 q.2
  let N := withCarried s x.2 q.2
  have hX : Y = X := congrArg (fun z => withInputs s.f.m.inputs z q.1) rel.1
  have hN : ∀ m, m ∉ g.maps → T m = N m := by
    intro m hm
    by_cases hc : m ∈ s.carried
    · simp [T, N, withCarried, hc]
    · simpa [T, N, withCarried, hc] using rel.2 m (by simpa [g, aug, SGhostedM.maps, completePoint] using hm)
  have hQ : Agree g.vars (decideQ s Y T) (decideQ s X N) := by
    intro i _
    rw [decideQ_of, decideQ_of]
    cases hl : lookup (fun q => q.1 == i) s.qflags with
    | none => exact congrFun hX i
    | some a =>
      exact ite_all_congr (fun j _ _ => congrFun hX j)
        (fun m hm => hN m (avoidsMaps_occ (apartC_parts (hq a (lookup_some hl).1)).2 hm))
  have hD := decide_apart hf hQ hN
  exact Prod.ext (evalE_apart h.keyApart hD hN) (evalE_apart h.valueApart hD hN)

-- Front door for rule 2: exact target identity, exact map name to erase,
-- deterministic complete post-row update, and exact source public predicate.
theorem checkedTransport {s d w r} (h : Checked s d w r) (target : SMachine)
    (shape : target = (aug s (completePoint s w r)).full)
    (P : (Env × ({m : Nat // m ≠ w} → Env)) → Prop)
    (inv : ∀ y : State, SReach target y.1 y.2 → P (projection (completePoint s w r) y))
    {X N} (hr : SReach s X N) : P (projection (completePoint s w r) (X,N)) := by
  subst target
  exact transport h.ok P inv hr

end Kern.GhostWrite

#print axioms Kern.GhostWrite.label
#print axioms Kern.GhostWrite.erase
#print axioms Kern.GhostWrite.liftRun
#print axioms Kern.GhostWrite.projectRun
#print axioms Kern.GhostWrite.public_eq
#print axioms Kern.GhostWrite.post_spec
#print axioms Kern.GhostWrite.assignment_eq
#print axioms Kern.GhostWrite.checkedWrite
#print axioms Kern.GhostWrite.checkedTransport

import SourceInclusion

/-! Finite (including zero-step) forward simulation. Counts remain part of each
actual producer transition; no arbitrary relation is substituted for GHolds. -/
namespace Bapa.FiniteSimulation
open Kern

inductive Steps {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl (x) : Steps R x x
  | next {x y z} : Steps R x y → R y z → Steps R x z

inductive Reachable {α : Type} (I : α → Prop) (R : α → α → Prop) : α → Prop where
  | initial {x} : I x → Reachable I R x
  | next {x y} : Reachable I R x → R x y → Reachable I R y

theorem Steps.reachable {α : Type} {I : α → Prop} {R : α → α → Prop}
    {x y : α} (steps : Steps R x y) (hx : Reachable I R x) : Reachable I R y := by
  induction steps with
  | refl => exact hx
  | next _ edge ih => exact .next ih edge

theorem Steps.trans {α : Type} {R : α → α → Prop} {x y z : α}
    (xy : Steps R x y) (yz : Steps R y z) : Steps R x z := by
  induction yz with
  | refl => exact xy
  | next _ edge ih => exact .next ih edge

structure ForwardSimulation {α β : Type} (Is : α → Prop) (Rs : α → α → Prop)
    (It : β → Prop) (Rt : β → β → Prop) (rel : α → β → Prop) : Prop where
  initial : ∀ x, Is x → ∃ y, Reachable It Rt y ∧ rel x y
  matching : ∀ x x' y, Reachable Is Rs x → Reachable It Rt y → rel x y → Rs x x' →
    ∃ y', Steps Rt y y' ∧ rel x' y'

theorem ForwardSimulation.reaches {α β : Type} {Is : α → Prop} {Rs : α → α → Prop}
    {It : β → Prop} {Rt : β → β → Prop} {rel : α → β → Prop}
    (sim : ForwardSimulation Is Rs It Rt rel) {x} (hx : Reachable Is Rs x) :
    ∃ y, Reachable It Rt y ∧ rel x y := by
  induction hx with
  | initial hi => exact sim.initial _ hi
  | next hr edge ih =>
    obtain ⟨y, hy, hrel⟩ := ih
    obtain ⟨z, steps, hz⟩ := sim.matching _ _ _ hr hy hrel edge
    exact ⟨z, steps.reachable hy, hz⟩

theorem ForwardSimulation.transfer {α β : Type} {Is : α → Prop} {Rs : α → α → Prop}
    {It : β → Prop} {Rt : β → β → Prop} {rel : α → β → Prop}
    (sim : ForwardSimulation Is Rs It Rt rel) (P : β → Prop) (Q : α → Prop)
    (ht : ∀ y, Reachable It Rt y → P y) (imp : ∀ x y, rel x y → P y → Q x)
    {x} (hx : Reachable Is Rs x) : Q x := by
  obtain ⟨y, hy, hrel⟩ := sim.reaches hx
  exact imp x y hrel (ht y hy)

theorem ForwardSimulation.projected {α β : Type} {Is : α → Prop} {Rs : α → α → Prop}
    {It : β → Prop} {Rt : β → β → Prop} {rel : α → β → Prop}
    (sim : ForwardSimulation Is Rs It Rt rel) (project : β → α)
    (hproject : ∀ x y, rel x y → project y = x) (P : α → Prop)
    (ht : ∀ y, Reachable It Rt y → P (project y)) {x} (hx : Reachable Is Rs x) : P x := by
  obtain ⟨y, hy, hrel⟩ := sim.reaches hx
  rw [← hproject x y hrel]
  exact ht y hy

abbrev KState := (Nat → Nat) × (Nat → Nat → Nat)

def Initial (s : SMachine) (x : KState) : Prop :=
  ∃ ρ M, StartMaps s.f.m M ∧ evalC ρ M s.f.m.pre = true ∧
    (∀ l ∈ s.facts, l.Holds ρ M) ∧ s.PFacts ρ M ∧ x = (applyS s.f.m.init ρ M, M)

def STransition (s : SMachine) (x y : KState) : Prop :=
  ∃ ι κ, evalC (sView s x.1 x.2 ι κ).1 (sView s x.1 x.2 ι κ).2 s.f.m.assume = true ∧
    y = sNext s x.1 x.2 ι κ

def CTransition (s : SMachine) (ds : List CDecl) (x y : KState) : Prop :=
  ∃ ι κ, GHolds ds (withInputs s.f.m.inputs x.1 ι) (withCarried s x.2 κ) ∧
    evalC (sView s x.1 x.2 ι κ).1 (sView s x.1 x.2 ι κ).2 s.f.m.assume = true ∧
    y = sNext s x.1 x.2 ι κ

abbrev SSteps (s : SMachine) := Steps (STransition s)
abbrev CSteps (s : SMachine) (ds : List CDecl) := Steps (CTransition s ds)

theorem sreach_into {s : SMachine} {ρ M} (h : SReach s ρ M) :
    Reachable (Initial s) (STransition s) (ρ,M) := by
  induction h with
  | start ρ M hm hp hf hpf => exact .initial ⟨ρ,M,hm,hp,hf,hpf,rfl⟩
  | step ρ M ι κ _ ha ih => exact .next ih ⟨ι,κ,ha,rfl⟩

theorem sreach_out {s : SMachine} {x} (h : Reachable (Initial s) (STransition s) x) :
    SReach s x.1 x.2 := by
  induction h with
  | initial hi =>
    obtain ⟨ρ,M,hm,hp,hf,hpf,rfl⟩ := hi
    exact .start ρ M hm hp hf hpf
  | next _ edge ih =>
    obtain ⟨ι,κ,ha,rfl⟩ := edge
    exact .step _ _ ι κ ih ha

theorem creach_into {s : SMachine} {ds : List CDecl} {ρ M} (h : CReach s ds ρ M) :
    Reachable (Initial s) (CTransition s ds) (ρ,M) := by
  induction h with
  | start ρ M hm hp hf hpf => exact .initial ⟨ρ,M,hm,hp,hf,hpf,rfl⟩
  | step ρ M ι κ _ hg ha ih => exact .next ih ⟨ι,κ,hg,ha,rfl⟩

theorem creach_out {s : SMachine} {ds : List CDecl} {x}
    (h : Reachable (Initial s) (CTransition s ds) x) : CReach s ds x.1 x.2 := by
  induction h with
  | initial hi =>
    obtain ⟨ρ,M,hm,hp,hf,hpf,rfl⟩ := hi
    exact .start ρ M hm hp hf hpf
  | next _ edge ih =>
    obtain ⟨ι,κ,hg,ha,rfl⟩ := edge
    exact .step _ _ ι κ ih hg ha

abbrev SSimulation (s t : SMachine) (rel : KState → KState → Prop) :=
  ForwardSimulation (Initial s) (STransition s) (Initial t) (STransition t) rel
abbrev CSimulation (s : SMachine) (ds : List CDecl) (t : SMachine) (dt : List CDecl)
    (rel : KState → KState → Prop) :=
  ForwardSimulation (Initial s) (CTransition s ds) (Initial t) (CTransition t dt) rel

theorem sprojected_reach {s t : SMachine} {rel : KState → KState → Prop}
    (sim : SSimulation s t rel) {ρ M} (h : SReach s ρ M) :
    ∃ y, SReach t y.1 y.2 ∧ rel (ρ,M) y := by
  obtain ⟨y, hy, hr⟩ := sim.reaches (sreach_into h)
  exact ⟨y,sreach_out hy,hr⟩

theorem cprojected_reach {s t : SMachine} {ds dt : List CDecl} {rel : KState → KState → Prop}
    (sim : CSimulation s ds t dt rel) {ρ M} (h : CReach s ds ρ M) :
    ∃ y, CReach t dt y.1 y.2 ∧ rel (ρ,M) y := by
  obtain ⟨y, hy, hr⟩ := sim.reaches (creach_into h)
  exact ⟨y,creach_out hy,hr⟩

/-- The relation can require an idle phase boundary as well as projection
agreement. Intermediate states need satisfy neither of those requirements. -/
theorem cprojected_law {s t : SMachine} {ds dt : List CDecl} {rel : KState → KState → Prop}
    (sim : CSimulation s ds t dt rel) (project : KState → KState)
    (hp : ∀ x y, rel x y → project y = x) (P : KState → Prop)
    (ht : ∀ ρ M, CReach t dt ρ M → P (project (ρ,M))) {ρ M} (h : CReach s ds ρ M) :
    P (ρ,M) := by
  obtain ⟨y, hy, hr⟩ := cprojected_reach sim h
  rw [← hp _ _ hr]
  exact ht y.1 y.2 hy

theorem sprojected_law {s t : SMachine} {rel : KState → KState → Prop}
    (sim : SSimulation s t rel) (project : KState → KState)
    (hp : ∀ x y, rel x y → project y = x) (P : KState → Prop)
    (ht : ∀ ρ M, SReach t ρ M → P (project (ρ,M))) {ρ M} (h : SReach s ρ M) :
    P (ρ,M) := by
  obtain ⟨y, hy, hr⟩ := sprojected_reach sim h
  rw [← hp _ _ hr]
  exact ht y.1 y.2 hy

/-- Compose the new multi-step leg after the checked same-step inclusion. -/
theorem cafter_inclusion {s u t : SMachine} {ds dt : List CDecl} {rel : KState → KState → Prop}
    (inc : SourceInclusion s u) (sim : CSimulation u ds t dt rel)
    {ρ M} (h : CReach s ds ρ M) : ∃ y, CReach t dt y.1 y.2 ∧ rel (ρ,M) y :=
  cprojected_reach sim (inc.creach ds h)

theorem safter_inclusion {s u t : SMachine} {rel : KState → KState → Prop}
    (inc : SourceInclusion s u) (sim : SSimulation u t rel)
    {ρ M} (h : SReach s ρ M) : ∃ y, SReach t y.1 y.2 ∧ rel (ρ,M) y :=
  sprojected_reach sim (inc.sreach h)

/-- Observable projections may omit source input temporaries as well as target
scan registers. Only the public store projection must agree at boundaries. -/
theorem cobservable_law {Ω : Type} {s t : SMachine} {ds dt : List CDecl}
    {rel : KState → KState → Prop} (sim : CSimulation s ds t dt rel)
    (sourceView targetView : KState → Ω)
    (hp : ∀ x y, rel x y → targetView y = sourceView x) (P : Ω → Prop)
    (ht : ∀ ρ M, CReach t dt ρ M → P (targetView (ρ,M))) {ρ M} (h : CReach s ds ρ M) :
    P (sourceView (ρ,M)) := by
  obtain ⟨y, hy, hr⟩ := cprojected_reach sim h
  rw [← hp _ _ hr]
  exact ht y.1 y.2 hy

#print axioms cobservable_law
#print axioms ForwardSimulation.reaches
#print axioms ForwardSimulation.projected
#print axioms cprojected_reach
#print axioms sprojected_reach
#print axioms cprojected_law
#print axioms sprojected_law
#print axioms cafter_inclusion
#print axioms safter_inclusion
end Bapa.FiniteSimulation

import CountMachine

/-! Search-free rewriting of retained certificates. This is a candidate
transformation, not a theorem that arbitrary bound erasure preserves validity.
Arithmetic leaf rows, count-instance coefficients and arithmetic proof steps
are kept. Splits for erased bound atoms are pruned in the corresponding
direction; all other split choices remain. The existing complete trusted
checker MUST accept the resulting candidate before any theorem is claimed. -/
namespace Bapa.CertificateBoundErasure
open Kern

mutual
  def expr (bound : Nat) : E → E
    | .var i => .var i
    | .const n => .const n
    | .add a b => .add (expr bound a) (expr bound b)
    | .sub a b => .sub (expr bound a) (expr bound b)
    | .mul n a => .mul n (expr bound a)
    | .min a b => .min (expr bound a) (expr bound b)
    | .max a b => .max (expr bound a) (expr bound b)
    | .prod a b => .prod (expr bound a) (expr bound b)
    | .ite p a b => .ite (condition bound p) (expr bound a) (expr bound b)
    | .get m k => .get m (expr bound k)
    | .tup a b => .tup (expr bound a) (expr bound b)
    | .proj i a => .proj i (expr bound a)
  def condition (bound : Nat) : C → C
    | .lt a (.const n) => if n = bound then trueC else .lt (expr bound a) (.const n)
    | .le a (.const n) => if n = bound then trueC else .le (expr bound a) (.const n)
    | .lt a b => .lt (expr bound a) (expr bound b)
    | .le a b => .le (expr bound a) (expr bound b)
    | .eq a b => .eq (expr bound a) (expr bound b)
    | .and a b => .and (condition bound a) (condition bound b)
    | .or a b => .or (condition bound a) (condition bound b)
    | .not a => .not (condition bound a)
end

def variableDefinition (bound : Nat) : VDef → VDef
  | .term e => .term (expr bound e)
  | d => d

def erasedSplit (bound : Nat) (r : Cert.Row) : Option Bool :=
  match r.coefs with
  | [(_, a)] =>
    if a = 1 ∧ (r.const = 1 - (bound : Int) ∨ r.const = -(bound : Int)) then some true
    else if a = -1 ∧ (r.const = (bound : Int) ∨ r.const = (bound : Int) + 1) then some false
    else none
  | _ => none

/-- Deterministic syntactic pruning, NOT an assertion that the erased atom
    holds in every target model. The post-translation checker is mandatory. -/
def pruneBoundSplits (bound : Nat) : Tree → Tree
  | .split r yes no =>
    match erasedSplit bound r with
    | some true => pruneBoundSplits bound yes
    | some false => pruneBoundSplits bound no
    | none => .split r (pruneBoundSplits bound yes) (pruneBoundSplits bound no)
  | t => t

def certificate (bound : Nat) (k : Kern.Cert) : Kern.Cert :=
  (k.1.map (variableDefinition bound), k.2.1.map (condition bound), pruneBoundSplits bound k.2.2)

def law (bound : Nat) (l : MLaw) : MLaw := {l with holds := condition bound l.holds}

def scalarMachine (bound : Nat) (m : MMachine) : MMachine :=
  {m with
    init := m.init.map fun p => (p.1, expr bound p.2)
    step := m.step.map fun p => (p.1, expr bound p.2)
    writes := m.writes.map fun p => (p.1, expr bound p.2.1, expr bound p.2.2)
    pre := condition bound m.pre
    assume := condition bound m.assume}

def machine (bound : Nat) (s : SMachine) : SMachine :=
  {s with
    f := {s.f with
      m := scalarMachine bound s.f.m
      flags := s.f.flags.map fun p => (p.1, condition bound p.2)}
    every := s.every.map fun p => (p.1, p.2.1, expr bound p.2.2)
    qflags := s.qflags.map fun p => (p.1, p.2.1, condition bound p.2.2)
    facts := s.facts.map (law bound)
    pfacts := s.pfacts.map fun p => (law bound p.1, p.2)}

def pairInstances (bound : Nat) (ps : List (Nat × E × List E)) : List (Nat × E × List E) :=
  ps.map fun p => (p.1, expr bound p.2.1, p.2.2.map (expr bound))

def entry (bound : Nat) (e : SEntry) : SEntry :=
  {e with
    law := law bound e.law
    insts := e.insts.map fun p => (p.1, expr bound p.2)
    qinsts := e.qinsts.map fun p => (p.1, p.2.map (expr bound))
    finsts := e.finsts.map fun p => (p.1, expr bound p.2)
    pinsts := pairInstances bound e.pinsts
    pfinsts := pairInstances bound e.pfinsts
    start := certificate bound e.start
    step := certificate bound e.step}

def countDeclaration (bound : Nat) (d : CDecl) : CDecl :=
  {d with below := expr bound d.below, body := expr bound d.body}

def countedCertificate (bound : Nat) (k : CCert) : CCert :=
  {k with
    hyps := k.hyps.map (condition bound)
    reads := k.reads.map fun p => (p.1, p.2.1, expr bound p.2.2)
    insts := k.insts.map fun i => {i with below := expr bound i.below}
    tab := k.tab.map (variableDefinition bound)
    tree := pruneBoundSplits bound k.tree
    lemmas := k.lemmas.map fun l => {l with tree := pruneBoundSplits bound l.tree}
    picks := k.picks.map fun p => (p.1, p.2.map (expr bound))}

def countedEntry (bound : Nat) (e : CEntry) : CEntry :=
  {e := entry bound e.e, start := countedCertificate bound e.start,
    step := countedCertificate bound e.step}

theorem tree_is_pruned (bound : Nat) (k : CCert) :
    (countedCertificate bound k).tree = pruneBoundSplits bound k.tree := rfl

theorem leaf_rows_unchanged (bound : Nat) (rows : List (Cert.Row × Src))
    (steps : List Cert.Step) (eqs prods : List (Nat × Nat)) :
    pruneBoundSplits bound (.leafAt rows steps eqs prods) = .leafAt rows steps eqs prods := rfl

theorem instance_coefficients_unchanged (bound : Nat) (k : CCert) :
    (countedCertificate bound k).insts.map (fun i => (i.terms, i.unit)) =
      k.insts.map (fun i => (i.terms, i.unit)) := by
  simp [countedCertificate, List.map_map]

/-- A translated family is valid only after its complete existing checker
    succeeds, including all count semantics and freshness side conditions. -/
theorem checked_counted_transport (bound : Nat) (s : SMachine) (ds : List CDecl)
    (ps : List CEntry)
    (h : checkCMachine (machine bound s) (ds.map (countDeclaration bound))
      (ps.map (countedEntry bound)) = true) :
    ∀ ρ M, CReach (machine bound s) (ds.map (countDeclaration bound)) ρ M →
      ∀ e ∈ ps.map (countedEntry bound),
        e.e.Holds ρ (withCnt (ds.map (countDeclaration bound)) ρ M) :=
  cmachine_sound _ _ _ h

#print axioms tree_is_pruned
#print axioms leaf_rows_unchanged
#print axioms instance_coefficients_unchanged
#print axioms checked_counted_transport
end Bapa.CertificateBoundErasure

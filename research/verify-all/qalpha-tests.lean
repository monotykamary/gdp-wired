import QAlpha
open Kern Kern.QAlpha

-- Multi-key relation and a free variable. Bound names may also be used
-- by other flags: only the selected flag is changed.
def qa : Nat × List Nat × C := (7, [1, 2], .eq (.get 4 (.var 1)) (.add (.var 2) (.var 3)))
def qb : Nat × List Nat × C := (8, [1], .eq (.var 1) (.var 3))
example : validQ qa ⟨7, 1, 10⟩ = true := by decide
example : validQ qa ⟨7, 1, 2⟩ = false := by decide
example : validQ qa ⟨7, 1, 3⟩ = false := by decide
example : validQ qa ⟨7, 1, 1⟩ = false := by decide
example : validQ qa ⟨7, 5, 10⟩ = false := by decide
example : renameQ qb ⟨7, 1, 10⟩ = qb := by decide
example : validQ (7, [1, 1, 2], qa.2.2) ⟨7, 1, 10⟩ = true := by decide
example : validQ (renameQ qa ⟨7, 1, 10⟩) ⟨7, 2, 11⟩ = true := by decide
example : validQ (renameQ qa ⟨7, 1, 10⟩) ⟨7, 2, 10⟩ = false := by decide
example (X : Nat → Nat) (N : Nat → Nat → Nat) :
    (∀ k, holdsC (atKeys X (renameQ qa ⟨7, 1, 10⟩).2.1 k) N (renameQ qa ⟨7, 1, 10⟩).2.2) ↔
    (∀ k, holdsC (atKeys X qa.2.1 k) N qa.2.2) :=
  quantifiedQ qa ⟨7, 1, 10⟩ (by decide) X N

def qaMachine (s : SMachine) : SMachine := { s with qflags := [qa, qb] }
def qaRenames : List Rename := [⟨7, 1, 10⟩, ⟨7, 2, 11⟩, ⟨8, 1, 12⟩]
example (s : SMachine) : validAll (qaMachine s) qaRenames = true := by rfl
example (s : SMachine) : validAll (qaMachine s) [⟨7, 1, 10⟩, ⟨7, 2, 10⟩] = false := by rfl
example (s : SMachine) (ds : List CDecl) (ρ M) :
    CReach (renameAll (qaMachine s) qaRenames) ds ρ M ↔ CReach (qaMachine s) ds ρ M :=
  (renameAll_equiv (qaMachine s) qaRenames (by rfl)).creach ds ρ M
#print axioms Kern.QAlpha.cmachine_sound
#print axioms Kern.QAlpha.smachine_sound

-- Universal law transport used by the exporter: no invariant-specific proof.
theorem qalpha_transport (s : SMachine) (rs : List Rename)
    (hv : validAll s rs = true) (ds : List CDecl) (P : (Nat → Nat) → (Nat → Nat → Nat) → Prop)
    (h : ∀ ρ M, CReach (renameAll s rs) ds ρ M → P ρ M) :
    ∀ ρ M, CReach s ds ρ M → P ρ M := by
  intro ρ M hr
  exact h ρ M (((renameAll_equiv s rs hv).creach ds ρ M).mpr hr)
#print axioms quantified
#print axioms decideQ_rename
#print axioms renameAll_equiv
#print axioms Equiv.view
#print axioms Equiv.next
#print axioms Equiv.sreach
#print axioms Equiv.creach
#print axioms qalpha_transport

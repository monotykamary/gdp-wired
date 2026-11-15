import BoundGhost

open Kern

-- The existential binder shadows the ghost label 7, without renaming the body.
def shadowBody : C := .eq (.var 7) (.const 3)
def witnesses : List (Nat × E) := [(7, .const 3), (8, .const 4)]
example : avoids [7] shadowBody = false := by decide
example : avoids ([7].filter fun v => !(witnesses.map (·.1)).contains v) shadowBody = true := by decide
example : avoidsMaps [10] shadowBody = true := by decide
example (ρg ρ : Nat → Nat) (Mg M : Nat → Nat → Nat)
    (hag : Agree [7] ρg ρ) (hm : ∀ mp, mp ∉ [10] → Mg mp = M mp) :
    ∃ f : Nat → Nat, evalC (updAll ρ ((witnesses.map (·.1)).map fun i => (i, f i))) M shadowBody = true := by
  apply some_of_subst_bound_apart witnesses shadowBody (by decide) (by decide) hag hm
  rfl

-- A free raw ghost label remains forbidden, even when another ghost is bound.
def freeBody : C := .eq (.var 9) (.var 7)
example : avoids ([7, 9].filter fun v => !(witnesses.map (·.1)).contains v) freeBody = false := by decide
example : avoids ([7, 9].filter fun v => !(witnesses.map (·.1)).contains v) freeBody ≠ true := by decide

#print axioms Kern.forall_some_of_ghostsubst_bound
#print axioms Kern.some_of_subst_bound_apart

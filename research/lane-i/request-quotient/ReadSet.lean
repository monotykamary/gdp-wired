import Std
namespace RequestQuotient
noncomputable section
attribute [local instance] Classical.propDecidable

inductive Slot where
  | scalar : Nat → Slot
  | cells : Nat → Slot
structure Request where
  scalar : Nat → Nat
  cells : Nat → Nat → Nat

-- Pure expressions after fixing params/state. bind covers count arguments,
-- sum covers bounded counts, every covers quantified guards. Outputs are
-- pointwise expressions, one for each scalar or map coordinate.
inductive Term where
  | lit : Nat → Term
  | input : Nat → Term
  | cell : Nat → Term → Term
  | binary : (Nat → Nat → Nat) → Term → Term → Term
  | choose : Term → Term → Term → Term
  | bind : Term → (Nat → Term) → Term
  | sum : Term → (Nat → Term) → Term
  | every : (Nat → Term) → Term

def eval (r : Request) : Term → Nat
  | .lit n => n
  | .input n => r.scalar n
  | .cell n key => r.cells n (eval r key)
  | .binary op a b => op (eval r a) (eval r b)
  | .choose c a b => if eval r c = 0 then eval r b else eval r a
  | .bind a body => eval r (body (eval r a))
  | .sum n body => ((List.range (eval r n)).map (fun k => eval r (body k))).sum
  | .every body => if ∀ k, eval r (body k) ≠ 0 then 1 else 0

def reads : Term → Slot → Prop
  | .lit _, _ => False
  | .input n, slot => slot = .scalar n
  | .cell n key, slot => slot = .cells n ∨ reads key slot
  | .binary _ a b, slot => reads a slot ∨ reads b slot
  | .choose c a b, slot => reads c slot ∨ reads a slot ∨ reads b slot
  | .bind a body, slot => reads a slot ∨ ∃ k, reads (body k) slot
  | .sum n body, slot => reads n slot ∨ ∃ k, reads (body k) slot
  | .every body, slot => ∃ k, reads (body k) slot

def Agrees (r s : Request) : Slot → Prop
  | .scalar n => r.scalar n = s.scalar n
  | .cells n => ∀ k, r.cells n k = s.cells n k

theorem read_congruence (t : Term) :
    ∀ r s, (∀ slot, reads t slot → Agrees r s slot) → eval r t = eval s t := by
  induction t with
  | lit n => intro r s h; rfl
  | input n =>
      intro r s h
      exact h (.scalar n) rfl
  | cell n key ih =>
      intro r s h
      have hk := ih r s (fun slot hs => h slot (Or.inr hs))
      have hm : ∀ k, r.cells n k = s.cells n k := h (.cells n) (Or.inl rfl)
      simp only [eval, hk, hm]
  | binary op a b ia ib =>
      intro r s h
      have ha := ia r s (fun slot hs => h slot (Or.inl hs))
      have hb := ib r s (fun slot hs => h slot (Or.inr hs))
      simp only [eval, ha, hb]
  | choose c a b ic ia ib =>
      intro r s h
      have hc := ic r s (fun slot hs => h slot (Or.inl hs))
      have ha := ia r s (fun slot hs => h slot (Or.inr (Or.inl hs)))
      have hb := ib r s (fun slot hs => h slot (Or.inr (Or.inr hs)))
      simp only [eval, hc, ha, hb]
  | bind a body ia ih =>
      intro r s h
      have ha := ia r s (fun slot hs => h slot (Or.inl hs))
      have hb : ∀ k, eval r (body k) = eval s (body k) := fun k =>
        ih k r s (fun slot hs => h slot (Or.inr ⟨k, hs⟩))
      simp only [eval, ha, hb]
  | sum n body ihN ih =>
      intro r s h
      have hn := ihN r s (fun slot hs => h slot (Or.inl hs))
      have hb : (fun k => eval r (body k)) = (fun k => eval s (body k)) :=
        funext (fun k => ih k r s (fun slot hs => h slot (Or.inr ⟨k, hs⟩)))
      simp only [eval, hn, hb]
  | every body ih =>
      intro r s h
      have hb : ∀ k, eval r (body k) = eval s (body k) := fun k =>
        ih k r s (fun slot hs => h slot ⟨k, hs⟩)
      simp only [eval, hb]

theorem same_read_projection_same_outputs (outputs : Nat → Term) (r s : Request)
    (h : ∀ key slot, reads (outputs key) slot → Agrees r s slot) :
    (fun key => eval r (outputs key)) = (fun key => eval s (outputs key)) := by
  funext key
  exact read_congruence (outputs key) r s (h key)

@[simp] theorem choose_zero (r : Request) (a b : Term) :
    eval r (.choose (.lit 0) a b) = eval r b := by simp [eval]
theorem choose_nonzero (r : Request) (n : Nat) (h : n ≠ 0) (a b : Term) :
    eval r (.choose (.lit n) a b) = eval r a := by simp [eval, h]
@[simp] theorem choose_same (r : Request) (c a : Term) :
    eval r (.choose c a a) = eval r a := by simp [eval]

-- In a plain-key expression, lower each bound-key map observation to an
-- input slot. There is no remaining direct occurrence of the bound key.
def observationsAt (cells : Nat → Nat → Nat) (key : Nat) : Request :=
  { scalar := fun n => cells n key, cells := cells }

theorem fresh_key_invariance (t : Term) (cells : Nat → Nat → Nat)
    (fallback : Nat → Nat) (a b : Nat)
    (ha : ∀ n, cells n a = fallback n) (hb : ∀ n, cells n b = fallback n) :
    eval (observationsAt cells a) t = eval (observationsAt cells b) t := by
  apply read_congruence t
  intro slot _
  cases slot with
  | scalar n => exact (ha n).trans (hb n).symm
  | cells n => intro k; rfl

#print axioms fresh_key_invariance
#print axioms read_congruence
#print axioms same_read_projection_same_outputs
end
end RequestQuotient

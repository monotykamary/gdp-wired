import Std

/-!
A deliberately restricted countermodel language, not a reinterpretation of any
retained numeric certificate. Every signature is finite and many-sorted.
All sorts are nonempty; empty-domain obligations are EXCLUDED, not padded.
There are no positive-arity function symbols: function-closure depth and the
number of additional function-generated witnesses are both exactly zero.
Only constants, witness variables, universally bound variables, equality and
relations occur. In particular there is no interpreted order, arithmetic,
cardinality, or fixed-64-domain assumption.
-/
namespace Bapa.Relational

structure Signature where
  sorts : Nat
  relations : Nat
  constants : Fin sorts → Nat
  arity : Fin relations → Nat
  argumentSort : (r : Fin relations) → Fin (arity r) → Fin sorts

abbrev SortId (σ : Signature) := Fin σ.sorts

structure Context (σ : Signature) where
  witnesses : SortId σ → Nat
  universals : SortId σ → Nat

inductive Term (σ : Signature) (Γ : Context σ) : SortId σ → Type where
  | constant {s} (i : Fin (σ.constants s)) : Term σ Γ s
  | witness {s} (i : Fin (Γ.witnesses s)) : Term σ Γ s
  | universal {s} (i : Fin (Γ.universals s)) : Term σ Γ s

inductive Matrix (σ : Signature) (Γ : Context σ) where
  | truth : Matrix σ Γ
  | falsity : Matrix σ Γ
  | equal {s} (a b : Term σ Γ s) : Matrix σ Γ
  | relation (r : Fin σ.relations)
      (args : (i : Fin (σ.arity r)) → Term σ Γ (σ.argumentSort r i)) : Matrix σ Γ
  | neg (p : Matrix σ Γ) : Matrix σ Γ
  | conj (p q : Matrix σ Γ) : Matrix σ Γ
  | disj (p q : Matrix σ Γ) : Matrix σ Γ

structure Model (σ : Signature) where
  size : SortId σ → Nat
  nonempty : ∀ s, 0 < size s
  constant : (s : SortId σ) → Fin (σ.constants s) → Fin (size s)
  relation : (r : Fin σ.relations) →
    ((i : Fin (σ.arity r)) → Fin (size (σ.argumentSort r i))) → Prop

variable {σ : Signature} {Γ : Context σ} {s : SortId σ}

abbrev Assignment (M : Model σ) (count : SortId σ → Nat) :=
  (s : SortId σ) → Fin (count s) → Fin (M.size s)

def Term.eval (M : Model σ) (w : Assignment M Γ.witnesses)
    (u : Assignment M Γ.universals) : Term σ Γ s → Fin (M.size s)
  | .constant i => M.constant s i
  | .witness i => w s i
  | .universal i => u s i

def Matrix.eval (M : Model σ) (w : Assignment M Γ.witnesses)
    (u : Assignment M Γ.universals) : Matrix σ Γ → Prop
  | .truth => True
  | .falsity => False
  | .equal a b => a.eval M w u = b.eval M w u
  | .relation r args => M.relation r (fun i => (args i).eval M w u)
  | .neg p => ¬ p.eval M w u
  | .conj p q => p.eval M w u ∧ q.eval M w u
  | .disj p q => p.eval M w u ∨ q.eval M w u

/-- This is satisfiability of the NEGATION of an obligation, not validity. -/
def Satisfies (M : Model σ) (p : Matrix σ Γ) : Prop :=
  ∃ w : Assignment M Γ.witnesses, ∀ u : Assignment M Γ.universals, p.eval M w u

/-- Nonempty sorts require a filler in addition to constants and witnesses.
    This is only the candidate cutoff until small_satisfiability is proved. -/
def cutoff (σ : Signature) (Γ : Context σ) (s : SortId σ) : Nat :=
  σ.constants s + Γ.witnesses s + 1

def functionClosureDepth (_σ : Signature) : Nat := 0

theorem functionClosureDepth_zero (σ : Signature) : functionClosureDepth σ = 0 := rfl

theorem cutoff_positive (σ : Signature) (Γ : Context σ) (s : SortId σ) :
    0 < cutoff σ Γ s := by simp [cutoff]

/-- An induced embedding: equality and every relation, including its negation,
    are reflected. A mere relation-preserving homomorphism is NOT enough. -/
structure Embedding (M N : Model σ) where
  map : (s : SortId σ) → Fin (M.size s) → Fin (N.size s)
  injective : ∀ s a b, map s a = map s b → a = b
  constants : ∀ s i, map s (M.constant s i) = N.constant s i
  relations : ∀ r args,
    M.relation r args ↔ N.relation r (fun i => map _ (args i))

variable {M N : Model σ} {count : SortId σ → Nat}

def Assignment.map (e : Embedding M N) (a : Assignment M count) : Assignment N count :=
  fun s i => e.map s (a s i)

theorem Term.eval_embedding (e : Embedding M N)
    (w : Assignment M Γ.witnesses) (u : Assignment M Γ.universals)
    (t : Term σ Γ s) :
    t.eval N (w.map e) (u.map e) = e.map s (t.eval M w u) := by
  cases t with
  | constant i => exact (e.constants s i).symm
  | witness i => rfl
  | universal i => rfl

/-- Checked semantic transport of the quantifier-free matrix. This theorem
    alone neither embeds the universal quantifier into a larger domain nor
    connects a model to the retained numeric certificate. -/
theorem Matrix.eval_embedding (e : Embedding M N)
    (w : Assignment M Γ.witnesses) (u : Assignment M Γ.universals)
    (p : Matrix σ Γ) :
    p.eval M w u ↔ p.eval N (w.map e) (u.map e) := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | equal a b =>
      simp only [Matrix.eval, Term.eval_embedding]
      exact ⟨congrArg (e.map _), e.injective _ _ _⟩
  | relation r args =>
      simp only [Matrix.eval, Term.eval_embedding]
      exact e.relations r _
  | neg p ih => exact not_congr ih
  | conj p q ihp ihq => exact and_congr ihp ihq
  | disj p q ihp ihq => exact or_congr ihp ihq

#print axioms functionClosureDepth_zero
#print axioms cutoff_positive
#print axioms Term.eval_embedding
#print axioms Matrix.eval_embedding
end Bapa.Relational

import RelationalFragment
import Kernel

/-! Representation only: no certificate coverage or source-to-fragment claim.
    Native tuple keys are injective at every size. A fixed-radix certificate
    does NOT implement this representation merely by dropping its cap. -/
namespace Bapa.Relational

attribute [local instance] Classical.propDecidable

private theorem pair_code_injective {a b c d : Nat}
    (h : Kern.cpair a b = Kern.cpair c d) : a = c ∧ b = d := by
  have hh := congrArg Kern.cun h
  simpa only [Kern.cun_cpair, Prod.mk.injEq] using hh

/-- Equal-length tuple encodings reflect every component, including equality. -/
theorem tuple_code_injective (a b : List Nat) (hlen : a.length = b.length)
    (h : Kern.tupk a = Kern.tupk b) : a = b := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => rfl
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases b with
      | nil => simp at hlen
      | cons y ys =>
          have hlen' : xs.length = ys.length := by simpa using hlen
          cases xs with
          | nil =>
              cases ys with
              | nil => simpa [Kern.tupk] using h
              | cons z zs => simp at hlen'
          | cons z zs =>
              cases ys with
              | nil => simp at hlen'
              | cons t ts =>
                  obtain ⟨hxy, htail⟩ := pair_code_injective h
                  subst y
                  exact congrArg (List.cons x) (ih _ hlen' htail)

variable {σ : Signature} {Γ : Context σ}

abbrev Arguments (M : Model σ) (r : Fin σ.relations) :=
  (i : Fin (σ.arity r)) → Fin (M.size (σ.argumentSort r i))

def argumentCode (args : Arguments M r) : Nat :=
  Kern.tupk (List.ofFn (fun i => (args i).val))

theorem argumentCode_injective {M : Model σ} {r : Fin σ.relations}
    (a b : Arguments M r) (h : argumentCode a = argumentCode b) : a = b := by
  have hl := tuple_code_injective _ _ (by simp) h
  funext i
  apply Fin.ext
  have hv := congrArg (fun xs : List Nat => xs[i.val]?.getD 0) hl
  simpa [i.isLt] using hv

/-- Total numeric map, default zero off the actual relation's tuple domain. -/
noncomputable def numericTableAt (M : Model σ) (r : Fin σ.relations) (key : Nat) : Nat :=
  if h : ∃ args : Arguments M r, argumentCode args = key then
    if M.relation r (Classical.choose h) then 1 else 0
  else 0

noncomputable def numericTables (M : Model σ) (r key : Nat) : Nat :=
  if h : r < σ.relations then numericTableAt M ⟨r, h⟩ key else 0

theorem numericTableAt_code (M : Model σ) (r : Fin σ.relations) (a : Arguments M r) :
    numericTableAt M r (argumentCode a) = if M.relation r a then 1 else 0 := by
  classical
  have hex : ∃ args : Arguments M r, argumentCode args = argumentCode a := ⟨a, rfl⟩
  unfold numericTableAt
  rw [dif_pos hex]
  have hc : Classical.choose hex = a :=
    argumentCode_injective _ _ (Classical.choose_spec hex)
  rw [hc]

theorem numericTables_code (M : Model σ) (r : Fin σ.relations) (a : Arguments M r) :
    numericTables M r.val (argumentCode a) = if M.relation r a then 1 else 0 := by
  classical
  unfold numericTables
  rw [dif_pos r.isLt]
  exact numericTableAt_code M r a

def tupleExpression : List Kern.E → Kern.E
  | [] => .const 0
  | [x] => x
  | x :: xs => .tup x (tupleExpression xs)

theorem tupleExpression_eval (env : Nat → Nat) (maps : Nat → Nat → Nat)
    (xs : List Kern.E) :
    Kern.evalE env maps (tupleExpression xs) = Kern.tupk (xs.map (Kern.evalE env maps)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y ys => simpa only [tupleExpression, Kern.evalE, List.map_cons, Kern.tupk] using congrArg (Kern.cpair (Kern.evalE env maps x)) ih

/-- The term compiler is an argument so the eventual obligation bridge must
    prove its own environment/name mapping rather than assume it silently. -/
def Matrix.compile (terms : (s : SortId σ) → Term σ Γ s → Kern.E) : Matrix σ Γ → Kern.C
  | .truth => .eq (.const 0) (.const 0)
  | .falsity => .eq (.const 0) (.const 1)
  | .equal a b => .eq (terms _ a) (terms _ b)
  | .relation r args => .eq (.get r.val (tupleExpression (List.ofFn (fun i => terms _ (args i))))) (.const 1)
  | .neg p => .not (p.compile terms)
  | .conj p q => .and (p.compile terms) (q.compile terms)
  | .disj p q => .or (p.compile terms) (q.compile terms)

/-- Exact semantic bridge to the *existing* kernel's Nat environments/maps and
    condition evaluator. This does NOT say a retained certificate proves the
    compiled formula: its syntax/name/guard match is a separate required gate. -/
theorem Matrix.compile_correct (M : Model σ)
    (w : Assignment M Γ.witnesses) (u : Assignment M Γ.universals)
    (terms : (s : SortId σ) → Term σ Γ s → Kern.E) (env : Nat → Nat)
    (ht : ∀ s (t : Term σ Γ s), Kern.evalE env (numericTables M) (terms s t) = (t.eval M w u).val)
    (p : Matrix σ Γ) :
    Kern.holdsC env (numericTables M) (p.compile terms) ↔ p.eval M w u := by
  classical
  induction p with
  | truth => simp [Matrix.compile, Matrix.eval, Kern.holdsC, Kern.evalE]
  | falsity => simp [Matrix.compile, Matrix.eval, Kern.holdsC, Kern.evalE]
  | equal a b =>
      simp only [Matrix.compile, Matrix.eval, Kern.holdsC, ht]
      exact Fin.val_inj
  | relation r args =>
      simp only [Matrix.compile, Matrix.eval, Kern.holdsC, Kern.evalE, tupleExpression_eval, List.map_ofFn, Function.comp_def, ht]
      change numericTables M r.val (argumentCode (fun i => (args i).eval M w u)) = 1 ↔ _
      rw [numericTables_code]
      by_cases h : M.relation r (fun i => (args i).eval M w u) <;> simp [h]
  | neg p ih => exact not_congr ih
  | conj p q ihp ihq => exact and_congr ihp ihq
  | disj p q ihp ihq => exact or_congr ihp ihq

/-- Grounding does not decide a relation or the matrix: it only instantiates
    its terms at the supplied sorted assignment. -/
def Term.ground (M : Model σ) (w : Assignment M Γ.witnesses)
    (u : Assignment M Γ.universals) (s : SortId σ) (t : Term σ Γ s) : Kern.E :=
  .const (t.eval M w u).val

/-- Quantifier-preserving countermodel transport to numeric kernel instances.
    The outer assignments retain their exact finite domains. The theorem does
    NOT identify these instances with any retained obligation. -/
theorem Satisfies.numeric_iff (M : Model σ) (p : Matrix σ Γ) :
    Satisfies M p ↔ ∃ w : Assignment M Γ.witnesses,
      ∀ u : Assignment M Γ.universals,
        Kern.holdsC (fun _ => 0) (numericTables M) (p.compile (Term.ground M w u)) := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, fun u => ?_⟩
    exact (p.compile_correct M w u (Term.ground M w u) (fun _ => 0) (fun _ _ => rfl)).mpr (hw u)
  · rintro ⟨w, hw⟩
    refine ⟨w, fun u => ?_⟩
    exact (p.compile_correct M w u (Term.ground M w u) (fun _ => 0) (fun _ _ => rfl)).mp (hw u)

#print axioms Satisfies.numeric_iff
#print axioms tuple_code_injective
#print axioms argumentCode_injective
#print axioms numericTableAt_code
#print axioms numericTables_code
#print axioms tupleExpression_eval
#print axioms Matrix.compile_correct
end Bapa.Relational

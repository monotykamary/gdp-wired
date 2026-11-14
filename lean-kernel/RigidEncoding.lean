import Rigid
import Data

/-!
The next bridge layer, over the representations actually used by emit.ts.
Function arguments use Data.pk (the existing argsKey); state relation tuples
use Kernel.cpair. No new expression or certificate rule is introduced.
-/
namespace Kern.Rigid.Encoding

noncomputable def packed2 (f : Nat → Nat → Nat) (key : Nat) : Nat :=
  f (unpk key).1 (unpk key).2

@[simp] theorem packed2_at (f : Nat → Nat → Nat) (a b : Nat) :
    packed2 f (pk a b) = f a b := by
  simp [packed2, unpk_pk]

def extend (M : Nat → Nat → Nat) (symbol : Nat) (value : Nat → Nat) : Nat → Nat → Nat :=
  fun mp => if mp = symbol then value else M mp

@[simp] theorem extend_own (M : Nat → Nat → Nat) (symbol : Nat) (value : Nat → Nat) :
    extend M symbol value symbol = value := by simp [extend]

theorem extend_other (M : Nat → Nat → Nat) (symbol mp : Nat) (value : Nat → Nat)
    (fresh : mp ≠ symbol) : extend M symbol value mp = M mp := by
  simp [extend, fresh]

def Source (nodes quorums member : Nat) (M : Nat → Nat → Nat) : Prop :=
  ∀ a b, a < quorums → b < quorums →
    ∃ n, n < nodes ∧ M member (pk n a) = 1 ∧ M member (pk n b) = 1

def Lowered (nodes quorums member witness : Nat) (M : Nat → Nat → Nat) : Prop :=
  ∀ a b, a < quorums → b < quorums →
    M witness (pk a b) < nodes ∧
    M member (pk (M witness (pk a b)) a) = 1 ∧
    M member (pk (M witness (pk a b)) b) = 1

/-- A source interpretation extends at a fresh name only. This holds also for
empty sorts and requires every valid argument pair, not only the diagonal. -/
theorem source_iff_extension (nodes quorums member witness : Nat) (M : Nat → Nat → Nat)
    (fresh : member ≠ witness) :
    Source nodes quorums member M ↔
    ∃ M', (∀ mp, mp ≠ witness → M' mp = M mp) ∧ Lowered nodes quorums member witness M' := by
  constructor
  · intro h
    obtain ⟨choose, hc⟩ := (Kern.Rigid.choice2_iff quorums quorums nodes
      (fun a b n => M member (pk n a) = 1 ∧ M member (pk n b) = 1)).mp h
    refine ⟨extend M witness (packed2 choose), ?_, ?_⟩
    · exact fun mp hm => extend_other M witness mp (packed2 choose) hm
    · intro a b ha hb
      simpa [Lowered, extend, fresh] using hc a b ha hb
  · rintro ⟨M', same, h⟩ a b ha hb
    have hw := h a b ha hb
    refine ⟨M' witness (pk a b), hw.1, ?_, ?_⟩
    · simpa [same member fresh] using hw.2.1
    · simpa [same member fresh] using hw.2.2

/-- A machine claim independent of the auxiliary follows from the ORIGINAL
source axiom. The lower-level checker must cover every witness interpretation. -/
theorem discharge (nodes quorums member witness : Nat) (M : Nat → Nat → Nat)
    (fresh : member ≠ witness) (claim : Prop)
    (checked : ∀ M', (∀ mp, mp ≠ witness → M' mp = M mp) →
      Lowered nodes quorums member witness M' → claim)
    (source : Source nodes quorums member M) : claim := by
  obtain ⟨M', same, h⟩ := (source_iff_extension nodes quorums member witness M fresh).mp source
  exact checked M' same h

/-- Exactly the expression built by existing argsKey for a two-argument function. -/
def call2 (symbol : Nat) (a b : E) : E :=
  .get symbol (.add (.prod (.add a b) (.add a b)) b)

@[simp] theorem eval_call2 (ρ : Nat → Nat) (M : Nat → Nat → Nat) (symbol : Nat) (a b : E) :
    evalE ρ M (call2 symbol a b) = M symbol (pk (evalE ρ M a) (evalE ρ M b)) := rfl

/-- Domain guards, output bound, and BOTH membership conjuncts are literal facts. -/
def witnessBody (member witness : Nat) (nodes quorums a b : E) : C :=
  let w := call2 witness a b
  .or (.not (.and (.lt a quorums) (.lt b quorums)))
    (.and (.lt w nodes)
      (.and (.eq (call2 member w a) (.const 1)) (.eq (call2 member w b) (.const 1))))

theorem eval_witnessBody (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (member witness : Nat) (nodes quorums a b : E) :
    evalC ρ M (witnessBody member witness nodes quorums a b) = true ↔
      (evalE ρ M a < evalE ρ M quorums → evalE ρ M b < evalE ρ M quorums →
        M witness (pk (evalE ρ M a) (evalE ρ M b)) < evalE ρ M nodes ∧
        M member (pk (M witness (pk (evalE ρ M a) (evalE ρ M b))) (evalE ρ M a)) = 1 ∧
        M member (pk (M witness (pk (evalE ρ M a) (evalE ρ M b))) (evalE ρ M b)) = 1) := by
  rw [evalC_iff]
  simp only [witnessBody, holdsC, eval_call2, evalE]
  constructor
  · intro h ha hb
    rcases h with h | h
    · exact False.elim (h ⟨ha, hb⟩)
    · exact h
  · intro h
    by_cases ha : evalE ρ M a < evalE ρ M quorums
    · by_cases hb : evalE ρ M b < evalE ρ M quorums
      · exact Or.inr (h ha hb)
      · exact Or.inl (fun x => hb x.2)
    · exact Or.inl (fun x => ha x.1)

/-- Literal MLaw/pfacts layout. Distinct binders cannot capture size parameters. -/
def witnessFact (member witness nodeVar quorumVar aVar bVar : Nat) : MLaw × List Nat :=
  (⟨witnessBody member witness (.var nodeVar) (.var quorumVar) (.var aVar) (.var bVar), some aVar⟩, [bVar])

theorem witnessFact_iff (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (member witness nodeVar quorumVar aVar bVar : Nat)
    (na : nodeVar ≠ aVar) (nb : nodeVar ≠ bVar)
    (qa : quorumVar ≠ aVar) (qb : quorumVar ≠ bVar) (ba : bVar ≠ aVar) :
    holdsOver (witnessFact member witness nodeVar quorumVar aVar bVar).1 M
      (witnessFact member witness nodeVar quorumVar aVar bVar).2 ρ ↔
      Lowered (ρ nodeVar) (ρ quorumVar) member witness M := by
  change (∀ b a, evalC (upd (upd ρ bVar b) aVar a) M
    (witnessBody member witness (.var nodeVar) (.var quorumVar) (.var aVar) (.var bVar)) = true) ↔ _
  simp only [eval_witnessBody, evalE, upd, na, nb, qa, qb, ba, ite_false, ite_true]
  constructor
  · intro h a b ha hb
    exact h b a ha hb
  · intro h b a ha hb
    exact h a b ha hb

/-- Fresh symbols cannot change any original expression that avoids them. -/
theorem evalE_extension (ρ : Nat → Nat) (M : Nat → Nat → Nat) (symbol : Nat)
    (value : Nat → Nat) (e : E) (fresh : avoidsMapsE [symbol] e = true) :
    evalE ρ (extend M symbol value) e = evalE ρ M e := by
  apply congrME
  intro mp hm
  have hn := avoidsMapsE_occ fresh hm
  apply extend_other
  simpa using hn

theorem evalC_extension (ρ : Nat → Nat) (M : Nat → Nat → Nat) (symbol : Nat)
    (value : Nat → Nat) (c : C) (fresh : avoidsMaps [symbol] c = true) :
    evalC ρ (extend M symbol value) c = evalC ρ M c := by
  apply congrMC
  intro mp hm
  have hn := avoidsMaps_occ fresh hm
  apply extend_other
  simpa using hn

/-- Full SMachine update preservation: no point write, bulk write OR carried
replacement can change the rigid interpretation. -/
theorem sNext_fixed (s : SMachine) (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) (symbol : Nat)
    (notCarried : s.carried.contains symbol = false)
    (notEvery : lookup (fun w => w.1 == symbol) s.every = none)
    (notWritten : lookup (fun w => w.1 == symbol) s.f.m.writes = none) :
    (sNext s ρ M ι κ).2 symbol = M symbol := by
  have hn : symbol ∉ s.carried := by
    intro h
    have ht : s.carried.contains symbol = true := List.contains_iff_mem.mpr h
    rw [notCarried] at ht
    contradiction
  funext key
  simp [sNext, everyMaps, notEvery, writeMaps, notWritten, sView, withCarried, hn]

#print axioms source_iff_extension
#print axioms discharge
#print axioms witnessFact_iff
#print axioms evalE_extension
#print axioms evalC_extension
#print axioms sNext_fixed
end Kern.Rigid.Encoding

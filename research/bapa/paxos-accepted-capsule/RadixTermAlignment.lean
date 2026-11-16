import Kernel

/-! The actual post-state goal may reconstruct an explicit tuple through
projections when a whole-address `every` binder is substituted. Kern's term
column lookup is intentionally syntactic. Align only existing term columns to
actual goal subexpressions equal after explicit tuple-projection reduction.
No premises, columns, splits or arithmetic steps are added. This proposes a
candidate; complete kernel checking remains mandatory. -/
namespace Bapa.RadixTermAlignment
open Kern

mutual
  def normalE : E → E
    | .var v => .var v
    | .const n => .const n
    | .add a b => .add (normalE a) (normalE b)
    | .sub a b => .sub (normalE a) (normalE b)
    | .mul n a => .mul n (normalE a)
    | .min a b => .min (normalE a) (normalE b)
    | .max a b => .max (normalE a) (normalE b)
    | .prod a b => .prod (normalE a) (normalE b)
    | .ite p a b => .ite (normalC p) (normalE a) (normalE b)
    | .get m a => .get m (normalE a)
    | .tup a b => .tup (normalE a) (normalE b)
    | .proj i a => match normalE a with
      | .tup x y => if i == 0 then x else y
      | a' => .proj i a'
  def normalC : C → C
    | .lt a b => .lt (normalE a) (normalE b)
    | .le a b => .le (normalE a) (normalE b)
    | .eq a b => .eq (normalE a) (normalE b)
    | .and a b => .and (normalC a) (normalC b)
    | .or a b => .or (normalC a) (normalC b)
    | .not a => .not (normalC a)
end

mutual
  def termsE (e : E) : List E := e :: match e with
    | .var _ | .const _ => []
    | .add a b | .sub a b | .min a b | .max a b | .prod a b | .tup a b =>
      termsE a ++ termsE b
    | .mul _ a | .get _ a | .proj _ a => termsE a
    | .ite p a b => termsC p ++ termsE a ++ termsE b
  def termsC : C → List E
    | .lt a b | .le a b | .eq a b => termsE a ++ termsE b
    | .and a b | .or a b => termsC a ++ termsC b
    | .not a => termsC a
end

def table (goal : List C) (tab : List VDef) : List VDef :=
  let candidates := (goal.flatMap termsC).map (fun e => (normalE e,e))
  tab.map fun d => match d with
    | .term e =>
      let canonical := normalE e
      match candidates.find? (fun p => beqE canonical p.1) with
      | some (_,actual) => .term actual
      | none => .term e
    | d => d

def firstTermIs (tab : List VDef) (e : E) : Bool :=
  match tab with
  | .term a :: _ => beqE a e
  | _ => false

theorem pair_projection : normalE (.proj 0 (.tup (.var 1) (.var 2))) = .var 1 := rfl

theorem nested_projection : normalE
    (.proj 1 (.proj 1 (.tup (.var 1) (.tup (.var 2) (.var 3))))) = .var 3 := rfl

theorem actual_syntax_selected : firstTermIs
    (table [.le (.proj 0 (.tup (.var 1) (.var 2))) (.const 1)] [.term (.var 1)])
    (.proj 0 (.tup (.var 1) (.var 2))) = true := by decide +kernel

theorem unrelated_term_unchanged : firstTermIs
    (table [.le (.proj 0 (.tup (.var 2) (.var 3))) (.const 1)] [.term (.var 7)])
    (.var 7) = true := by decide +kernel

theorem table_length (goal : List C) (tab : List VDef) :
    (table goal tab).length = tab.length := by simp [table]

#print axioms pair_projection
#print axioms nested_projection
#print axioms actual_syntax_selected
#print axioms unrelated_term_unchanged
#print axioms table_length
end Bapa.RadixTermAlignment

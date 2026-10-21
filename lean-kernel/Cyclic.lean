import Kernel

/-!
Cyclic: one rule for every induction, proven sound. Lean 4.34.0, core only, on top of `Kernel.lean`.

A cyclic proof is a list of nodes, each a sequent over the environment: its hypotheses imply its conclusion, for every
environment and every maps that meet the facts. The facts are conditions that hold at every value of their keys (a
function's equations: f(k + 1) = next(k, f(k)) at every k). A node's proof is one kernel goal, refuted by a tree: its
hypotheses, facts at the terms it names, and what other nodes give where it uses them, against its conclusion. A use
of node m reads m at a substitution σ of m's variables by terms over this node's frame, where a guard holds: it gives
m's conclusion at σ, once m's hypotheses at σ follow (one goal each) and m's rank at σ is below this node's rank (one
goal, ranks compared in order). Uses may go to any node, the node itself included: the proof is a graph, its cycles
the inductions. Every back-edge lowers a rank of naturals compared in order, so every chain of uses is finite, and
`cyclic_sound` is well-founded induction on the rank.

Nothing about machines, recurrences or trees is built in: those are instances, a node's variables standing for a step
counter, a recurrence's argument, a node of a table. The goals are built here, from the nodes, so nothing in
kernel/cyclic.ts but its tree check is trusted beyond this file.
-/

namespace Kern

/-- A condition that holds at every value of its keys (the rest of the environment fixed). -/
structure Fact where
  keys : List Nat
  holds : C

/-- A use of node `node` at `σ` where `guard` holds: a tree per hypothesis of that node (each at σ), and one for the
descent of its rank. -/
structure Use where
  node : Nat
  σ : List (Nat × E)
  guard : C
  premises : List (List VDef × Tree)
  descent : List VDef × Tree

/-- A node: hypotheses ⇒ conclusion, its rank (naturals compared in order), the facts it reads at terms
(fact index, a term per key), the nodes it uses, and the tree of its own goal. -/
structure CNode where
  hyps : List C
  concl : C
  rank : List E
  insts : List (Nat × List E)
  uses : List Use
  main : List VDef × Tree

def falseC : C := .lt (.const 0) (.const 0)

/-- `as` below `bs` in order: the first that differs is smaller. -/
def lexLtC : List E → List E → C
  | a :: as, b :: bs => .or (.lt a b) (.and (.eq a b) (lexLtC as bs))
  | _, _ => falseC

/-- The same over values, for lists of one length. -/
def lexLt : List Nat → List Nat → Prop
  | a :: as, b :: bs => as.length = bs.length ∧ (a < b ∨ (a = b ∧ lexLt as bs))
  | _, _ => False

def override (keys : List Nat) (vals env : Nat → Nat) : Nat → Nat := fun i => if keys.contains i then vals i else env i

/-- The facts hold: each at every value of its keys. -/
def FactsHold (facts : List Fact) (env : Nat → Nat) (maps : Nat → Nat → Nat) : Prop :=
  ∀ f ∈ facts, ∀ vals : Nat → Nat, evalC (override f.keys vals env) maps f.holds = true

def cycInsts (facts : List Fact) (insts : List (Nat × List E)) : List C :=
  insts.filterMap fun p => facts[p.1]?.map fun f => substC (f.keys.zip p.2) f.holds

/-- A substitution leaves every fact's other variables alone. -/
def factsAvoid (facts : List Fact) (σ : List (Nat × E)) : Bool :=
  σ.all fun p => facts.all fun f => f.keys.contains p.1 || !occC p.1 f.holds

def baseHyps (facts : List Fact) (n : CNode) : List C := n.hyps ++ cycInsts facts n.insts
def useHyps (nodes : List CNode) (us : List Use) : List C :=
  us.filterMap fun u => nodes[u.node]?.map fun m => .or (.not u.guard) (substC u.σ m.concl)
def mainGoal (facts : List Fact) (nodes : List CNode) (n : CNode) : List C :=
  baseHyps facts n ++ useHyps nodes n.uses ++ [.not n.concl]
def premiseGoal (facts : List Fact) (n : CNode) (u : Use) (c : C) : List C :=
  baseHyps facts n ++ [u.guard, .not (substC u.σ c)]
def descentGoal (facts : List Fact) (n : CNode) (u : Use) (m : CNode) : List C :=
  baseHyps facts n ++ [u.guard, .not (lexLtC (m.rank.map (substE u.σ)) n.rank)]

def checkUse (facts : List Fact) (nodes : List CNode) (n : CNode) (u : Use) : Bool :=
  match nodes[u.node]? with
  | none => false
  | some m => m.rank.length == n.rank.length && factsAvoid facts u.σ && m.hyps.length == u.premises.length
      && (m.hyps.zip u.premises).all (fun p => checkGoal ⟨p.2.1, premiseGoal facts n u p.1⟩ p.2.2)
      && checkGoal ⟨u.descent.1, descentGoal facts n u m⟩ u.descent.2

def checkCyclic (facts : List Fact) (nodes : List CNode) : Bool :=
  nodes.all fun n => checkGoal ⟨n.main.1, mainGoal facts nodes n⟩ n.main.2 && n.uses.all (checkUse facts nodes n)

section
variable {env : Nat → Nat} {maps : Nat → Nat → Nat}

theorem lexLtC_sound : ∀ (as bs : List E), as.length = bs.length → evalC env maps (lexLtC as bs) = true →
    lexLt (as.map (evalE env maps)) (bs.map (evalE env maps))
  | [], [], _, h => by simp [lexLtC, falseC, evalC, evalE] at h
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | a :: as, b :: bs, hl, h => by
    simp only [lexLtC, evalC, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.map_cons, lexLt, List.length_map]
    refine ⟨by simpa using hl, ?_⟩
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, lexLtC_sound as bs (by simpa using hl) h2⟩

theorem lex_acc_cons (n : Nat) (ihn : ∀ l : List Nat, l.length = n → Acc lexLt l) :
    ∀ a (as : List Nat), as.length = n → Acc lexLt (a :: as) := by
  intro a
  refine (Nat.lt_wfRel.wf).induction (C := fun a => ∀ (as : List Nat), as.length = n → Acc lexLt (a :: as)) a ?_
  intro a iha
  · intro as has
    have hacc := ihn as has
    revert has
    induction hacc with
    | intro as _ ihas =>
      intro has
      constructor
      intro w hw
      cases w with
      | nil => simp [lexLt] at hw
      | cons c cs =>
        simp only [lexLt] at hw
        obtain ⟨hlen, hc⟩ := hw
        rcases hc with hlt | ⟨rfl, hl⟩
        · exact iha c hlt cs (by omega)
        · exact ihas cs hl (by omega)

theorem lex_acc : ∀ n (l : List Nat), l.length = n → Acc lexLt l
  | 0, l, h => by
    cases l with
    | nil => exact ⟨_, fun w hw => by cases w <;> simp [lexLt] at hw⟩
    | cons _ _ => simp at h
  | n + 1, l, h => by
    cases l with
    | nil => simp at h
    | cons a as => exact lex_acc_cons n (lex_acc n) a as (by simpa using h)

theorem lexLt_wf : WellFounded lexLt := ⟨fun l => lex_acc l.length l rfl⟩

theorem cyc_zip_cover {α β : Type} : ∀ (as : List α) (bs : List β), as.length = bs.length → ∀ a ∈ as, ∃ b, (a, b) ∈ as.zip bs
  | [], _, _, a, ha => by simp at ha
  | _ :: _, [], h, _, _ => by simp at h
  | a :: as, b :: bs, h, x, hx => by
    simp only [List.mem_cons] at hx
    simp only [List.zip_cons_cons, List.mem_cons]
    rcases hx with rfl | hx
    · exact ⟨b, Or.inl rfl⟩
    · obtain ⟨b', hb'⟩ := cyc_zip_cover as bs (by simpa using h) x hx
      exact ⟨b', Or.inr hb'⟩

theorem zip_keys {keys : List Nat} {ts : List E} {i : Nat} (h : i ∈ (keys.zip ts).map (·.1)) : i ∈ keys := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  exact (List.of_mem_zip hp).1

theorem inst_holds {facts : List Fact} (hF : FactsHold facts env maps) (insts : List (Nat × List E)) :
    ∀ c ∈ cycInsts facts insts, evalC env maps c = true := by
  intro c hc
  simp only [cycInsts, List.mem_filterMap, Option.map_eq_some_iff] at hc
  obtain ⟨p, _, f, hf, rfl⟩ := hc
  rw [subst_evalC]
  have he : applyS (f.keys.zip p.2) env maps = override f.keys (applyS (f.keys.zip p.2) env maps) env := by
    funext i
    simp only [override]
    split
    · rfl
    · rename_i hi
      exact applyS_other (fun h => hi (List.contains_iff_mem.mpr (zip_keys h))) env maps
  rw [he]
  exact hF f (List.mem_of_getElem? hf) _

theorem facts_after {facts : List Fact} {σ : List (Nat × E)} (hA : factsAvoid facts σ = true)
    (hF : FactsHold facts env maps) : FactsHold facts (applyS σ env maps) maps := by
  intro f hf vals
  rw [congrC (override f.keys vals (applyS σ env maps)) (override f.keys vals env) maps f.holds ?_]
  · exact hF f hf vals
  · intro i hi
    simp only [override]
    split
    · rfl
    · rename_i hk
      cases ha : assoc σ i with
      | none => simp only [applyS, ha]
      | some e =>
        exfalso
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (assoc_mem ha)
        simp only [factsAvoid, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hA
        rcases hA p hp f hf with h | h
        · exact hk h
        · simp [h] at hi

theorem cyc_base {facts : List Fact} {n : CNode} (hF : FactsHold facts env maps)
    (hH : ∀ c ∈ n.hyps, evalC env maps c = true) : ∀ c ∈ baseHyps facts n, evalC env maps c = true := by
  intro c hc
  simp only [baseHyps, List.mem_append] at hc
  rcases hc with hc | hc
  · exact hH c hc
  · exact inst_holds hF n.insts c hc
end

/-- Every node of an accepted cyclic proof holds: for any maps, at every environment that meets the facts and the
node's hypotheses, its conclusion holds. -/
theorem cyclic_sound (facts : List Fact) (nodes : List CNode) (h : checkCyclic facts nodes = true) (maps : Nat → Nat → Nat) :
    ∀ env, FactsHold facts env maps → ∀ n ∈ nodes, (∀ c ∈ n.hyps, evalC env maps c = true) → evalC env maps n.concl = true := by
  have key : ∀ v : List Nat, ∀ n ∈ nodes, ∀ env, n.rank.map (evalE env maps) = v → FactsHold facts env maps →
      (∀ c ∈ n.hyps, evalC env maps c = true) → evalC env maps n.concl = true := by
    intro v
    refine lexLt_wf.induction (C := fun v => ∀ n ∈ nodes, ∀ env, n.rank.map (evalE env maps) = v → FactsHold facts env maps →
      (∀ c ∈ n.hyps, evalC env maps c = true) → evalC env maps n.concl = true) v ?_
    intro v ih n hn env hv hF hH
    have hc := (List.all_eq_true.mp h) n hn
    simp only [Bool.and_eq_true] at hc
    obtain ⟨hmain, huses⟩ := hc
    have hbase := cyc_base hF hH
    have huse : ∀ c ∈ useHyps nodes n.uses, evalC env maps c = true := by
      intro c hc
      simp only [useHyps, List.mem_filterMap, Option.map_eq_some_iff] at hc
      obtain ⟨u, hu, m, hm, rfl⟩ := hc
      have hcu := (List.all_eq_true.mp huses) u hu
      simp only [checkUse, hm, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcu
      obtain ⟨⟨⟨⟨hlen, hav⟩, hpl⟩, hprem⟩, hdesc⟩ := hcu
      simp only [evalC, Bool.or_eq_true, Bool.not_eq_true']
      by_cases hg : evalC env maps u.guard = true
      · right
        rw [subst_evalC]
        have hprem' : ∀ c ∈ m.hyps, evalC (applyS u.σ env maps) maps c = true := by
          intro c hc
          obtain ⟨p, hp⟩ := cyc_zip_cover m.hyps u.premises hpl c hc
          have hs := sound ⟨p.1, premiseGoal facts n u c⟩ p.2 (hprem (c, p) hp) env maps
          rw [← subst_evalC]
          apply Decidable.byContradiction
          intro hf
          apply hs
          intro c' hc'
          simp only [premiseGoal, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc'
          rcases hc' with hc' | rfl | rfl
          · exact hbase c' hc'
          · exact hg
          · simp only [evalC, Bool.not_eq_true']; simpa using hf
        have hdl : evalC env maps (lexLtC (m.rank.map (substE u.σ)) n.rank) = true := by
          have hs := sound ⟨u.descent.1, descentGoal facts n u m⟩ u.descent.2 hdesc env maps
          apply Decidable.byContradiction
          intro hf
          apply hs
          intro c' hc'
          simp only [descentGoal, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc'
          rcases hc' with hc' | rfl | rfl
          · exact hbase c' hc'
          · exact hg
          · simp only [evalC, Bool.not_eq_true']; simpa using hf
        have hlx := lexLtC_sound (env := env) (maps := maps) _ _ (by simpa using hlen) hdl
        have hrank : (m.rank.map (substE u.σ)).map (evalE env maps) = m.rank.map (evalE (applyS u.σ env maps) maps) := by
          simp only [List.map_map]
          exact List.map_congr_left (fun e _ => by simp [Function.comp, subst_evalE])
        rw [hrank, hv] at hlx
        exact ih _ hlx m (List.mem_of_getElem? hm) (applyS u.σ env maps) rfl (facts_after hav hF) hprem'
      · left
        simpa using hg
    have hs := sound ⟨n.main.1, mainGoal facts nodes n⟩ n.main.2 hmain env maps
    apply Decidable.byContradiction
    intro hf
    apply hs
    intro c hc
    simp only [mainGoal, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (hc | hc) | rfl
    · exact hbase c hc
    · exact huse c hc
    · simp only [evalC, Bool.not_eq_true']; simpa using hf
  intro env hF n hn hH
  exact key _ n hn env rfl hF hH

end Kern

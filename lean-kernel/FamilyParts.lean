import CountMachine
/-! One entry's check in pieces (research module, generated proofs' library; not part of the trusted files).
Every definition below is a restatement of a part of the existing check, and every theorem concludes the ORIGINAL
`cEntryCheckF` / `checkMCF` / `checkGoalFrames` / `checkTFrames` from the pieces. Only that direction is used. -/
open Kern Cert
namespace FamilyParts

/-- The subtree at an address, with the path extended by exactly the split conditions passed on the way. The walk
stops at the first leaf: an address longer than the branch names that leaf with its own path. -/
def subAt : Path → Tree → List Bool → Path × Tree
  | p, .split l y _, true :: bs => subAt ((l, true) :: p) y bs
  | p, .split l _ n, false :: bs => subAt ((l, false) :: p) n bs
  | p, t, _ => (p, t)

def checkAt (tab : List VDef) (hyps : List C) (lemmas : List CutLemma) (frames : List FrameCut) (monos : List MonoCut) (lins : List LinCut)
    (p : Path) (t : Tree) (a : List Bool) : Bool :=
  checkTFrames tab hyps lemmas frames monos lins (subAt p t a).1 (subAt p t a).2

theorem checkAt_nil (tab : List VDef) (hyps : List C) (lemmas : List CutLemma) (frames : List FrameCut) (monos : List MonoCut) (lins : List LinCut)
    (p : Path) (t : Tree) (h : checkAt tab hyps lemmas frames monos lins p t [] = true) :
    checkTFrames tab hyps lemmas frames monos lins p t = true := by
  cases t <;> simpa [checkAt, subAt] using h

/-- Both children of an address give the address. At a leaf either child is the leaf itself. -/
theorem checkAt_split (tab : List VDef) (hyps : List C) (lemmas : List CutLemma) (frames : List FrameCut) (monos : List MonoCut) (lins : List LinCut) :
    ∀ (a : List Bool) (p : Path) (t : Tree),
      checkAt tab hyps lemmas frames monos lins p t (a ++ [true]) = true →
      checkAt tab hyps lemmas frames monos lins p t (a ++ [false]) = true →
      checkAt tab hyps lemmas frames monos lins p t a = true := by
  intro a
  induction a with
  | nil =>
    intro p t h1 h0
    cases t with
    | split l y n =>
      simp only [checkAt, subAt, List.nil_append] at h1 h0 ⊢
      cases y <;> cases n <;> simp_all [checkTFrames, subAt]
    | leaf rows steps eqs prods => simpa [checkAt, subAt] using h1
    | leafAt rows steps eqs prods => simpa [checkAt, subAt] using h1
    | leafSq rows sqs steps eqs prods => simpa [checkAt, subAt] using h1
  | cons b a ih =>
    intro p t h1 h0
    cases t with
    | split l y n =>
      cases b with
      | true => exact ih ((l, true) :: p) y (by simpa [checkAt, subAt] using h1) (by simpa [checkAt, subAt] using h0)
      | false => exact ih ((l, false) :: p) n (by simpa [checkAt, subAt] using h1) (by simpa [checkAt, subAt] using h0)
    | leaf rows steps eqs prods => simpa [checkAt, subAt] using h1
    | leafAt rows steps eqs prods => simpa [checkAt, subAt] using h1
    | leafSq rows sqs steps eqs prods => simpa [checkAt, subAt] using h1

/-- The list after j chunks of c. -/
def dropN (c : Nat) : Nat → List α → List α
  | 0, l => l
  | j + 1, l => (dropN c j l).drop c

/-- A list's check from its first c elements and the rest: every element is in one of the two. -/
theorem all_split (p : α → Bool) (c : Nat) (l : List α) (h1 : (l.take c).all p = true) (h2 : (l.drop c).all p = true) : l.all p = true := by
  have h : (l.take c ++ l.drop c).all p = true := by rw [List.all_append, h1, h2]; rfl
  rwa [List.take_append_drop] at h

/-- The step goal the original check builds, handed to a condition q; false when the original has no goal. -/
def mcfWith (ds : List CDecl) (k : CCert) (q : Goal → List Count → Bool) : Bool :=
  match toCounts ds k.reads with
  | some cs => match countHyps cs k.insts with
    | some hs => q ⟨k.tab, (k.hyps ++ k.reads.map (readHyp ds) ++ pickHyps ds k.reads k.picks) ++ hs⟩ cs
    | none => false
  | none => false

/-- The original check's conditions outside the goal. -/
def mcfPre (hyps : List C) (ds : List CDecl) (k : CCert) : Bool :=
  namedIn hyps k.hyps hyps && ds.all (fun d => d.j != d.key && d.lo != d.key) && readsOk k.hyps ds k.reads
    && k.reads.all (fun r => k.insts.all (fun i => i.wit != r.1 && !occE i.wit r.2.2))
    && mcfWith ds k (fun _ cs => countedOkW cs k.insts)

/-- The goal check's conditions outside the frames and the tree. -/
def goalPre (lemmas : List CutLemma) (monos : List MonoCut) (lins : List LinCut) (g : Goal) (cs : List Count) : Bool :=
  wfTab 0 g.tab && lemmas.all (checkLemma g.tab g.hyps) && monos.all (monoOk cs) && lins.all (linOk cs)

theorem goal_of_parts (g : Goal) (cs : List Count) (t : Tree) (lemmas : List CutLemma) (frames : List FrameCut) (monos : List MonoCut) (lins : List LinCut)
    (h0 : goalPre lemmas monos lins g cs = true) (hf : frames.all (frameOk g.tab cs) = true)
    (ht : checkAt g.tab g.hyps lemmas frames monos lins [] t [] = true) :
    checkGoalFrames g cs t lemmas frames monos lins = true := by
  have ht' := checkAt_nil _ _ _ _ _ _ _ _ ht
  simp only [goalPre, Bool.and_eq_true] at h0
  simp only [checkGoalFrames, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h0.1.1.1, h0.1.1.2⟩, hf⟩, h0.1.2⟩, h0.2⟩, ht'⟩

theorem mcfWith_map1 (ds : List CDecl) (k : CCert) (q r : Goal → List Count → Bool)
    (h : ∀ g cs, q g cs = true → r g cs = true) (hq : mcfWith ds k q = true) : mcfWith ds k r = true := by
  unfold mcfWith at hq ⊢
  cases h1 : toCounts ds k.reads with
  | none => rw [h1] at hq; cases hq
  | some cs =>
    rw [h1] at hq; simp only at hq ⊢
    cases h2 : countHyps cs k.insts with
    | none => rw [h2] at hq; cases hq
    | some hs => rw [h2] at hq; exact h _ _ hq

theorem mcfWith_map2 (ds : List CDecl) (k : CCert) (q1 q2 r : Goal → List Count → Bool)
    (h : ∀ g cs, q1 g cs = true → q2 g cs = true → r g cs = true) (h1 : mcfWith ds k q1 = true) (h2 : mcfWith ds k q2 = true) : mcfWith ds k r = true := by
  unfold mcfWith at h1 h2 ⊢
  cases e1 : toCounts ds k.reads with
  | none => rw [e1] at h1; cases h1
  | some cs =>
    rw [e1] at h1 h2; simp only at h1 h2 ⊢
    cases e2 : countHyps cs k.insts with
    | none => rw [e2] at h1; cases h1
    | some hs => rw [e2] at h1 h2; exact h _ _ h1 h2

theorem mcfWith_map3 (ds : List CDecl) (k : CCert) (q1 q2 q3 r : Goal → List Count → Bool)
    (h : ∀ g cs, q1 g cs = true → q2 g cs = true → q3 g cs = true → r g cs = true)
    (h1 : mcfWith ds k q1 = true) (h2 : mcfWith ds k q2 = true) (h3 : mcfWith ds k q3 = true) : mcfWith ds k r = true := by
  unfold mcfWith at h1 h2 h3 ⊢
  cases e1 : toCounts ds k.reads with
  | none => rw [e1] at h1; cases h1
  | some cs =>
    rw [e1] at h1 h2 h3; simp only at h1 h2 h3 ⊢
    cases e2 : countHyps cs k.insts with
    | none => rw [e2] at h1; cases h1
    | some hs => rw [e2] at h1 h2 h3; exact h _ _ h1 h2 h3

/-- The original `checkMCF` from the conditions outside the goal and the goal check. -/
theorem checkMCF_of_parts (hyps : List C) (ds : List CDecl) (k : CCert) (frames : List FrameCut) (monos : List MonoCut) (lins : List LinCut)
    (hpre : mcfPre hyps ds k = true)
    (hgoal : mcfWith ds k (fun g cs => checkGoalFrames g cs k.tree k.lemmas frames monos lins) = true) :
    checkMCF hyps ds k frames monos lins = true := by
  unfold mcfPre at hpre
  unfold mcfWith at hpre hgoal
  unfold checkMCF checkCountedWF
  cases e1 : toCounts ds k.reads with
  | none => rw [e1] at hgoal; cases hgoal
  | some cs =>
    rw [e1] at hpre hgoal; simp only at hpre hgoal ⊢
    cases e2 : countHyps cs k.insts with
    | none => rw [e2] at hgoal; cases hgoal
    | some hs =>
      rw [e2] at hpre hgoal; simp only [Bool.and_eq_true] at hpre hgoal ⊢
      exact ⟨hpre.1, hpre.2, hgoal⟩

/-- The entry's conditions other than the step goal. -/
def entryRest (s : SMachine) (ds : List CDecl) (es : List SEntry) (ce : CEntryF) : Bool :=
  cEntryOk s ds es ce.e && witsOk s es ce.start && witsOk s es ce.step
    && checkMCF (cStartGoal s ds ce.e) (cStartDecls s ds) ce.start ce.startAux.frames ce.startAux.monos ce.startAux.lins

/-- The original `cEntryCheckF` from its pieces. -/
theorem entry_of_parts (s : SMachine) (ds : List CDecl) (es : List SEntry) (ce : CEntryF)
    (hrest : entryRest s ds es ce = true)
    (hstep : checkMCF (cStepGoal s ds es ce.e) (cStepDecls s ds) ce.step ce.stepAux.frames ce.stepAux.monos ce.stepAux.lins = true) :
    cEntryCheckF s ds es ce = true := by
  unfold entryRest at hrest
  unfold cEntryCheckF
  rw [hrest, hstep]; rfl

-- Both primary obligations may be partitioned; no monolithic INIT is hidden in entryRest.
def entryPre (s : SMachine) (ds : List CDecl) (es : List SEntry) (ce : CEntryF) : Bool :=
  cEntryOk s ds es ce.e && witsOk s es ce.start && witsOk s es ce.step

theorem entry_of_both (s : SMachine) (ds : List CDecl) (es : List SEntry) (ce : CEntryF)
    (hp : entryPre s ds es ce = true)
    (hstart : checkMCF (cStartGoal s ds ce.e) (cStartDecls s ds) ce.start ce.startAux.frames ce.startAux.monos ce.startAux.lins = true)
    (hstep : checkMCF (cStepGoal s ds es ce.e) (cStepDecls s ds) ce.step ce.stepAux.frames ce.stepAux.monos ce.stepAux.lins = true) :
    cEntryCheckF s ds es ce = true := by
  unfold entryPre at hp
  unfold cEntryCheckF
  rw [hp, hstart, hstep]
  rfl

end FamilyParts
#print axioms FamilyParts.entry_of_both
#print axioms FamilyParts.checkAt_nil
#print axioms FamilyParts.checkAt_split
#print axioms FamilyParts.all_split
#print axioms FamilyParts.goal_of_parts
#print axioms FamilyParts.mcfWith_map1
#print axioms FamilyParts.mcfWith_map2
#print axioms FamilyParts.mcfWith_map3
#print axioms FamilyParts.checkMCF_of_parts
#print axioms FamilyParts.entry_of_parts

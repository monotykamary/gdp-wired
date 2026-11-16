import CountedSourceBridge

namespace Kern

/-- One-way operational inclusion. None of these premises is a proof-search verdict. -/
structure SourceInclusion (s t : SMachine) : Prop where
  inputs : s.f.m.inputs = t.f.m.inputs
  carried : s.carried = t.carried
  initial : s.f.m.init = t.f.m.init
  startMaps : ∀ M, StartMaps s.f.m M → StartMaps t.f.m M
  pre : ∀ ρ M, evalC ρ M s.f.m.pre = true → evalC ρ M t.f.m.pre = true
  facts : ∀ ρ M, (∀ l ∈ s.facts, l.Holds ρ M) → ∀ l ∈ t.facts, l.Holds ρ M
  pfacts : ∀ ρ M, s.PFacts ρ M → t.PFacts ρ M
  admission : ∀ ρ M ι κ,
    evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume = true →
    evalC (sView t ρ M ι κ).1 (sView t ρ M ι κ).2 t.f.m.assume = true
  next : ∀ ρ M ι κ,
    evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume = true →
    sNext s ρ M ι κ = sNext t ρ M ι κ

theorem SourceInclusion.creach {s t : SMachine} (h : SourceInclusion s t) (ds : List CDecl) :
    ∀ {ρ M}, CReach s ds ρ M → CReach t ds ρ M := by
  intro ρ M hr
  induction hr with
  | start ρ M hm hp hf hpf =>
      rw [h.initial]
      exact .start ρ M (h.startMaps M hm) (h.pre ρ M hp) (h.facts ρ M hf) (h.pfacts ρ M hpf)
  | step ρ M ι κ hr hg ha ih =>
      have hc : withCarried s M κ = withCarried t M κ := by
        funext mp
        simp only [withCarried, h.carried]
      have hg' : GHolds ds (withInputs t.f.m.inputs ρ ι) (withCarried t M κ) := by
        rw [← h.inputs, ← hc]
        exact hg
      have out := CReach.step ρ M ι κ ih hg' (h.admission ρ M ι κ ha)
      rw [h.next ρ M ι κ ha]
      exact out

theorem SourceInclusion.sreach {s t : SMachine} (h : SourceInclusion s t) :
    ∀ {ρ M}, SReach s ρ M → SReach t ρ M := by
  intro ρ M hr
  induction hr with
  | start ρ M hm hp hf hpf =>
      rw [h.initial]
      exact .start ρ M (h.startMaps M hm) (h.pre ρ M hp) (h.facts ρ M hf) (h.pfacts ρ M hpf)
  | step ρ M ι κ hr ha ih =>
      have out := SReach.step ρ M ι κ ih (h.admission ρ M ι κ ha)
      rw [h.next ρ M ι κ ha]
      exact out

/-- A checked implication between public entries, including all bound keys. -/
def SourceLawImplication (strong weak : SEntry) : Prop :=
  ∀ ρ M, strong.Holds ρ M → weak.Holds ρ M

theorem sourceLawImplication_of_pointwise (strong weak : SEntry)
    (hk : strong.law.key = weak.law.key) (hks : strong.keys2 = weak.keys2)
    (hp : ∀ ρ M, evalC ρ M strong.law.holds = true → evalC ρ M weak.law.holds = true) :
    SourceLawImplication strong weak := by
  have atom : ∀ ρ M, strong.law.Holds ρ M → weak.law.Holds ρ M := by
    intro ρ M ha
    unfold MLaw.Holds at ha ⊢
    rw [← hk]
    cases he : strong.law.key with
    | none => simp only [he] at ha ⊢; exact hp ρ M ha
    | some k => simp only [he] at ha ⊢; intro v; exact hp (upd ρ k v) M (ha v)
  intro ρ M hs
  unfold SEntry.Holds at hs ⊢
  rw [← hks]
  generalize strong.keys2 = ks at hs ⊢
  induction ks generalizing ρ with
  | nil => exact atom ρ M hs
  | cons k ks ih => intro v; exact ih (upd ρ k v) (hs v)

/-- Compose operational inclusion and semantic law weakening. Count projection
    and alpha transport can be applied before/after this theorem independently. -/
theorem sourceLaw_via_inclusion {s t : SMachine} (ds : List CDecl)
    (h : SourceInclusion s t) (strong weak : SEntry)
    (hw : SourceLawImplication strong weak)
    (ht : ∀ ρ M, CReach t ds ρ M → strong.Holds ρ (withCnt ds ρ M)) :
    ∀ ρ M, CReach s ds ρ M → weak.Holds ρ (withCnt ds ρ M) := by
  intro ρ M hr
  exact hw ρ _ (ht ρ M (h.creach ds hr))

/-- Uncounted counterpart, for composition with separately checked ghost/witness projection. -/
theorem sourceLaw_via_sinclusion {s t : SMachine}
    (h : SourceInclusion s t) (strong weak : SEntry)
    (hw : SourceLawImplication strong weak)
    (ht : ∀ ρ M, SReach t ρ M → strong.Holds ρ M) :
    ∀ ρ M, SReach s ρ M → weak.Holds ρ M := by
  intro ρ M hr
  exact hw ρ M (ht ρ M (h.sreach hr))

end Kern
#print axioms Kern.sourceLaw_via_sinclusion
#print axioms Kern.SourceInclusion.creach
#print axioms Kern.SourceInclusion.sreach
#print axioms Kern.sourceLawImplication_of_pointwise
#print axioms Kern.sourceLaw_via_inclusion

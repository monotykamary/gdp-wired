import CountMachine
import GhostMap

namespace Kern

/-- Agreement of maps observable by the source. -/
def PublicMaps (fresh : List Nat) (M N : Nat → Nat → Nat) : Prop :=
  ∀ mp, mp ∉ fresh → M mp = N mp

/-- The exact semantic obligation remaining for a source step: a producer request
    can be chosen which satisfies its counts, preserves the assumption, and has
    the same scalar successor and public map successor. No source assumption is
    weakened, and this does not assert any freshness property. -/
def CountedStepExtension (s : SMachine) (source producer : List CDecl)
    (fresh : List Nat) : Prop :=
  ∀ ρ M N ι κ, PublicMaps fresh N M →
    GHolds source (withInputs s.f.m.inputs ρ ι) (withCarried s M κ) →
    evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume = true →
    ∃ κ', GHolds producer (withInputs s.f.m.inputs ρ ι) (withCarried s N κ') ∧
      evalC (sView s ρ N ι κ').1 (sView s ρ N ι κ').2 s.f.m.assume = true ∧
      (sNext s ρ N ι κ').1 = (sNext s ρ M ι κ).1 ∧
      PublicMaps fresh (sNext s ρ N ι κ').2 (sNext s ρ M ι κ).2

/-- A simulation with an explicit step-extension premise; start is shared
    exactly, whereas subsequent map states need only agree publicly. -/
theorem counted_source_reach {s : SMachine} {source producer : List CDecl}
    {fresh : List Nat} (hstep : CountedStepExtension s source producer fresh) :
    ∀ {ρ M}, CReach s source ρ M →
      ∃ N, CReach s producer ρ N ∧ PublicMaps fresh N M := by
  intro ρ M hr
  induction hr with
  | start ρ M hM hp hf hpf =>
      exact ⟨M, CReach.start ρ M hM hp hf hpf, fun _ _ => rfl⟩
  | step ρ M ι κ hr hg ha ih =>
      obtain ⟨N, hn, hag⟩ := ih
      obtain ⟨κ', hg', ha', hs, hm⟩ := hstep ρ M N ι κ hag hg ha
      have hnext := CReach.step ρ N ι κ' hn hg' ha'
      rw [hs] at hnext
      exact ⟨_, hnext, hm⟩

/-- Producer counts can always be constructed while keeping every non-count
    request map unchanged. This is the kernel's checked count construction. -/
theorem producer_request_counts (s : SMachine) (ds : List CDecl)
    (hd : cDistinct (cMaps ds) = true)
    (hc : ∀ d ∈ ds, d.mp ∈ s.carried)
    (hav : ∀ d ∈ ds, avoidsMapsE (cMaps ds) d.below = true ∧ avoidsMapsE (cMaps ds) d.body = true)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    ∃ κ', (∀ mp, mp ∉ cMaps ds → withCarried s M κ' mp = withCarried s M κ mp) ∧
      GHolds ds (withInputs s.f.m.inputs ρ ι) (withCarried s M κ') :=
  counts_exist s ds hd hc hav ρ M ι κ

/-- Construct producer request counts without changing any public request map.
    Public producer declarations must already be source declarations; all extra
    maps are fresh, and freshness names only producer count maps. -/
theorem producer_request_public (s : SMachine) (source producer : List CDecl)
    (fresh : List Nat) (hd : cDistinct (cMaps producer) = true)
    (hc : ∀ d ∈ producer, d.mp ∈ s.carried)
    (hav : ∀ d ∈ producer, avoidsMapsE (cMaps producer) d.below = true ∧ avoidsMapsE (cMaps producer) d.body = true)
    (hkey : ∀ d ∈ producer, occE d.key d.below = false)
    (hsub : ∀ mp ∈ fresh, mp ∈ cMaps producer)
    (hpublic : ∀ d ∈ producer, d.mp ∉ fresh → d ∈ source)
    (ρ : Nat → Nat) (M N : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (hag : PublicMaps fresh N M)
    (hs : GHolds source (withInputs s.f.m.inputs ρ ι) (withCarried s M κ)) :
    ∃ κ', GHolds producer (withInputs s.f.m.inputs ρ ι) (withCarried s N κ') ∧
      PublicMaps fresh (withCarried s N κ') (withCarried s M κ) := by
  obtain ⟨κ', hoff, hg⟩ := counts_exist s producer hd hc hav ρ N ι κ
  have hbase : ∀ mp, mp ∉ cMaps producer →
      withCarried s N κ' mp = withCarried s M κ mp := by
    intro mp hm
    rw [hoff mp hm]
    unfold withCarried
    split
    · rfl
    · exact hag mp (fun hf => hm (hsub mp hf))
  refine ⟨κ', hg, ?_⟩
  intro mp hm
  by_cases hp : mp ∈ cMaps producer
  · obtain ⟨d, hdp, heq⟩ := List.mem_map.mp hp
    subst mp
    funext x
    rw [hg d hdp x, hs d (hpublic d hdp hm) x]
    apply cntOf_congr d (hkey d hdp)
    · intro i _ _ _ _; rfl
    · intro m hor
      apply hbase m
      rcases hor with hb | hb
      · exact avoidsMapsE_occ (hav d hdp).1 hb
      · exact avoidsMapsE_occ (hav d hdp).2 hb
  · exact hbase mp hp

/-- The two interpretations of public count maps agree, including original
    source counts, when added declarations are confined to fresh maps. -/
theorem withCnt_public (source producer : List CDecl) (fresh : List Nat)
    (hsd : cDistinct (cMaps source) = true)
    (hpd : cDistinct (cMaps producer) = true)
    (hsource : ∀ d ∈ source, d ∈ producer)
    (hpublic : ∀ d ∈ producer, d.mp ∉ fresh → d ∈ source)
    (hkey : ∀ d ∈ producer, occE d.key d.below = false)
    (hav : ∀ d ∈ producer, avoidsMapsE fresh d.below = true ∧ avoidsMapsE fresh d.body = true)
    (ρ : Nat → Nat) (M N : Nat → Nat → Nat) (hag : PublicMaps fresh N M) :
    PublicMaps fresh (withCnt producer ρ N) (withCnt source ρ M) := by
  intro mp hm
  by_cases hp : mp ∈ cMaps producer
  · obtain ⟨d, hdp, heq⟩ := List.mem_map.mp hp
    subst mp
    rw [withCnt_at hpd hdp, withCnt_at hsd (hpublic d hdp hm)]
    funext x
    apply cntOf_congr d (hkey d hdp)
    · intro i _ _ _ _; rfl
    · intro m hor
      apply hag m
      rcases hor with hb | hb
      · exact avoidsMapsE_occ (hav d hdp).1 hb
      · exact avoidsMapsE_occ (hav d hdp).2 hb
  · have hs : mp ∉ cMaps source := by
      intro hs
      obtain ⟨d, hd, heq⟩ := List.mem_map.mp hs
      apply hp
      exact List.mem_map.mpr ⟨d, hsource d hd, heq⟩
    rw [withCnt_other hp, withCnt_other hs]
    exact hag mp hm

/-- Semantic noninterference of the machine with respect to fresh maps. This
    concerns only the machine, not count declarations or reachable states. -/
def MachinePublicStep (s : SMachine) (fresh : List Nat) : Prop :=
  ∀ ρ M N ι κ κ', PublicMaps fresh N M →
    PublicMaps fresh (withCarried s N κ') (withCarried s M κ) →
    evalC (sView s ρ N ι κ').1 (sView s ρ N ι κ').2 s.f.m.assume =
      evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume ∧
    (sNext s ρ N ι κ').1 = (sNext s ρ M ι κ).1 ∧
    PublicMaps fresh (sNext s ρ N ι κ').2 (sNext s ρ M ι κ).2

/-- Reduce step extension to count-declaration conditions and the machine's
    independently stated public-map noninterference. -/
theorem counted_step_of_public (s : SMachine) (source producer : List CDecl)
    (fresh : List Nat) (hd : cDistinct (cMaps producer) = true)
    (hc : ∀ d ∈ producer, d.mp ∈ s.carried)
    (hav : ∀ d ∈ producer, avoidsMapsE (cMaps producer) d.below = true ∧ avoidsMapsE (cMaps producer) d.body = true)
    (hkey : ∀ d ∈ producer, occE d.key d.below = false)
    (hsub : ∀ mp ∈ fresh, mp ∈ cMaps producer)
    (hpublic : ∀ d ∈ producer, d.mp ∉ fresh → d ∈ source)
    (hmachine : MachinePublicStep s fresh) : CountedStepExtension s source producer fresh := by
  intro ρ M N ι κ hag hg ha
  obtain ⟨κ', hc', hm⟩ := producer_request_public s source producer fresh hd hc hav hkey hsub hpublic ρ M N ι κ hag hg
  obtain ⟨he, hn, hw⟩ := hmachine ρ M N ι κ κ' hag hm
  exact ⟨κ', hc', he.trans ha, hn, hw⟩

/-- When the interpreted maps agree publicly, a source law avoiding the fresh
    maps transfers without identifying the raw maps or the count declarations. -/
theorem source_law_transfer (e : SEntry) (fresh : List Nat)
    (havoid : avoidsMaps fresh e.law.holds = true) {ρ : Nat → Nat}
    {M N : Nat → Nat → Nat} (hag : PublicMaps fresh N M)
    (h : e.Holds ρ N) : e.Holds ρ M := by
  exact holdsOver_maps havoid (fun mp hm => (hag mp hm).symm) e.keys2 ρ h

end Kern

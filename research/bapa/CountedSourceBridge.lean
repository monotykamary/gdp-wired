import CountedNoninterference

namespace Kern

/-- Extending carried names is idempotent when supplied the original request view. -/
theorem bapa_withCarried_from_view (s : SMachine) (extra : List Nat)
    (M κ : Nat → Nat → Nat) :
    withCarried {s with carried := s.carried ++ extra} M (withCarried s M κ) = withCarried s M κ := by
  funext mp
  simp only [withCarried, List.contains_append]
  cases hs : s.carried.contains mp <;> cases he : extra.contains mp <;> simp [hs, he]

/-- A source run lifts to the same machine with additional carried count maps.
Only public-map agreement is asserted: fresh maps are not equated to arbitrary
source maps. Every premise below is about finite declarations or source syntax. -/
theorem bapa_counted_source_reach (s : SMachine) (source producer : List CDecl)
    (fresh extra : List Nat)
    (hd : cDistinct (cMaps producer) = true)
    (hc : ∀ d ∈ producer, d.mp ∈ s.carried ++ extra)
    (hav : ∀ d ∈ producer, avoidsMapsE (cMaps producer) d.below = true ∧ avoidsMapsE (cMaps producer) d.body = true)
    (hkey : ∀ d ∈ producer, occE d.key d.below = false)
    (hsub : ∀ mp ∈ fresh, mp ∈ cMaps producer)
    (hpublic : ∀ d ∈ producer, d.mp ∉ fresh → d ∈ source)
    (havoid : StepAvoids s fresh) :
    ∀ {ρ M}, CReach s source ρ M →
      ∃ N, CReach {s with carried := s.carried ++ extra} producer ρ N ∧ PublicMaps fresh N M := by
  let t : SMachine := {s with carried := s.carried ++ extra}
  intro ρ M hr
  induction hr with
  | start ρ M hM hp hf hpf =>
      exact ⟨M, CReach.start ρ M hM hp hf hpf, fun _ _ => rfl⟩
  | step ρ M ι κ hr hg ha ih =>
      obtain ⟨N, hn, hag⟩ := ih
      let κ0 := withCarried s M κ
      have hv0 : withCarried t M κ0 = withCarried s M κ := bapa_withCarried_from_view s extra M κ
      have hg0 : GHolds source (withInputs t.f.m.inputs ρ ι) (withCarried t M κ0) := by
        rw [hv0]
        exact hg
      obtain ⟨κ', hg', hv⟩ := producer_request_public t source producer fresh hd hc hav hkey hsub hpublic ρ M N ι κ0 hag hg0
      have hv' : PublicMaps fresh (withCarried t N κ') (withCarried s M κ) := by
        rw [hv0] at hv
        exact hv
      obtain ⟨ha', hs', hm'⟩ := step_avoids_two s fresh extra havoid ρ M N ι κ κ' hv'
      have hnext := CReach.step ρ N ι κ' hn hg' (ha'.trans ha)
      rw [hs'] at hnext
      exact ⟨_, hnext, hm'⟩

private theorem bapa_avoidsMapsE_mono {small large : List Nat} {e : E}
    (hs : ∀ mp ∈ small, mp ∈ large) (h : avoidsMapsE large e = true) : avoidsMapsE small e = true := by
  simp only [avoidsMapsE, List.all_eq_true] at h ⊢
  intro mp hm
  exact h mp (hs mp hm)

/-- The retained counted theorem transfers to the source count interpretation.
This theorem has no assumed operational simulation: it is derived above from
finite source noninterference and finite count-declaration premises. -/
theorem bapa_counted_source_law (s : SMachine) (source producer : List CDecl)
    (fresh extra : List Nat) (e : SEntry)
    (hsd : cDistinct (cMaps source) = true)
    (hd : cDistinct (cMaps producer) = true)
    (hc : ∀ d ∈ producer, d.mp ∈ s.carried ++ extra)
    (hav : ∀ d ∈ producer, avoidsMapsE (cMaps producer) d.below = true ∧ avoidsMapsE (cMaps producer) d.body = true)
    (hkey : ∀ d ∈ producer, occE d.key d.below = false)
    (hsub : ∀ mp ∈ fresh, mp ∈ cMaps producer)
    (hsource : ∀ d ∈ source, d ∈ producer)
    (hpublic : ∀ d ∈ producer, d.mp ∉ fresh → d ∈ source)
    (havoid : StepAvoids s fresh)
    (hlaw : avoidsMaps fresh e.law.holds = true)
    (hproof : ∀ ρ M, CReach {s with carried := s.carried ++ extra} producer ρ M → e.Holds ρ (withCnt producer ρ M)) :
    ∀ ρ M, CReach s source ρ M → e.Holds ρ (withCnt source ρ M) := by
  intro ρ M hr
  obtain ⟨N, hn, hag⟩ := bapa_counted_source_reach s source producer fresh extra hd hc hav hkey hsub hpublic havoid hr
  have hav' : ∀ d ∈ producer, avoidsMapsE fresh d.below = true ∧ avoidsMapsE fresh d.body = true := by
    intro d hm
    exact ⟨bapa_avoidsMapsE_mono hsub (hav d hm).1, bapa_avoidsMapsE_mono hsub (hav d hm).2⟩
  have hi := withCnt_public source producer fresh hsd hd hsource hpublic hkey hav' ρ M N hag
  exact source_law_transfer e fresh hlaw hi (hproof ρ N hn)

end Kern

#print axioms Kern.bapa_counted_source_reach
#print axioms Kern.bapa_counted_source_law

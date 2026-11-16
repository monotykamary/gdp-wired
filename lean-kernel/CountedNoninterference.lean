import CountedSourceProjection

namespace Kern
open Classical

/-- Finite syntactic read footprint of a step. -/
def StepAvoids (s : SMachine) (fresh : List Nat) : Prop :=
  avoidsMaps fresh s.f.m.assume = true ∧
  (∀ p ∈ s.f.flags, avoidsMaps fresh p.2 = true) ∧
  (∀ q ∈ s.qflags, avoidsMaps fresh q.2.2 = true) ∧
  (∀ p ∈ s.f.m.step, avoidsMapsE fresh p.2 = true) ∧
  (∀ w ∈ s.f.m.writes, avoidsMapsE fresh w.2.1 = true ∧ avoidsMapsE fresh w.2.2 = true) ∧
  (∀ w ∈ s.every, avoidsMapsE fresh w.2.2 = true)

 /-- Executable finite check suitable for generated `by decide` certificates. -/
def stepAvoidsCheck (s : SMachine) (fresh : List Nat) : Bool :=
  avoidsMaps fresh s.f.m.assume &&
  s.f.flags.all (fun p => avoidsMaps fresh p.2) &&
  s.qflags.all (fun q => avoidsMaps fresh q.2.2) &&
  s.f.m.step.all (fun p => avoidsMapsE fresh p.2) &&
  s.f.m.writes.all (fun w => avoidsMapsE fresh w.2.1 && avoidsMapsE fresh w.2.2) &&
  s.every.all (fun w => avoidsMapsE fresh w.2.2)

theorem stepAvoids_of_check (s : SMachine) (fresh : List Nat)
    (h : stepAvoidsCheck s fresh = true) : StepAvoids s fresh := by
  simp only [stepAvoidsCheck, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- Identical machine except for request-carried map names. Agreement of its
request views suffices even when the carried lists differ on fresh names. -/
theorem step_avoids_two (s : SMachine) (fresh extra : List Nat)
    (h : StepAvoids s fresh) :
    ∀ ρ M N ι κ κ',
    PublicMaps fresh (withCarried {s with carried := s.carried ++ extra} N κ') (withCarried s M κ) →
    evalC (sView {s with carried := s.carried ++ extra} ρ N ι κ').1 (sView {s with carried := s.carried ++ extra} ρ N ι κ').2 s.f.m.assume =
      evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume ∧
    (sNext {s with carried := s.carried ++ extra} ρ N ι κ').1 = (sNext s ρ M ι κ).1 ∧
    PublicMaps fresh (sNext {s with carried := s.carried ++ extra} ρ N ι κ').2 (sNext s ρ M ι κ).2 := by
  intro ρ M N ι κ κ' hN
  obtain ⟨ha, hf, hq, hs, hw, he⟩ := h
  let t : SMachine := {s with carried := s.carried ++ extra}
  let X := withInputs s.f.m.inputs ρ ι
  let A := withCarried t N κ'
  let B := withCarried s M κ
  have hQ : decideQ t X A = decideQ s X B := by
    funext v
    rw [decideQ_of, decideQ_of]
    change (match lookup (fun q => q.1 == v) s.qflags with
      | some q => if ∀ k, holdsC (atKeys X q.2.1 k) A q.2.2 then 1 else 0
      | none => X v) = _
    cases hl : lookup (fun q => q.1 == v) s.qflags with
    | some q =>
      exact ite_all_congr (fun _ _ _ => rfl) (fun mp hm => hN mp (avoidsMaps_occ (hq q (lookup_some hl).1) hm))
    | none => rfl
  have hD : decideFlags s.f.flags (decideQ t X A) A = decideFlags s.f.flags (decideQ s X B) B := by
    apply funext; intro i
    have hd := decide_apart (V := []) (MS := fresh) (fun p hp => by simpa [apartC, avoids] using hf p hp)
      (X := decideQ t X A) (X' := decideQ s X B) (N := A) (N' := B)
      (fun i _ => congrFun hQ i) hN
    exact hd i (by simp)
  have hc {c : C} (havoid : avoidsMaps fresh c = true) :
      evalC (decideFlags s.f.flags (decideQ t X A) A) A c =
      evalC (decideFlags s.f.flags (decideQ s X B) B) B c := by
    rw [hD]; exact congrMC _ _ _ c (fun mp hm => hN mp (avoidsMaps_occ havoid hm))
  have hx {e : E} (havoid : avoidsMapsE fresh e = true) :
      evalE (decideFlags s.f.flags (decideQ t X A) A) A e =
      evalE (decideFlags s.f.flags (decideQ s X B) B) B e := by
    rw [hD]; exact congrME _ _ _ e (fun mp hm => hN mp (avoidsMapsE_occ havoid hm))
  refine ⟨hc ha, ?_, ?_⟩
  · funext i
    simp only [sNext, sView, applyS]
    cases hst : assoc s.f.m.step i with
    | none => exact congrFun hD i
    | some e =>
      have hm : (i, e) ∈ s.f.m.step := by
        simp only [assoc, Option.map_eq_some_iff] at hst
        obtain ⟨q, hq', rfl⟩ := hst
        obtain ⟨hqm, hqv⟩ := lookup_some hq'
        simp only [beq_iff_eq] at hqv
        rw [← hqv]; exact hqm
      exact hx (hs (i,e) hm)
  · intro mp hmp
    funext key
    simp only [sNext, sView, everyMaps]
    change (match lookup (fun w => w.1 == mp) s.every with
      | some w => evalE (upd _ w.2.1 key) A w.2.2
      | none => writeMaps s.f.m.writes _ A mp key) = _
    cases hl : lookup (fun w => w.1 == mp) s.every with
    | some w =>
      rw [hD]
      exact congrME _ _ _ _ (fun m hm => hN m (avoidsMapsE_occ (he w (lookup_some hl).1) hm))
    | none =>
      simp only [writeMaps]
      cases hl2 : lookup (fun w => w.1 == mp) s.f.m.writes with
      | none => exact congrFun (hN mp hmp) key
      | some w =>
        obtain ⟨h1, h2⟩ := hw w (lookup_some hl2).1
        dsimp only
        have hn : A mp = B mp := hN mp hmp
        rw [hx h1, hx h2, hn]

/-- The same-machine public-step property follows from finite syntax alone. -/
theorem step_avoids_public (s : SMachine) (fresh : List Nat)
    (h : StepAvoids s fresh) : MachinePublicStep s fresh := by
  intro ρ M N ι κ κ' _ hN
  have ht : ({s with carried := s.carried ++ []} : SMachine) = s := by cases s; simp
  have hh := step_avoids_two s fresh [] h
  rw [ht] at hh
  exact hh ρ M N ι κ κ' hN


end Kern

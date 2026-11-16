import Sums

/-! Exact global sums from semantic finite-change covers. A cover is proved
from update syntax and the already checked family; it is not an assumption
added to a source transition. This interface avoids requiring historical cover
certificate trees that an otherwise complete family capsule did not retain. -/
namespace Bapa.SemanticSums
open Kern

/-- Only addresses explicitly present in a finite syntactic cover may change
an integrand. Quantification is over every natural address, not a finite test. -/
def Preserves (h : SumMachine) (ps : List SEntry) : Prop :=
  ∀ ρ M, (∀ e ∈ ps, e.Holds ρ M) → ∀ ι κ,
    evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.s.f.m.assume = true →
    ∀ d ∈ h.sums, ∀ key,
      key ∉ d.cs.map (evalE (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2) →
      gAt d.g (sNext h.plain ρ M ι κ).2 key = gAt d.g M key

variable (h : SumMachine)
theorem sum_step (hok : sumOk h = true) (cover : Preserves h ps) {ρ M}
    (hsum : ∀ d ∈ h.sums, IsSum (gAt d.g M) (ρ d.v))
    (hlaws : ∀ e ∈ ps, e.Holds ρ M) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (ha : evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.s.f.m.assume = true) :
    ∀ d ∈ h.sums, IsSum (gAt d.g (sNext h.plain ρ M ι κ).2) ((sNext h.plain ρ M ι κ).1 d.v) := by
  obtain ⟨hdist, hall⟩ := sumOk_parts hok
  intro d hd
  obtain ⟨hg, _, _, hcar, _, _, _, _, hv, _⟩ := sumOk1_parts (hall d hd)
  let V := (sView h.plain ρ M ι κ).1
  let N := withCarried h.s M κ
  let M' := (sNext h.plain ρ M ι κ).2
  let cs' := d.cs.map (evalE V N)
  have hold : evalE V N (dTermE (gHere d) d.cs) = dsum (gAt d.g M) cs' := by
    rw [dTermE_eval V N d.cs (gHere d) (gAt d.g N) (fun t => gHere_eval d hg V N t), gAt_carried h d hcar]
  have hnew : evalE V N (dTermE (gAfter h.s d) d.cs) = dsum (gAt d.g M') cs' :=
    dTermE_eval V N d.cs (gAfter h.s d) (gAt d.g M') (fun t => gAfter_eval h d hg V N t)
  have hval : (sNext h.plain ρ M ι κ).1 d.v = ρ d.v + dsum (gAt d.g M') cs' - dsum (gAt d.g M) cs' := by
    show applyS (h.s.f.m.step ++ h.sums.map (fun d => (d.v, sumNext h.s d))) V N d.v = _
    simp only [applyS]
    rw [assoc_after (fun hm => hv (by simp [hm])), assoc_sums (sumNext h.s) hdist hd]
    simp only [sumNext, evalE, hold, hnew]
    have hview : V d.v = ρ d.v := view_v h hv ρ M ι κ
    rw [hview]
  rw [hval]
  exact isSum_change cs' (hsum d hd) (cover ρ M hlaws ι κ ha d hd)

theorem sum_start (hok : sumOk h = true) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hM : StartMaps h.plain.f.m M) :
    ∀ d ∈ h.sums, IsSum (gAt d.g M) (applyS h.plain.f.m.init ρ M d.v) := by
  obtain ⟨hdist, hall⟩ := sumOk_parts hok
  intro d hd
  obtain ⟨_, hm, h0, _, _, _, _, _, hv, _⟩ := sumOk1_parts (hall d hd)
  have hval : applyS h.plain.f.m.init ρ M d.v = 0 := by
    show applyS (h.s.f.m.init ++ h.sums.map (fun d => (d.v, E.const 0))) ρ M d.v = 0
    simp only [applyS]
    rw [assoc_after (fun hm' => hv (by simp [hm'])), assoc_sums (fun _ => E.const 0) hdist hd]
    rfl
  rw [hval]
  refine isSum_zero (fun key => ?_)
  rw [gAt]
  refine Eq.trans (congrME _ _ _ d.g (fun mp hmp => ?_)) h0
  funext _
  obtain ⟨p, hp, hpe⟩ := List.mem_map.mp (hm mp (mapsE_occ mp d.g hmp))
  cases hl : lookup (fun p => p.1 == mp) h.s.f.m.maps0 with
  | none => exact absurd (lookup_none_all hl p hp) (by simp [hpe])
  | some p0 =>
    obtain ⟨hp0, hp0e⟩ := lookup_some hl
    simp only [beq_iff_eq] at hp0e
    simp only [startVal, hl, Option.map_some, Option.getD_some]
    rw [← hp0e]; exact hM p0 hp0 key


theorem sum_facts (hok : sumOk h = true) (hs : sOk h.plain = true) {ρ : Nat → Nat} {M : Nat → Nat → Nat}
    (hsum : ∀ d ∈ h.sums, IsSum (gAt d.g M) (ρ d.v)) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 (sumsC h.sums) = true := by
  obtain ⟨_, hall⟩ := sumOk_parts hok
  obtain ⟨_, hqd, _, _, hdx, _, _⟩ := sOk_parts h.plain hs
  let N := withCarried h.s M κ
  let Wi := withInputs h.s.f.m.inputs ρ ι
  have one : ∀ d ∈ h.sums, evalC (sView h.plain ρ M ι κ).1 N (.and (sumFact d) (.eq (.var d.q) (.const 1))) = true := by
    intro d hd
    obtain ⟨hg, _, _, hcar, _, _, _, _, hv, hvk⟩ := sumOk1_parts (hall d hd)
    have hvi : d.v ∉ h.s.f.m.inputs := fun hm => hv (by simp [hm])
    simp only [evalC, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · show decide (evalE _ N (dTermE (gHere d) d.cs) ≤ (sView h.plain ρ M ι κ).1 d.v) = true
      apply decide_eq_true
      rw [dTermE_eval _ N d.cs (gHere d) (gAt d.g N) (fun t => gHere_eval d hg _ N t), gAt_carried h d hcar, view_v h hv ρ M ι κ]
      exact dsum_le (hsum d hd) _
    · have hqv : d.q ∈ h.plain.qVars := List.mem_map_of_mem (q_mem h hd)
      have hqf : d.q ∉ flagVars h.s.f.flags := fun hm =>
        (distinct_append hdx).2.2 d.q (by simp only [SMachine.extVars, List.mem_append]; exact Or.inl (Or.inr hqv)) hm
      show decideFlags h.s.f.flags (decideQ h.plain Wi N) N d.q = 1
      rw [decide_other hqf, decideQ_of, lookup_unique hqd (q_mem h hd)]
      simp only
      rw [if_pos]
      intro key
      rw [← evalC_iff]
      show decide (evalE _ N (dTermE (gHere d) (.var d.k :: d.cs.map (inlineE h.s.f.flags))) ≤ atKeys Wi [d.k] key d.v) = true
      apply decide_eq_true
      rw [dTermE_eval _ N _ (gHere d) (gAt d.g N) (fun t => gHere_eval d hg _ N t), gAt_carried h d hcar,
        atKeys_out (show d.v ∉ [d.k] by simpa using hvk)]
      show _ ≤ withInputs h.s.f.m.inputs ρ ι d.v
      rw [withInputs_other hvi]
      exact dsum_le (hsum d hd) _
  have all : ∀ ds : List SumDecl, (∀ d ∈ ds, d ∈ h.sums) → evalC (sView h.plain ρ M ι κ).1 N (sumsC ds) = true := by
    intro ds
    induction ds with
    | nil => intro _; rfl
    | cons d ds ih =>
      intro hm
      have h1 := one d (hm d List.mem_cons_self)
      have h2 := ih (fun d' hd' => hm d' (List.mem_cons_of_mem _ hd'))
      show (evalC _ N (.and (sumFact d) (.eq (.var d.q) (.const 1))) && evalC _ N (sumsC ds)) = true
      rw [h1, h2]; rfl
  exact all h.sums (fun _ hd => hd)

/-- The plain machine allows exactly the requests the rule's own assumption allows, wherever the sums are exact. -/
theorem sum_assume (hok : sumOk h = true) (hs : sOk h.plain = true) {ρ : Nat → Nat} {M : Nat → Nat → Nat}
    (hsum : ∀ d ∈ h.sums, IsSum (gAt d.g M) (ρ d.v)) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.plain.f.m.assume
      = evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.s.f.m.assume := by
  show (evalC _ _ h.s.f.m.assume && evalC _ _ (sumsC h.sums)) = _
  rw [sum_facts h hok hs hsum ι κ, Bool.and_true]


theorem sum_cells (hl : checkSMachine h.plain ps = true) (hok : sumOk h = true)
    (cover : Preserves h ps) :
    ∀ ρ M, SReach h.plain ρ M →
      (∀ d ∈ h.sums, IsSum (gAt d.g M) (ρ d.v)) ∧ ∀ e ∈ ps, e.Holds ρ M := by
  intro ρ M hr
  induction hr with
  | start ρ M hm hp hf hpf =>
      exact ⟨sum_start h hok ρ M hm, smachine_sound h.plain ps hl _ _ (.start ρ M hm hp hf hpf)⟩
  | step ρ M ι κ hr ha ih =>
      have ha0 : evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.s.f.m.assume = true := by
        have hboth : evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2
            (.and h.s.f.m.assume (sumsC h.sums)) = true := ha
        simp only [evalC, Bool.and_eq_true] at hboth
        exact hboth.1
      exact ⟨sum_step h hok cover ih.1 ih.2 ι κ ha0,
        smachine_sound h.plain ps hl _ _ (.step ρ M ι κ hr ha)⟩

theorem sum_holds (hl : checkSMachine h.plain ps = true) (hok : sumOk h = true)
    (cover : Preserves h ps) :
    ∀ ρ M, SReach h.plain ρ M → ∀ d ∈ h.sums, IsSum (gAt d.g M) (ρ d.v) :=
  fun ρ M hr => (sum_cells h hl hok cover ρ M hr).1

theorem sum_allowed (hl : checkSMachine h.plain ps = true) (hok : sumOk h = true)
    (cover : Preserves h ps) :
    ∀ ρ M, SReach h.plain ρ M → ∀ ι κ,
      evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.plain.f.m.assume =
      evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.s.f.m.assume :=
  fun ρ M hr ι κ => sum_assume h hok (sOk_of hl) (sum_holds h hl hok cover ρ M hr) ι κ

section project
variable (hg : sghostOk h.ghosts = true)
include hg
theorem sum_project (hl : checkSMachine h.plain ps = true) (hok : sumOk h = true)
    (cover : Preserves h ps) :
    ∀ {ρ M}, SReach h.s ρ M → ∃ ρg, SReach h.plain ρg M ∧ Agree h.ghosts.vars ρg ρ := by
  intro ρ M hr
  induction hr with
  | start ρ M hM h0 hfa hpf =>
    refine ⟨applyS h.plain.f.m.init ρ M, SReach.start ρ M hM h0 hfa hpf, fun i hi => ?_⟩
    have hvi : i ∉ h.sums.map (fun d => d.v) := fun hm => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm; exact hi (ghosts_vars h hd).1
    show applyS (h.s.f.m.init ++ h.sums.map (fun d => (d.v, E.const 0))) ρ M i = applyS h.s.f.m.init ρ M i
    exact applyS_append_other (by simpa using hvi) ρ M
  | step ρ M ι κ _ ha ih =>
    obtain ⟨ρg, hrg, hag⟩ := ih
    obtain ⟨hA, hS, hW⟩ := sum_ghost_step h hg hag M ι κ
    refine ⟨_, ?_, hS⟩
    rw [← hW]
    refine SReach.step ρg M ι κ hrg ?_
    rw [sum_allowed h hl hok cover ρg M hrg ι κ, hA]; exact ha

/-- The laws of the plain machine that read no sum's name hold in every state the rule reaches. -/
theorem sum_project_laws (ps : List SEntry) (hl : checkSMachine h.plain ps = true) (hok : sumOk h = true)
    (cover : Preserves h ps) :
    ∀ ρ M, SReach h.s ρ M → ∀ e ∈ ps, avoids h.ghosts.vars e.law.holds = true → e.Holds ρ M := by
  intro ρ M hr e he hav
  obtain ⟨ρg, hrg, hag⟩ := sum_project h hg hl hok cover hr
  exact sentry_transfer (V := h.ghosts.vars) (MS := []) hav (by simp [avoidsMaps]) (fun i hi => (hag i hi).symm) (fun _ _ => rfl)
    (smachine_sound h.plain ps hl ρg M hrg e he)


end project
#print axioms sum_cells
#print axioms sum_project_laws
end Bapa.SemanticSums

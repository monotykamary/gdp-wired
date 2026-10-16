import Progress

/-!
StepLaw: kernel.ts's step laws, "every request the machine allows takes a step where `then` holds", proven sound.

`then` reads the state before the step (with the request's inputs) by plain names and the state and maps after it by
primed names (`prime`, `primeMaps`), as Progress does; `when` narrows the requests. Where Progress names one request
and must prove it allowed, a step law is about every request: its inputs are any `ι`, and the machine's assumption
(flags decided) is a hypothesis. Lean builds the goal itself from the machine (`stepLawGoal`, reusing Progress's
`progressBefore`, `primeSub` and `rdAfter` with an empty request), and `steplaw_sound` shows that an accepted tree makes
`StepLawHolds` true in every reachable state. The exporter inlines flags into `when` and `then` (as kernel.ts's goal
does), so both must read no flag variable.
-/

namespace Kern

structure StepLaw where
  when : C
  then_ : C
  prime : List (Nat × Nat)      -- a state variable, and the name `then` reads its value after the step by
  primeMaps : List (Nat × Nat)  -- a map, and the name `then` reads it after the step by
  insts : List (Nat × E)        -- (law index, key): where the goal assumes the laws about every key
  proof : List VDef × Tree

-- The same goal shape as Progress's, with no request named: the request's inputs are the inputs as they are.
def asProgress (sl : StepLaw) : Progress := ⟨sl.when, sl.then_, [], sl.prime, sl.primeMaps, sl.insts, sl.proof, sl.proof⟩

def stepLawGoal (f : FMMachine) (laws : List MLaw) (sl : StepLaw) : List C :=
  progressBefore f laws (asProgress sl)
    ++ [inlineC f.flags f.m.assume, .not (substRC (primeSub f (asProgress sl)) (rdAfter f (asProgress sl)) sl.then_)]

def checkStepLaw (f : FMMachine) (ps : List MEntry) (sl : StepLaw) : Bool :=
  avoids (flagVars f.flags) sl.then_ && avoids (flagVars f.flags) sl.when
    && checkGoal ⟨sl.proof.1, stepLawGoal f (ps.map (·.law)) sl⟩ sl.proof.2

/-- A step law: in every reachable state, every request (inputs ι) the machine allows with its flags decided, and that
`when` admits, takes a step where `then` holds: primed names read the state and maps after it, plain names the state
before it with the request's inputs. -/
def StepLawHolds (f : FMMachine) (sl : StepLaw) : Prop :=
  ∀ ρ M, FMReach f ρ M → ∀ ι : Nat → Nat,
    evalC (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M f.m.assume = true →
    evalC (withInputs f.m.inputs ρ ι) M sl.when = true →
    evalC (primed sl.prime (applyS f.m.step (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M) (withInputs f.m.inputs ρ ι))
      (primedMaps sl.primeMaps (writeMaps f.m.writes (decideFlags f.flags (withInputs f.m.inputs ρ ι) M) M) M)
      sl.then_ = true

theorem applyS_nil (ρ : Nat → Nat) (M : Nat → Nat → Nat) : applyS [] ρ M = ρ := by
  funext i; simp [applyS, assoc, lookup]

theorem steplaw_sound (f : FMMachine) (ps : List MEntry) (sl : StepLaw)
    (hl : checkFMMachine f ps = true) (hs : checkStepLaw f ps sl = true) : StepLawHolds f sl := by
  intro ρ M hr ι hA hW
  have hl0 := hl
  simp only [checkFMMachine, Bool.and_eq_true, List.all_eq_true] at hl
  obtain ⟨⟨⟨hf, hpref⟩, _⟩, hc⟩ := hl
  simp only [checkStepLaw, Bool.and_eq_true] at hs
  obtain ⟨_, hgoal⟩ := hs
  obtain ⟨ρ₀, hr₀, hag⟩ := fmreach_plain f hf hr
  -- The laws and the precondition hold in the reachable state.
  have hlaws : ∀ e ∈ ps, e.law.Holds ρ M := fmmachine_sound f ps hl0 ρ M hr
  have hcm := hc
  simp only [checkMMachine, Bool.and_eq_true, List.all_eq_true] at hcm
  obtain ⟨⟨hpa, hpr⟩, hent⟩ := hcm
  try simp only [Bool.not_eq_true'] at hpr
  have hpre : evalC ρ M f.m.pre = true := by
    rw [congrC ρ ρ₀ M f.m.pre (fun j hj => hag j (avoids_occ hpref hj))]
    exact pre_mreach (m := f.plain) hpa hpr hr₀
  -- They hold with the request's inputs too: neither reads an input.
  have hagX : Agree f.m.inputs (withInputs f.m.inputs ρ ι) ρ := fun i hi => withInputs_other hi ρ ι
  have hpreX : evalC (withInputs f.m.inputs ρ ι) M f.m.pre = true := by
    rw [congrC (withInputs f.m.inputs ρ ι) ρ M f.m.pre (fun j hj => hagX j (fun h =>
      avoids_occ hpa hj (List.mem_append_left _ (List.mem_append_left _ h))))]
    exact hpre
  have hlawsX : ∀ e ∈ ps, e.law.Holds (withInputs f.m.inputs ρ ι) M := by
    intro e he
    have hav := hent e he
    exact holds_agree e.law hav.1.1.1 hagX M (hlaws e he)
  have hb := before_true f ps (asProgress sl) (withInputs f.m.inputs ρ ι) M hpreX hlawsX hW
  apply Decidable.byContradiction; intro hn
  apply sound _ _ hgoal (withInputs f.m.inputs ρ ι) M
  intro c hc'
  simp only [stepLawGoal, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with hc' | rfl | rfl
  · exact hb c hc'
  · rw [inline_evalC]; exact hA
  · let e := decideFlags f.flags (withInputs f.m.inputs ρ ι) M
    have hnow : ∀ t, evalE (withInputs f.m.inputs ρ ι) M (nowE f (asProgress sl) t) = evalE e M t := by
      intro t; simp only [nowE, asProgress, subst_evalE, applyS_nil, inline_evalE, e]
    have hrd : ∀ mp k, evalE (withInputs f.m.inputs ρ ι) M (rdAfter f (asProgress sl) mp k)
        = primedMaps sl.primeMaps (writeMaps f.m.writes e M) M mp (evalE (withInputs f.m.inputs ρ ι) M k) := by
      intro mp k
      simp only [rdAfter, primedMaps, asProgress]
      cases hq : lookup (fun q => q.2 == mp) sl.primeMaps with
      | none => simp [evalE]
      | some q =>
        simp only [writeMaps]
        cases hw : lookup (fun w => w.1 == q.1) f.m.writes with
        | none => simp [evalE]
        | some w =>
          have h1 := hnow w.2.1
          have h2 := hnow w.2.2
          simp only [asProgress] at h1 h2
          simp only [evalE, evalC, h1, h2]
          by_cases hk : evalE (withInputs f.m.inputs ρ ι) M k = evalE e M w.2.1 <;> simp [hk]
    have henv : applyS (primeSub f (asProgress sl)) (withInputs f.m.inputs ρ ι) M = primed sl.prime (applyS f.m.step e M) (withInputs f.m.inputs ρ ι) := by
      funext i
      have hps : lookup (fun p : Nat × E => p.1 == i) (primeSub f (asProgress sl))
          = (lookup (fun q => q.2 == i) sl.prime).map (fun q => (q.2, nowE f (asProgress sl) (stepTerm f q.1))) := by
        simp only [primeSub, asProgress, lookup_map_pred]
      simp only [primed, applyS, assoc, hps]
      cases hq : lookup (fun q => q.2 == i) sl.prime with
      | none => rfl
      | some q =>
        simp only [Option.map_some]
        rw [hnow]
        simp only [stepTerm]
        cases hs : assoc f.m.step q.1 with
        | none =>
          rw [show Option.map (fun x => x.2) (lookup (fun p => p.1 == q.1) f.m.step) = none from hs]
          simp [evalE, e]
        | some t =>
          rw [show Option.map (fun x => x.2) (lookup (fun p => p.1 == q.1) f.m.step) = some t from hs]
    simp only [evalC, substR_evalC _ _ _ M _ hrd, henv]
    simpa [e] using hn

end Kern

#print axioms Kern.steplaw_sound

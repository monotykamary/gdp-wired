import Sets

/-! Checked accelerated refutation over unmodified `Sets.lean` / `Kernel.lean`.
No new trusted rules and no new axioms: every repeat segment is proved by
induction on the repeat count `j` using `Kern.sound` on ordinary kernel goals
(`checkGoal g t = true`), and concrete prefix/suffix steps replay via
`SReach.step`. -/

open Kern

namespace AccelRefute

abbrev Env := Nat → Nat
abbrev Maps := Nat → Nat → Nat

/-- Two environments agree outside inputs and plain flag variables. -/
def AgreeOn (inputs : List Nat) (fl : List (Nat × C)) (ρ1 ρ2 : Env) : Prop :=
  ∀ v, v ∉ inputs → flagOf fl v = none → ρ1 v = ρ2 v

/-- No plain flag body reads any plain flag variable (the standard `flagsOfM` normal form). -/
def flagsNoFlag (fl : List (Nat × C)) : Bool :=
  fl.all fun p => fl.all fun q => !occC q.1 p.2

/-- Right-nested conjunction matching `leanConnective 'and'` on nonempty lists. -/
def andList : List C → C
  | [] => .le (.const 0) (.const 0)
  | [x] => x
  | x :: xs => .and x (andList xs)

theorem evalC_andList (ρ : Env) (M : Maps) :
    ∀ cs : List C, evalC ρ M (andList cs) = true ↔ ∀ c ∈ cs, evalC ρ M c = true
  | [] => by simp [andList, evalC]
  | [x] => by simp [andList]
  | x :: y :: rest => by
    simp only [andList, evalC, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    exact and_congr Iff.rfl ((evalC_andList ρ M (y :: rest)).trans (by
      simp only [List.mem_cons, forall_eq_or_imp]))

private theorem lookup_mem {α : Type} (p : α → Bool) (xs : List α) (a : α)
    (h : lookup p xs = some a) : a ∈ xs := by
  induction xs with
  | nil => simp [lookup] at h
  | cons x xs ih =>
    cases hx : p x with
    | false => exact List.mem_cons_of_mem _ (ih (by simpa [lookup, hx] using h))
    | true =>
      have he : x = a := by simpa [lookup, hx] using h
      simp [he]

private theorem lookup_hit {α : Type} (p : α → Bool) (xs : List α) (a : α)
    (h : lookup p xs = some a) : p a = true := by
  induction xs with
  | nil => simp [lookup] at h
  | cons x xs ih =>
    cases hx : p x with
    | false => exact ih (by simpa [lookup, hx] using h)
    | true =>
      have he : x = a := by simpa [lookup, hx] using h
      simpa [← he] using hx

private theorem flagOf_some_mem (fl : List (Nat × C)) (i : Nat) (c : C)
    (h : flagOf fl i = some c) : (i, c) ∈ fl := by
  unfold flagOf at h
  cases hl : lookup (fun p => p.1 == i) fl with
  | none => simp [hl] at h
  | some p =>
    have hm := lookup_mem _ _ _ hl
    have ht : p.1 = i := by simpa using lookup_hit _ _ _ hl
    have hc : p.2 = c := by simpa [hl] using h
    cases p; simp only at ht hc; subst ht hc; exact hm

private theorem flagOf_none_of_not_mem (fl : List (Nat × C)) (i : Nat)
    (h : ∀ p ∈ fl, p.1 ≠ i) : flagOf fl i = none := by
  cases hf : flagOf fl i with
  | none => rfl
  | some c => exact False.elim (h (i, c) (flagOf_some_mem fl i c hf) rfl)

theorem withCarried_nil (s : SMachine) (hc : s.carried = []) (M κ : Maps) :
    withCarried s M κ = M := by
  funext mp k
  simp [withCarried, hc]

theorem decideQ_nil (s : SMachine) (hq : s.qflags = []) (X : Env) (N : Maps) :
    decideQ s X N = X := by
  funext i
  simp [decideQ, hq, lookup]

theorem sView_scalar (s : SMachine) (hq : s.qflags = []) (hc : s.carried = [])
    (ρ : Env) (M : Maps) (ι : Env) (κ : Maps) :
    sView s ρ M ι κ = (decideFlags s.f.flags (withInputs s.f.m.inputs ρ ι) M, M) := by
  simp [sView, withCarried_nil s hc, decideQ_nil s hq]

theorem everyMaps_scalar (s : SMachine) (he : s.every = []) (hw : s.f.m.writes = [])
    (D : Env) (N : Maps) : everyMaps s D N = N := by
  funext mp k
  simp [everyMaps, he, writeMaps, hw, lookup]

theorem sNext_scalar (s : SMachine) (hq : s.qflags = []) (hc : s.carried = [])
    (he : s.every = []) (hw : s.f.m.writes = [])
    (ρ : Env) (M : Maps) (ι : Env) (κ : Maps) :
    sNext s ρ M ι κ =
      (applyS s.f.m.step (decideFlags s.f.flags (withInputs s.f.m.inputs ρ ι) M) M, M) := by
  simp [sNext, sView_scalar s hq hc, everyMaps_scalar s he hw]

theorem decideFlags_agree (inputs : List Nat) (fl : List (Nat × C)) (req : Env) (M : Maps)
    {ρ1 ρ2 : Env} (ha : AgreeOn inputs fl ρ1 ρ2) (hfl : flagsNoFlag fl = true) :
    decideFlags fl (withInputs inputs ρ1 req) M =
      decideFlags fl (withInputs inputs ρ2 req) M := by
  have hwi : ∀ v, flagOf fl v = none →
      withInputs inputs ρ1 req v = withInputs inputs ρ2 req v := by
    intro v hv
    by_cases hi : v ∈ inputs
    · simp [withInputs, List.contains_iff_mem, hi]
    · simp [withInputs, List.contains_iff_mem, hi, ha v hi hv]
  funext i
  simp only [decideFlags, applyS, assoc_flagSub]
  cases hf : flagOf fl i with
  | none => exact hwi i hf
  | some c =>
    have hmem := flagOf_some_mem fl i c hf
    have hno : ∀ q ∈ fl, occC q.1 c = false := by
      have h1 := (List.all_eq_true.mp hfl) (i, c) hmem
      intro q hq
      have h2 := (List.all_eq_true.mp h1) q hq
      simpa using h2
    have hceq : evalC (withInputs inputs ρ1 req) M c = evalC (withInputs inputs ρ2 req) M c := by
      apply congrC
      intro v hv
      apply hwi v
      apply flagOf_none_of_not_mem
      intro q hq heq
      subst heq
      have h0 := hno q hq
      simp [h0] at hv
    simp [evalE, hceq]

/-- Initialize a concrete `SReach` state agreeing with `base`. -/
theorem sreach_start_agree (s : SMachine) (ρ0 : Env) (M : Maps) (base : Env)
    (hM : StartMaps s.f.m M) (hpre : evalC ρ0 M s.f.m.pre = true)
    (hfacts : ∀ l ∈ s.facts, l.Holds ρ0 M) (hpf : s.PFacts ρ0 M)
    (hagree : AgreeOn s.f.m.inputs s.f.flags (applyS s.f.m.init ρ0 M) base) :
    ∃ ρ, SReach s ρ M ∧ AgreeOn s.f.m.inputs s.f.flags ρ base :=
  ⟨applyS s.f.m.init ρ0 M, SReach.start ρ0 M hM hpre hfacts hpf, hagree⟩

/-- Advance one concrete step from a state agreeing with `base` to one agreeing with `next`. -/
theorem sreach_concrete_step (s : SMachine) (M : Maps) (req base next : Env)
    (hq : s.qflags = []) (hc : s.carried = []) (he : s.every = []) (hw : s.f.m.writes = [])
    (hfl : flagsNoFlag s.f.flags = true)
    (hcur : ∃ ρ, SReach s ρ M ∧ AgreeOn s.f.m.inputs s.f.flags ρ base)
    (hallow : evalC (decideFlags s.f.flags (withInputs s.f.m.inputs base req) M) M s.f.m.assume = true)
    (hnext : AgreeOn s.f.m.inputs s.f.flags
      (applyS s.f.m.step (decideFlags s.f.flags (withInputs s.f.m.inputs base req) M) M) next) :
    ∃ ρ', SReach s ρ' M ∧ AgreeOn s.f.m.inputs s.f.flags ρ' next := by
  obtain ⟨ρ, hreach, hagree⟩ := hcur
  have hd := decideFlags_agree s.f.m.inputs s.f.flags req M hagree hfl
  have hallow' : evalC (sView s ρ M req (fun _ _ => 0)).1 (sView s ρ M req (fun _ _ => 0)).2 s.f.m.assume = true := by
    rw [sView_scalar s hq hc, hd]; exact hallow
  have hstep := SReach.step ρ M req (fun _ _ => 0) hreach hallow'
  rw [sNext_scalar s hq hc he hw, hd] at hstep
  exact ⟨_, hstep, hnext⟩

/-- Checked induction on `j ∈ [0, K]` for repeating request `req` `K` times with closed form `phi`. -/
theorem sreach_repeat_checked (s : SMachine) (M : Maps) (req : Env) (K : Nat) (phi : Nat → Env)
    (hq : s.qflags = []) (hc : s.carried = []) (he : s.every = []) (hw : s.f.m.writes = [])
    (hfl : flagsNoFlag s.f.flags = true)
    (hbase : ∃ ρ, SReach s ρ M ∧ AgreeOn s.f.m.inputs s.f.flags ρ (phi 0))
    (hallow : ∀ j, j < K →
      evalC (decideFlags s.f.flags (withInputs s.f.m.inputs (phi j) req) M) M s.f.m.assume = true)
    (hstep : ∀ j, j < K →
      AgreeOn s.f.m.inputs s.f.flags
        (applyS s.f.m.step (decideFlags s.f.flags (withInputs s.f.m.inputs (phi j) req) M) M)
        (phi (j + 1))) :
    ∃ ρ, SReach s ρ M ∧ AgreeOn s.f.m.inputs s.f.flags ρ (phi K) := by
  have go : ∀ j, j ≤ K → ∃ ρ, SReach s ρ M ∧ AgreeOn s.f.m.inputs s.f.flags ρ (phi j) := by
    intro j hj
    induction j with
    | zero => exact hbase
    | succ j ih =>
      have hlt : j < K := Nat.lt_of_succ_le hj
      exact sreach_concrete_step s M req (phi j) (phi (j + 1)) hq hc he hw hfl
        (ih (Nat.le_of_lt hlt)) (hallow j hlt) (hstep j hlt)
  exact go K (Nat.le_refl K)

/-- Derive admissibility `hallow` for all `j < K` from a kernel-checked `allowGoal`. -/
theorem allow_of_goal (s : SMachine) (M : Maps) (p0 req : Env) (jVar K : Nat)
    (phi : Nat → Env) (σ : List (Nat × E)) (facts : List C) (tab : List VDef) (tree : Tree)
    (hcheck : checkGoal ⟨tab, (.lt (.var jVar) (.const K)) :: facts ++ [.not (substC σ (inlineC s.f.flags s.f.m.assume))]⟩ tree = true)
    (hfresh : occC jVar (inlineC s.f.flags s.f.m.assume) = false)
    (hfacts : ∀ j, j < K → ∀ c ∈ facts, evalC (upd p0 jVar j) M c = true)
    (hsub : ∀ j v, v ≠ jVar → applyS σ (upd p0 jVar j) M v = withInputs s.f.m.inputs (phi j) req v) :
    ∀ j, j < K →
      evalC (decideFlags s.f.flags (withInputs s.f.m.inputs (phi j) req) M) M s.f.m.assume = true := by
  intro j hj
  have hunsat := sound _ tree hcheck (upd p0 jVar j) M
  have hceq : evalC (applyS σ (upd p0 jVar j) M) M (inlineC s.f.flags s.f.m.assume) =
      evalC (withInputs s.f.m.inputs (phi j) req) M (inlineC s.f.flags s.f.m.assume) := by
    apply congrC
    intro v hv
    apply hsub j v
    intro heq; subst heq; simp [hfresh] at hv
  cases hev : evalC (decideFlags s.f.flags (withInputs s.f.m.inputs (phi j) req) M) M s.f.m.assume with
  | true => rfl
  | false =>
    exfalso
    apply hunsat
    intro c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | hfm | rfl
    · simp [evalC, evalE, upd, hj]
    · exact hfacts j hj c hfm
    · simp only [evalC, subst_evalC, hceq, inline_evalC, hev]; rfl

/-- Derive step preservation `hstep` for all `j < K` from a kernel-checked `stepGoal`. -/
theorem step_of_goal (s : SMachine) (M : Maps) (p0 req : Env) (jVar K : Nat)
    (phi : Nat → Env) (σ : List (Nat × E)) (eqs : List (Nat × E × E))
    (facts : List C) (tab : List VDef) (tree : Tree)
    (hcheck : checkGoal ⟨tab, (.lt (.var jVar) (.const K)) :: facts ++ [.not (andList (eqs.map fun q => .eq (substE σ (inlineE s.f.flags q.2.1)) q.2.2))]⟩ tree = true)
    (hfresh : eqs.all (fun q => !occE jVar (inlineE s.f.flags q.2.1)) = true)
    (hfacts : ∀ j, j < K → ∀ c ∈ facts, evalC (upd p0 jVar j) M c = true)
    (hsub : ∀ j v, v ≠ jVar → applyS σ (upd p0 jVar j) M v = withInputs s.f.m.inputs (phi j) req v)
    (heqs_step : ∀ v e, assoc s.f.m.step v = some e → ∃ rhs, (v, e, rhs) ∈ eqs ∧ ∀ j, j < K → evalE (upd p0 jVar j) M rhs = phi (j + 1) v)
    (hframe : ∀ j, j < K → ∀ v, v ∉ s.f.m.inputs → flagOf s.f.flags v = none → assoc s.f.m.step v = none → phi j v = phi (j + 1) v) :
    ∀ j, j < K →
      AgreeOn s.f.m.inputs s.f.flags
        (applyS s.f.m.step (decideFlags s.f.flags (withInputs s.f.m.inputs (phi j) req) M) M)
        (phi (j + 1)) := by
  intro j hj
  have hunsat := sound _ tree hcheck (upd p0 jVar j) M
  have hall : evalC (upd p0 jVar j) M (andList (eqs.map fun q => .eq (substE σ (inlineE s.f.flags q.2.1)) q.2.2)) = true := by
    cases hc : evalC (upd p0 jVar j) M (andList (eqs.map fun q => .eq (substE σ (inlineE s.f.flags q.2.1)) q.2.2)) with
    | true => rfl
    | false =>
      exfalso
      apply hunsat
      intro c hcm
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hcm
      rcases hcm with rfl | hfm | rfl
      · simp [evalC, evalE, upd, hj]
      · exact hfacts j hj c hfm
      · simp [evalC, hc]
  have heach := (evalC_andList (upd p0 jVar j) M _).mp hall
  intro v hvin hvfl
  simp only [applyS]
  cases ha : assoc s.f.m.step v with
  | none =>
    simp only [decideFlags, applyS, assoc_flagSub, hvfl, Option.map_none, withInputs, List.contains_iff_mem, hvin, ite_false]
    exact hframe j hj v hvin hvfl ha
  | some e =>
    obtain ⟨rhs, hmem, hrhs⟩ := heqs_step v e ha
    have hfr : occE jVar (inlineE s.f.flags e) = false := by
      have h1 := (List.all_eq_true.mp hfresh) (v, e, rhs) hmem
      simpa using h1
    have heeq : evalE (applyS σ (upd p0 jVar j) M) M (inlineE s.f.flags e) =
        evalE (withInputs s.f.m.inputs (phi j) req) M (inlineE s.f.flags e) := by
      apply congrE
      intro u hu
      apply hsub j u
      intro heq; subst heq; simp [hfr] at hu
    have hmem' : C.eq (substE σ (inlineE s.f.flags e)) rhs ∈
        eqs.map (fun q => C.eq (substE σ (inlineE s.f.flags q.2.1)) q.2.2) :=
      List.mem_map.mpr ⟨(v, e, rhs), hmem, rfl⟩
    have heq := heach _ hmem'
    simp only [evalC, subst_evalE, heeq, inline_evalE, decide_eq_true_eq] at heq
    exact heq.trans (hrhs j hj)

/-- Conclude `∃ ρ M, SReach s ρ M ∧ ¬ law.Holds ρ M` from reaching a violating state. -/
theorem refutes_of_reached (s : SMachine) (M : Maps) (law : MLaw) (finalEnv : Env)
    (hkey : law.key = none)
    (havoids : avoids (s.f.m.inputs ++ s.f.flags.map (·.1)) law.holds = true)
    (hreach : ∃ ρ, SReach s ρ M ∧ AgreeOn s.f.m.inputs s.f.flags ρ finalEnv)
    (hbreaks : evalC finalEnv M law.holds = false) :
    ∃ ρ M', SReach s ρ M' ∧ ¬ law.Holds ρ M' := by
  obtain ⟨ρ, hr, hagree⟩ := hreach
  refine ⟨ρ, M, hr, ?_⟩
  have heq : evalC ρ M law.holds = evalC finalEnv M law.holds := by
    apply evalC_avoids havoids
    intro v hv
    have h1 : v ∉ s.f.m.inputs := fun h => hv (List.mem_append_left _ h)
    have h2 : flagOf s.f.flags v = none := by
      apply flagOf_none_of_not_mem
      intro p hp heq
      apply hv
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨p, hp, heq⟩
    exact hagree v h1 h2
  intro hholds
  have ht : evalC ρ M law.holds = true := by
    cases law with
    | mk holds key =>
      simp only at hkey; subst hkey
      exact hholds
  rw [heq, hbreaks] at ht
  contradiction

end AccelRefute

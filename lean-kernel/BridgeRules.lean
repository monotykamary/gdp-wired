import Bridge
import Refine
import History

/-!
BridgeRules: the rest of today's rules carried by cyclic proofs. Lean 4.34.0, core only, on top of `Bridge.lean`.

Bridge.lean carries a cyclic proof's node to a machine's law about every reachable state. The rules beside the laws
claim more: a step law (and a k-step law) is about every k allowed requests in a row from every reachable state. Here
a node over the same encoding reads the run's last k steps up to time t, each time one step back from the next (t − 1,
t − 1 − 1, …, as a step's fact reads the time before it): the first state at t − k, the j-th request at t − (k − j), the
state after them at t. Its hypotheses are among the precondition, k ≤ t, t ≤ T, T < Ω and each step's `when` at its time,
its conclusion `then` with the plain names at t − k, each later request's inputs and the maps it carries at its time, and
the primed names at t (`cycKOk`). `cyc_kstep_sound`: such a node of a checked cyclic proof makes the k-step law hold, as
Sets.lean's `SKStepHolds` states it (the claim `skstep_sound` proves of the usual certificate). The run is the one a
reachable state ends (`reach_run`), extended by the k requests (`run_ext`).

From those, what the other rules claim, each from its claims' meaning in place of their certificates: liveness under
fairness (`sleads_of_holds`) and weak fairness (`sleads_wf_of_holds`, a helpful request allowed being a node at the
run's last request, `cyc_allow_sound`), a history's laws through its plain machine (`hreach_plain`), a ghosted machine's
laws of the original (`cyc_ghost_holds`), a refinement (`srefines_of_holds`).

Flags that hold at every key (a machine with `qflags`): Bridge.lean's encoding has none. Here the machine is read as its
sk machine (`SMachine.sk`: the flags and their witnesses inputs a request names), whose runs, every request decided as a
goal reads it (`sReq`, `CRun.Decided`), are the machine's off the witnesses (`sk_step`, `sk_run`); the encoding adds the
flags' closing conditions at each time (`cycQFacts`: 0 or 1, 0 or the body at every value of its keys, 1 or the body
failing at the witness), which hold on such runs (`qfacts_hold`, through Sets.lean's `closing_true`). `cyc_qmachine_sound`,
`cyc_qkstep_sound` and `cyc_qallow_sound` are the three bridges for them.
-/

namespace Kern
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! A run extended by requests -/

theorem run_snoc_ok {s : SMachine} (hq : s.qflags = []) {r : CRun} {T : Nat} (hr : r.Ok s T) {ρ : Nat → Nat}
    {M : Nat → Nat → Nat} (hst : r.st T = ρ) (hmp : r.mp T = M) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (ha : evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume = true) :
    (r.snoc T (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2 ι κ).Ok s (T + 1) := by
  have hv : sView s ρ M ι κ = (decideFlags s.f.flags (withInputs s.f.m.inputs ρ ι) (withCarried s M κ), withCarried s M κ) := by
    simp only [sView, decideQ_nil hq]
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := snoc_last (r := r) (T := T) (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2 ι κ
  obtain ⟨z1, z2, z3⟩ := snoc_zero (r := r) (T := T) (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2 ι κ
  have hN : (r.snoc T (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2 ι κ).N s T = (sView s ρ M ι κ).2 := by
    rw [hv, CRun.N, l4, l6, hmp]
  have hV : (r.snoc T (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2 ι κ).V s T = (sView s ρ M ι κ).1 := by
    rw [CRun.V, hN, CRun.X, l3, l5, hst, hv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [z3]; exact hr.maps0
  · rw [z1, z3]; exact hr.pre
  · rw [z1, z3]; exact hr.facts
  · rw [z1, z3]; exact hr.pfacts
  · rw [z1, z2, z3]; exact hr.init
  · intro u hu
    rcases Nat.lt_or_ge u T with hlt | hge
    · obtain ⟨e1, e2, e3, e4⟩ := snoc_early (s := s) (r := r) hlt (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2 ι κ
      rw [e1, e2, e3, e4]; exact hr.step u hlt
    · have hu' : u = T := by omega
      rw [hu', hV, hN, l1, l2]
      exact ⟨ha, rfl, rfl⟩

-- A run that ends in a state, extended by requests the machine allows one after another.
theorem run_ext {s : SMachine} (hq : s.qflags = []) : ∀ (qs : List SRequest) (ws : List C) (r : CRun) (T : Nat)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat), r.Ok s T → r.st T = ρ → r.mp T = M → qs.length ≤ ws.length → SAllowed s ws ρ M qs →
    ∃ r' : CRun, r'.Ok s (T + qs.length) ∧ r'.ρ0 = r.ρ0 ∧ (∀ u, u ≤ T → r'.st u = r.st u ∧ r'.mp u = r.mp u)
      ∧ (∀ u, u < T → r'.ι u = r.ι u ∧ r'.κ u = r.κ u)
      ∧ (∀ j, j ≤ qs.length → r'.st (T + j) = (sEnd s ρ M (qs.take j)).1 ∧ r'.mp (T + j) = (sEnd s ρ M (qs.take j)).2)
      ∧ (∀ j (h : j < qs.length), r'.ι (T + j) = qs[j].1 ∧ r'.κ (T + j) = qs[j].2)
  | [], _, r, T, ρ, M, hr, hst, hmp, _, _ => by
    refine ⟨r, hr, rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun j hj => ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    have : j = 0 := by simpa using hj
    subst this
    simp [sEnd, hst, hmp]
  | q :: qs, [], _, _, _, _, _, _, _, hlen, _ => by simp at hlen
  | q :: qs, w :: ws, r, T, ρ, M, hr, hst, hmp, hlen, hK => by
    obtain ⟨ha, _, hrest⟩ := hK
    have hr1 := run_snoc_ok hq hr hst hmp q.1 q.2 ha
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := snoc_last (r := r) (T := T) (sNext s ρ M q.1 q.2).1 (sNext s ρ M q.1 q.2).2 q.1 q.2
    obtain ⟨r', hr', h0, hle, hlt, hj, hι⟩ := run_ext hq qs ws _ (T + 1) _ _ hr1 l1 l2 (by simp at hlen; omega) hrest
    refine ⟨r', by simpa [Nat.add_assoc, Nat.add_comm 1] using hr', h0, fun u hu => ?_, fun u hu => ?_, fun j hjl => ?_, fun j hjl => ?_⟩
    · obtain ⟨a, b⟩ := hle u (by omega)
      rw [a, b]; simp [CRun.snoc, hu]
    · obtain ⟨a, b⟩ := hlt u (by omega)
      rw [a, b]; simp [CRun.snoc, hu]
    · cases j with
      | zero =>
        obtain ⟨a, b⟩ := hle T (by omega)
        rw [Nat.add_zero, a, b, l3, l4, hst, hmp]; simp [sEnd]
      | succ j =>
        obtain ⟨a, b⟩ := hj j (by simp at hjl; omega)
        rw [show T + (j + 1) = T + 1 + j by omega, a, b]
        simp [sEnd]
    · cases j with
      | zero =>
        obtain ⟨a, b⟩ := hlt T (by omega)
        rw [Nat.add_zero, a, b, l5, l6]; simp
      | succ j =>
        obtain ⟨a, b⟩ := hι j (by simp at hjl; omega)
        rw [show T + (j + 1) = T + 1 + j by omega, a, b]
        simp

-- Each `when` along the requests: the j-th met at the state the first j steps reach.
theorem sallowed_at {s : SMachine} : ∀ (qs : List SRequest) (ws : List C) (ρ : Nat → Nat) (M : Nat → Nat → Nat),
    SAllowed s ws ρ M qs → ∀ j (hq : j < qs.length) (hw : j < ws.length),
      evalC (withExt s (sEnd s ρ M (qs.take j)).1 (sReq s (sEnd s ρ M (qs.take j)).1 (sEnd s ρ M (qs.take j)).2 qs[j].1 qs[j].2))
        (withCarried s (sEnd s ρ M (qs.take j)).2 qs[j].2) ws[j] = true
  | [], _, _, _, _, j, hq, _ => absurd hq (Nat.not_lt_zero j)
  | _ :: _, [], _, _, _, j, _, hw => absurd hw (Nat.not_lt_zero j)
  | q :: qs, w :: ws, ρ, M, hK, j, hq, hw => by
    obtain ⟨_, hW, hrest⟩ := hK
    cases j with
    | zero => simpa [sEnd] using hW
    | succ j =>
      have := sallowed_at qs ws _ _ hrest j (by simp at hq; omega) (by simp at hw; omega)
      simpa [sEnd] using this

/-! A machine with no flag at every key and no witness reads its request plainly -/

theorem sReq_plain {s : SMachine} (hq : s.qflags = []) (hw : s.wits = []) (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) (v : Nat) : sReq s ρ M ι κ v = if s.f.m.inputs.contains v then ι v else 0 := by
  simp only [sReq, hq, hw, lookup]

theorem withExt_plain {s : SMachine} (hq : s.qflags = []) (hw : s.wits = []) (ρ e : Nat → Nat) (v : Nat) :
    withExt s ρ e v = if s.f.m.inputs.contains v then e v else ρ v := by
  simp only [withExt, SMachine.extVars, SMachine.qVars, SMachine.wVars, hq, hw, List.map_nil, List.flatMap_nil, List.append_nil]

theorem sExts_plain {s : SMachine} (hq : s.qflags = []) (hw : s.wits = []) : ∀ (ρ : Nat → Nat) (M : Nat → Nat → Nat) (qs : List SRequest),
    sExts s ρ M qs = qs.map (fun q v => if s.f.m.inputs.contains v then q.1 v else 0)
  | _, _, [] => rfl
  | ρ, M, q :: qs => by
    simp only [sExts, List.map_cons, sExts_plain hq hw _ _ qs]
    congr 1; funext v; exact sReq_plain hq hw ρ M q.1 q.2 v

/-! The encoding of a k-step law -/

-- Time t − n, one step back at a time (t − 1 − 1 …), as a step's fact reads the time before it: the j-th state of k at
-- t − (k − j), the last at t.
def tBack (ce : CycEnc) : Nat → E
  | 0 => .var ce.t
  | n + 1 => .sub (tBack ce n) (.const 1)

theorem tBack_eval (ce : CycEnc) (Q : Nat → Nat) (M : Nat → Nat → Nat) : ∀ n, evalE Q M (tBack ce n) = Q ce.t - n
  | 0 => by simp [tBack, evalE]
  | n + 1 => by simp [tBack, evalE, tBack_eval ce Q M n]; omega

-- The same times read t − n at once (as core/translate.ts's step laws over several steps read them).
def tSub (ce : CycEnc) : Nat → E
  | 0 => .var ce.t
  | n + 1 => .sub (.var ce.t) (.const (n + 1))

theorem tSub_eval (ce : CycEnc) (Q : Nat → Nat) (M : Nat → Nat → Nat) : ∀ n, evalE Q M (tSub ce n) = Q ce.t - n
  | 0 => by simp [tSub, evalE]
  | n + 1 => by simp [tSub, evalE]

-- Either: one step back at a time (b), or at once.
def tAtS (tb : Bool) (ce : CycEnc) (n : Nat) : E := if tb then tBack ce n else tSub ce n

theorem tAtS_eval (tb : Bool) (ce : CycEnc) (Q : Nat → Nat) (M : Nat → Nat → Nat) (n : Nat) : evalE Q M (tAtS tb ce n) = Q ce.t - n := by
  cases tb
  · simp only [tAtS, Bool.false_eq_true, ↓reduceIte]; exact tSub_eval ce Q M n
  · simp only [tAtS, ↓reduceIte]; exact tBack_eval ce Q M n

-- The map over time of a traced variable, and of a map.
def cycVM (ce : CycEnc) (x : Nat) : Nat := ((lookup (fun p => p.1 == x) ce.vtr).map (·.2)).getD 0
def cycMM (ce : CycEnc) (m : Nat) : Nat := ((lookup (fun p => p.1 == m) ce.mtr).map (·.2)).getD 0

-- Each later request's inputs at their fresh names, read at its time (of k steps, the j-th at t − (k − j)).
def kRenσ (tb : Bool) (ce : CycEnc) (k : Nat) : Nat → List (List (Nat × Nat)) → List (Nat × E)
  | _, [] => []
  | j, r :: rs => r.map (fun p => (p.2, .get (cycVM ce p.1) (tAtS tb ce (k - j)))) ++ kRenσ tb ce k (j + 1) rs

-- The step and the carried map a fresh map name stands for.
def kMren : Nat → List (List (Nat × Nat)) → Nat → Option (Nat × Nat)
  | _, [], _ => none
  | j, r :: rs, m => match lookup (fun p => p.2 == m) r with
    | some p => some (j, p.1)
    | none => kMren (j + 1) rs m

-- `then` over the run of k steps ending at t: primed names at t, each later request's inputs at its time, the rest at
-- t − k.
def kσ (tb : Bool) (ce : CycEnc) (sl : SKStep) : List (Nat × E) :=
  sl.k.prime.map (fun q => (q.2, .get (cycVM ce q.1) (tAtS tb ce 0))) ++ kRenσ tb ce sl.k.whens.length 0 sl.k.ren
    ++ cycσ ce (tAtS tb ce sl.k.whens.length)
def kRd (tb : Bool) (ce : CycEnc) (sl : SKStep) : Nat → E → E := fun m key =>
  match lookup (fun q => q.2 == m) sl.k.primeMaps with
  | some q => .get (cycMM ce q.1) (.add (tAtS tb ce 0) (.prod key (.var ce.om)))
  | none => match kMren 0 sl.mren m with
    | some p => .get (cycMM ce p.2) (.add (tAtS tb ce (sl.k.whens.length - p.1)) (.prod key (.var ce.om)))
    | none => cycRd ce (tAtS tb ce sl.k.whens.length) m key

-- Each step's `when` at its time.
def kWhens (tb : Bool) (ce : CycEnc) (k : Nat) : Nat → List C → List C
  | _, [] => []
  | j, w :: ws => trC ce (tAtS tb ce (k - j)) w :: kWhens tb ce k (j + 1) ws

theorem kWhens_mem (tb : Bool) (ce : CycEnc) (k : Nat) : ∀ (j : Nat) (ws : List C) {c : C}, c ∈ kWhens tb ce k j ws → ∃ i, ∃ h : i < ws.length, c = trC ce (tAtS tb ce (k - (j + i))) ws[i]
  | _, [], _, h => by simp [kWhens] at h
  | j, w :: ws, c, h => by
    simp only [kWhens, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by simp, by simp⟩
    · obtain ⟨i, hi, rfl⟩ := kWhens_mem tb ce k (j + 1) ws h
      exact ⟨i + 1, by simp; omega, by simp [Nat.add_assoc, Nat.add_comm 1 i]⟩

/-- A k-step law's node, checked against the machine's encoding: the encoding fits the machine as for its laws, the
law's fresh names stand for traced inputs and state variables and the maps for maps over time, `then` and each `when`
read no added variable, flag or map over time, the conclusion is `then` over the run (`kσ`, `kRd`) and the hypotheses
are among the precondition, k ≤ t, t ≤ T, T < Ω and each step's `when` at its time. -/
def cycKOkAt (tb : Bool) (s : SMachine) (ce : CycEnc) (facts : List Fact) (sl : SKStep) (n : CNode) : Bool :=
  cycShapeOk s ce [] && cycTermsOk s ce [] && s.wits.isEmpty && cycFactsIn s ce facts
    && sl.k.ren.length == sl.k.whens.length && sl.mren.length == sl.k.whens.length
    && sl.k.ren.all (fun r => r.all fun p => s.f.m.inputs.contains p.1)
    && sl.k.prime.all (fun q => (ce.vtr.map (·.1)).contains q.1 && !s.f.m.inputs.contains q.1)
    && sl.mren.all (fun r => r.all fun p => s.carried.contains p.1 && !ce.tm.contains p.2)
    && sl.k.primeMaps.all (fun q => (ce.mtr.map (·.1)).contains q.1 && !s.carried.contains q.1 && !ce.tm.contains q.2)
    && avoids (ce.special ++ flagVars s.f.flags) sl.k.then_ && avoidsMaps ce.tm sl.k.then_
    && sl.k.whens.all (fun w => avoids (ce.special ++ flagVars s.f.flags) w && avoidsMaps ce.tm w)
    && beqC n.concl (substRC (kσ tb ce sl) (kRd tb ce sl) sl.k.then_)
    && n.hyps.all (fun h => beqC h s.f.m.pre || beqC h (.le (.const sl.k.whens.length) (.var ce.t)) || beqC h (.le (.var ce.t) (.var ce.T))
      || beqC h (.lt (.var ce.T) (.var ce.om)) || (kWhens tb ce sl.k.whens.length 0 sl.k.whens).any (beqC h))

/-! The encoding read back -/

theorem applyS_app (A B : List (Nat × E)) (Q : Nat → Nat) (M : Nat → Nat → Nat) (v : Nat) :
    applyS (A ++ B) Q M v = match assoc A v with | some e => evalE Q M e | none => applyS B Q M v := by
  simp only [applyS, assoc_append_or]; cases assoc A v <;> simp [Option.or]

theorem assoc_ren (r : List (Nat × Nat)) (g : Nat × Nat → E) (v : Nat) :
    assoc (r.map (fun p => (p.2, g p))) v = (lookup (fun p => p.2 == v) r).map g := by
  simp only [assoc, lookup_map_pred, Option.map_map]; rfl

theorem not_tgt_cons {r : List (Nat × Nat)} {rs : List (List (Nat × Nat))} {v : Nat} (hv : v ∈ tgts (r :: rs))
    (hn : lookup (fun p => p.2 == v) r = none) : v ∈ tgts rs := by
  simp only [tgts, List.mem_append] at hv
  rcases hv with h | h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    have := lookup_none_all hn p hp; simp at this
  · exact h

-- Each later request's inputs at their fresh names: the run's request at its time, as renEnv reads it.
theorem kRen_eval (tb : Bool) (ce : CycEnc) (k : Nat) (Q : Nat → Nat) (cm : Nat → Nat → Nat) (b : Nat → Nat) (rest : List (Nat × E)) :
    ∀ (rs : List (List (Nat × Nat))) (j : Nat) (ιs : List (Nat → Nat)), rs.length ≤ ιs.length →
      (∀ i (hi : i < rs.length) (hι : i < ιs.length), ∀ p ∈ rs[i], evalE Q cm (.get (cycVM ce p.1) (tAtS tb ce (k - (j + i)))) = ιs[i] p.1) →
      ∀ v, v ∈ tgts rs → applyS (kRenσ tb ce k j rs ++ rest) Q cm v = renEnv rs ιs b v
  | [], _, _, _, _, v, hv => by simp [tgts] at hv
  | _ :: _, _, [], hl, _, _, _ => by simp at hl
  | r :: rs, j, ι :: ιs, hl, hX, v, hv => by
    simp only [kRenσ, List.append_assoc]
    rw [applyS_app, assoc_ren]
    simp only [renEnv]
    cases hr : lookup (fun p => p.2 == v) r with
    | some p =>
      have h0 := hX 0 (by simp) (by simp) p (lookup_some hr).1
      simp only [Nat.add_zero, List.getElem_cons_zero] at h0
      simpa using h0
    | none =>
      simp only [Option.map_none]
      exact kRen_eval tb ce k Q cm b rest rs (j + 1) ιs (by simp at hl; omega)
        (fun i hi hι p hp => by
          have := hX (i + 1) (by simp; omega) (by simp; omega) p (by simpa using hp)
          simpa [Nat.add_assoc, Nat.add_comm 1 i] using this) v (not_tgt_cons hv hr)

theorem kRen_out (tb : Bool) (ce : CycEnc) (k : Nat) (Q : Nat → Nat) (cm : Nat → Nat → Nat) (rest : List (Nat × E)) :
    ∀ (rs : List (List (Nat × Nat))) (j : Nat) (v : Nat), v ∉ tgts rs → applyS (kRenσ tb ce k j rs ++ rest) Q cm v = applyS rest Q cm v
  | [], _, _, _ => by simp [kRenσ]
  | r :: rs, j, v, hv => by
    simp only [kRenσ, List.append_assoc]
    rw [applyS_app, assoc_ren]
    have hn : lookup (fun p => p.2 == v) r = none := lookup_none (fun p hp => by
      simp only [beq_eq_false_iff_ne]; intro he; exact hv (by simp only [tgts, List.mem_append]; exact Or.inl (List.mem_map.mpr ⟨p, hp, he⟩)))
    simp only [hn, Option.map_none]
    exact kRen_out tb ce k Q cm rest rs (j + 1) v (fun h => hv (by simp only [tgts, List.mem_append]; exact Or.inr h))

-- The maps a later request carries at their fresh names: the run's at its time, as renMaps reads them.
theorem kMren_eval : ∀ (rs : List (List (Nat × Nat))) (j : Nat) (κs : List (Nat → Nat → Nat)) (b : Nat → Nat → Nat) (m : Nat),
    rs.length ≤ κs.length →
      (kMren j rs m = none → renMaps rs κs b m = b m)
      ∧ (∀ i c, kMren j rs m = some (i, c) → ∃ (i' : Nat) (hi : i' < rs.length) (hκ : i' < κs.length), i = j + i'
          ∧ (∃ p ∈ rs[i'], p.1 = c ∧ p.2 = m) ∧ renMaps rs κs b m = κs[i'] c)
  | [], _, κs, b, m, _ => ⟨fun _ => by cases κs <;> rfl, fun _ _ h => by simp [kMren] at h⟩
  | _ :: _, _, [], _, _, hl => by simp at hl
  | r :: rs, j, κ :: κs, b, m, hl => by
    have ih := kMren_eval rs (j + 1) κs b m (by simp at hl; omega)
    cases hr : lookup (fun p => p.2 == m) r with
    | some p =>
      refine ⟨fun h => by simp [kMren, hr] at h, fun i c h => ?_⟩
      simp only [kMren, hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨0, by simp, by simp, by simp, ⟨p, by simpa using (lookup_some hr).1, rfl, by simpa using (lookup_some hr).2⟩, by simp [renMaps, hr]⟩
    | none =>
      refine ⟨fun h => ?_, fun i c h => ?_⟩
      · simp only [kMren, hr] at h; simp only [renMaps, hr]; exact ih.1 h
      · simp only [kMren, hr] at h
        obtain ⟨i', hi, hκ, rfl, hp, he⟩ := ih.2 i c h
        exact ⟨i' + 1, by simp; omega, by simp; omega, by omega, by simpa using hp, by simp [renMaps, hr, he]⟩

theorem cycVM_spec {ce : CycEnc} {x : Nat} (h : x ∈ ce.vtr.map (·.1)) : ∃ p ∈ ce.vtr, p.1 = x ∧ cycVM ce x = p.2 := by
  cases hl : lookup (fun p => p.1 == x) ce.vtr with
  | none => obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; have := lookup_none_all hl p hp; simp at this
  | some p => exact ⟨p, (lookup_some hl).1, by simpa using (lookup_some hl).2, by simp [cycVM, hl]⟩
theorem cycMM_spec {ce : CycEnc} {m : Nat} (h : m ∈ ce.mtr.map (·.1)) : ∃ p ∈ ce.mtr, p.1 = m ∧ cycMM ce m = p.2 := by
  cases hl : lookup (fun p => p.1 == m) ce.mtr with
  | none => obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; have := lookup_none_all hl p hp; simp at this
  | some p => exact ⟨p, (lookup_some hl).1, by simpa using (lookup_some hl).2, by simp [cycMM, hl]⟩

-- A traced variable's map over time, read at a time within the run: the run's state with its request there.
theorem read_vm {s : SMachine} {ce : CycEnc} {r : CRun} {om : Nat} (hd : distinct ce.tm = true) {x : Nat} (hx : x ∈ ce.vtr.map (·.1)) (u : Nat) :
    cycMaps s ce r om (cycVM ce x) u = r.X s u x := by
  obtain ⟨p, hp, rfl, he⟩ := cycVM_spec hx
  rw [he, cm_v hd hp]
-- A map's map over time, read at a time within the run and a key.
theorem read_mm {s : SMachine} {ce : CycEnc} {r : CRun} {T : Nat} (hd : distinct ce.tm = true) {m : Nat} (hm : m ∈ ce.mtr.map (·.1))
    {u : Nat} (hu : u ≤ T) (kv : Nat) : cycMaps s ce r (T + 1) (cycMM ce m) (u + kv * (T + 1)) = r.N s u m kv := by
  obtain ⟨p, hp, rfl, he⟩ := cycMM_spec hm
  rw [he, cm_m hd hp]; simp only [pair_mod hu, pair_div hu]

/-! The bridge for step laws and k-step laws -/

-- The bridge for one time form (`tAtS b`).
theorem cyc_kstep_sound_at (tb : Bool) (s : SMachine) (ce : CycEnc) (facts : List Fact) (nodes : List CNode) (hc : checkCyclic facts nodes = true)
    (sl : SKStep) (n : CNode) (hn : n ∈ nodes) (hok : cycKOkAt tb s ce facts sl n = true) : SKStepHolds s sl := by
  simp only [cycKOkAt, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsh, hte⟩, hwit⟩, hfa⟩, hrl⟩, hml⟩, hrin⟩, hpr⟩, hmr⟩, hpm⟩, hthv⟩, hthm⟩, hwh⟩, hcon⟩, hhy⟩ := hok
  have hS := cycShape_of hsh
  have hT := cycTerms_of hte
  have hW : s.wits = [] := isEmpty_nil hwit
  have hsp := special_parts hS.dsp
  intro ρ M hr q₁ qs hlen hK
  obtain ⟨r, T0, hr0, hst, hmp⟩ := reach_run hS.q hr
  obtain ⟨r', hr', _, _, _, hj, hι⟩ := run_ext hS.q (q₁ :: qs) sl.k.whens r T0 ρ M hr0 hst hmp (by simp; omega) hK
  have hk : sl.k.whens.length = (q₁ :: qs).length := by simp; omega
  -- The node's environment: t and T the run's end (the last state's time), Ω one above it, the rest from before the
  -- start.
  obtain ⟨Q, hQt, hQT, hQo, hQr⟩ : ∃ Q : Nat → Nat, Q ce.t = T0 + (q₁ :: qs).length ∧ Q ce.T = T0 + (q₁ :: qs).length ∧ Q ce.om = T0 + (q₁ :: qs).length + 1
      ∧ ∀ i, i ∉ ce.special → Q i = r'.ρ0 i :=
    ⟨fun i => if i = ce.t then T0 + (q₁ :: qs).length else if i = ce.T then T0 + (q₁ :: qs).length else if i = ce.om then T0 + (q₁ :: qs).length + 1 else r'.ρ0 i,
      by simp, by simp [Ne.symm hsp.2.2.2.2.2.1], by simp [Ne.symm hsp.2.2.2.2.2.2, Ne.symm hsp.2.2.2.2.1],
      fun i hi => by
        dsimp only
        rw [if_neg (fun e => hi (in_special (Or.inr (Or.inr (Or.inr (Or.inr e)))))), if_neg (fun e => hi (in_special (Or.inr (Or.inr (Or.inl e))))),
          if_neg (fun e => hi (in_special (Or.inr (Or.inr (Or.inr (Or.inl e))))))]⟩
  have hEnv : EnvOk s ce [] r' (T0 + (q₁ :: qs).length) Q := ⟨hQT, hQo, fun i hi => hQr i (notP hi).1⟩
  -- The state at each time, and each request at its time.
  have hst0 : r'.st T0 = ρ ∧ r'.mp T0 = M := by simpa [sEnd] using hj 0 (by simp)
  have hι0 : r'.ι T0 = q₁.1 ∧ r'.κ T0 = q₁.2 := by
    have h := hι 0 (by simp); simp only [Nat.add_zero, List.getElem_cons_zero] at h; exact h
  have hend : r'.st (T0 + (q₁ :: qs).length) = (sEnd s ρ M (q₁ :: qs)).1 ∧ r'.mp (T0 + (q₁ :: qs).length) = (sEnd s ρ M (q₁ :: qs)).2 := by
    simpa using hj (q₁ :: qs).length (Nat.le_refl _)
  have hframe : ∀ u, u ≤ T0 + (q₁ :: qs).length → ∀ i, i ∉ ce.vtr.map (·.1) → i ∉ flagVars s.f.flags → r'.st u i = r'.ρ0 i := fun u hu i hv hf =>
    run_frame hr' u hu i (fun h => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact hv (hS.initv p hp))
      (fun h => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact hv (hS.stepv p hp)) (fun h => hv (hS.inv i h)) hf
  have hw0 : evalE Q (cycMaps s ce r' (T0 + (q₁ :: qs).length + 1)) (tAtS tb ce sl.k.whens.length) = T0 := by rw [tAtS_eval tb, hQt, hk]; omega
  -- The facts hold of the run.
  have hF : FactsHold facts Q (cycMaps s ce r' (T0 + (q₁ :: qs).length + 1)) := by
    intro f hf vals
    have hfi := List.all_eq_true.mp hfa f hf
    simp only [Bool.or_eq_true] at hfi
    rcases hfi with hnc | hcan
    · exact natC_true _ hnc
    · obtain ⟨g, hg, hb⟩ := List.any_eq_true.mp hcan
      simp only [factBeq, Bool.and_eq_true, beq_iff_eq] at hb
      rw [hb.1, beqC_eq hb.2]
      exact canon_holds hS hT hr' hg hEnv vals
  -- The node's hypotheses hold there.
  have hH : ∀ c ∈ n.hyps, evalC Q (cycMaps s ce r' (T0 + (q₁ :: qs).length + 1)) c = true := by
    intro c hc
    have h := hhy c hc
    simp only [Bool.or_eq_true] at h
    rcases h with (((h | h) | h) | h) | h
    · rw [beqC_eq h, congr2C (ρ' := r'.ρ0) (M' := r'.mp 0) _ (fun j hj => hEnv.2.2 j (avoids_occ hT.prz hj))
        (fun m hm => cm_o (avoidsMaps_occ hT.prm hm))]
      exact hr'.pre
    · rw [beqC_eq h, evalC_iff]; simp only [holdsC, evalE, hQt, hk]; omega
    · rw [beqC_eq h, evalC_iff]; simp only [holdsC, evalE, hQt, hQT]; omega
    · rw [beqC_eq h, evalC_iff]; simp only [holdsC, evalE, hQT, hQo]; omega
    · obtain ⟨c', hc', hb⟩ := List.any_eq_true.mp h
      rw [beqC_eq hb]
      obtain ⟨i, hi, rfl⟩ := kWhens_mem tb ce sl.k.whens.length 0 sl.k.whens hc'
      have hiq : i < (q₁ :: qs).length := by omega
      have hu : T0 + i ≤ T0 + (q₁ :: qs).length := by omega
      have hwi : evalE Q (cycMaps s ce r' (T0 + (q₁ :: qs).length + 1)) (tAtS tb ce (sl.k.whens.length - (0 + i))) = T0 + i := by rw [tAtS_eval tb, hQt, hk]; omega
      have hall := sallowed_at (q₁ :: qs) sl.k.whens ρ M hK i hiq hi
      obtain ⟨hsti, hmpi⟩ := hj i (by omega)
      obtain ⟨hιi, hκi⟩ := hι i hiq
      have hav := hwh _ (List.getElem_mem hi)
      rw [enc_trC hS hT hr' hEnv hwi hu]
      rw [congr2C (ρ' := withExt s (sEnd s ρ M ((q₁ :: qs).take i)).1 (sReq s (sEnd s ρ M ((q₁ :: qs).take i)).1 (sEnd s ρ M ((q₁ :: qs).take i)).2 (q₁ :: qs)[i].1 (q₁ :: qs)[i].2))
        (M' := withCarried s (sEnd s ρ M ((q₁ :: qs).take i)).2 (q₁ :: qs)[i].2) _ ?_ ?_]
      · exact hall
      · intro x hx
        have hxz := avoids_occ hav.1 hx
        rw [withExt_plain hS.q hW, sReq_plain hS.q hW]
        by_cases hv : x ∈ ce.vtr.map (·.1)
        · rw [enc_σ_in hS hT hr' hEnv hwi hu hv, CRun.X, hsti, hιi]; simp only [withInputs]; split <;> rfl
        · have hxi : x ∉ s.f.m.inputs := fun h => hv (hS.inv x h)
          rw [enc_σ_out hS hT hr' hEnv hwi hu hv, if_neg (fun h => hxi (List.contains_iff_mem.mp h)), ← hsti,
            hframe _ hu x hv (fun h => hxz (List.mem_append_right _ h))]
          exact hQr x (fun h => hxz (List.mem_append_left _ h))
      · intro m hm
        rw [cv_N (avoidsMaps_occ hav.2 hm), CRun.N, hmpi, hκi]
  have hc0 := cyclic_sound facts nodes hc (cycMaps s ce r' (T0 + (q₁ :: qs).length + 1)) Q hF n hn hH
  rw [beqC_eq hcon] at hc0
  -- `then` over the run: the maps it reads, then its names.
  have hTle : T0 ≤ T0 + (q₁ :: qs).length := Nat.le_add_right _ _
  let Mt : Nat → Nat → Nat := primedMaps sl.k.primeMaps (sEnd s ρ M (q₁ :: qs)).2 (renMaps sl.mren ((q₁ :: qs).map (·.2)) (withCarried s M q₁.2))
  have hrd : ∀ m key, evalE Q (cycMaps s ce r' (T0 + (q₁ :: qs).length + 1)) (kRd tb ce sl m key)
      = (fun m => if ce.tm.contains m then cycMaps s ce r' (T0 + (q₁ :: qs).length + 1) m else Mt m) m
        (evalE Q (cycMaps s ce r' (T0 + (q₁ :: qs).length + 1)) key) := by
    intro m key
    simp only [kRd]
    cases hq : lookup (fun q => q.2 == m) sl.k.primeMaps with
    | some q =>
      obtain ⟨hqm, hqe⟩ := lookup_some hq
      have hqe' : q.2 = m := by simpa using hqe
      obtain ⟨⟨hq1, hq2⟩, hq3⟩ := hpm q hqm
      have hnt : ¬ ce.tm.contains m = true := by rw [← hqe']; simpa using hq3
      simp only [evalE, tAtS_eval tb, hQt, hQo, Nat.sub_zero]
      rw [read_mm hS.dtm (List.contains_iff_mem.mp hq1) (Nat.le_refl _), N_not_carried (by simpa using hq2), hend.2, if_neg hnt]
      simp only [Mt, primedMaps, hq]
    | none =>
      have hkm := kMren_eval sl.mren 0 ((q₁ :: qs).map (·.2)) (withCarried s M q₁.2) m (by simp; omega)
      cases hkr : kMren 0 sl.mren m with
      | some p =>
        obtain ⟨i', hi', hκ', hi0, ⟨p', hp', hp1, hp2⟩, hren⟩ := hkm.2 p.1 p.2 hkr
        obtain ⟨hcar, hnt0⟩ := hmr _ (List.getElem_mem hi') p' hp'
        have hnt : ¬ ce.tm.contains m = true := by rw [← hp2]; simpa using hnt0
        have hiq : i' < (q₁ :: qs).length := by simpa using hκ'
        obtain ⟨hιi, hκi⟩ := hι i' hiq
        simp only [evalE, tAtS_eval tb, hQt, hQo, hi0, Nat.zero_add]
        rw [show T0 + (q₁ :: qs).length - (sl.k.whens.length - i') = T0 + i' by rw [hk]; omega]
        rw [read_mm hS.dtm (hS.carm _ (by rw [← hp1]; exact List.contains_iff_mem.mp hcar)) (by omega), CRun.N, hκi, if_neg hnt]
        simp only [Mt, primedMaps, hq, hren, withCarried, ← hp1, hcar, if_true, List.getElem_map]
      | none =>
        rw [enc_rd hS hT hr' hEnv hw0 hTle]
        simp only [cycView]
        by_cases ht : ce.tm.contains m = true
        · rw [if_pos ht, if_pos ht]
        · rw [if_neg ht, if_neg ht, CRun.N, hst0.2, hι0.2]
          simp only [Mt, primedMaps, hq, hkm.1 hkr]
  rw [substR_evalC (kσ tb ce sl) (kRd tb ce sl) Q _ _ hrd] at hc0
  rw [congr2C (ρ' := primed sl.k.prime (sEnd s ρ M (q₁ :: qs)).1 (renEnv sl.k.ren (sExts s ρ M (q₁ :: qs)) (withExt s ρ (sReq s ρ M q₁.1 q₁.2))))
    (M' := Mt) _ ?_ ?_] at hc0
  · exact hc0
  · intro x hx
    have hxz := avoids_occ hthv hx
    simp only [kσ, List.append_assoc]
    rw [applyS_app, assoc_ren]
    simp only [primed]
    cases hq : lookup (fun q => q.2 == x) sl.k.prime with
    | some q =>
      obtain ⟨hqm, _⟩ := lookup_some hq
      obtain ⟨hq1, hq2⟩ := hpr q hqm
      simp only [Option.map_some, evalE, tAtS_eval tb, hQt, Nat.sub_zero]
      rw [read_vm hS.dtm (List.contains_iff_mem.mp hq1), CRun.X, withInputs_other (by simpa using hq2), hend.1]
    | none =>
      simp only [Option.map_none]
      by_cases hxr : x ∈ tgts sl.k.ren
      · rw [kRen_eval tb ce sl.k.whens.length Q _ _ _ sl.k.ren 0 (sExts s ρ M (q₁ :: qs)) (by rw [sExts_plain hS.q hW]; simp; omega) ?_ x hxr]
        intro i hi hιl p hp
        have hpin := hrin _ (List.getElem_mem hi) p hp
        have hiq : i < (q₁ :: qs).length := by rw [sExts_plain hS.q hW] at hιl; simpa using hιl
        obtain ⟨hιi, _⟩ := hι i hiq
        simp only [evalE, tAtS_eval tb, hQt, Nat.zero_add]
        rw [show T0 + (q₁ :: qs).length - (sl.k.whens.length - i) = T0 + i by rw [hk]; omega]
        rw [read_vm hS.dtm (hS.inv _ (List.contains_iff_mem.mp hpin)), CRun.X]
        simp only [withInputs, hpin, if_true, hιi]
        have hx : ∀ (l : List (Nat → Nat)), l = (q₁ :: qs).map (fun q v => if s.f.m.inputs.contains v then q.1 v else 0) →
            ∀ h : i < l.length, (q₁ :: qs)[i].1 p.1 = l[i] p.1 := by
          intro l hl h; subst hl; simp only [List.getElem_map, hpin, if_true]
        exact hx _ (sExts_plain hS.q hW _ _ _) hιl
      · rw [kRen_out tb ce sl.k.whens.length Q _ _ sl.k.ren 0 x hxr, renEnv_other _ _ _ x hxr, withExt_plain hS.q hW, sReq_plain hS.q hW]
        by_cases hv : x ∈ ce.vtr.map (·.1)
        · rw [enc_σ_in hS hT hr' hEnv hw0 hTle hv, CRun.X, hst0.1, hι0.1]; simp only [withInputs]; split <;> rfl
        · have hxi : x ∉ s.f.m.inputs := fun h => hv (hS.inv x h)
          rw [enc_σ_out hS hT hr' hEnv hw0 hTle hv, if_neg (fun h => hxi (List.contains_iff_mem.mp h)), ← hst0.1,
            hframe _ hTle x hv (fun h => hxz (List.mem_append_right _ h))]
          exact hQr x (fun h => hxz (List.mem_append_left _ h))
  · intro m hm
    simp only [if_neg (fun h => avoidsMaps_occ hthm hm (List.contains_iff_mem.mp h))]

-- A step law's node with its times either way (`cycKOkAt`).
def cycKOk (s : SMachine) (ce : CycEnc) (facts : List Fact) (sl : SKStep) (n : CNode) : Bool :=
  cycKOkAt true s ce facts sl n || cycKOkAt false s ce facts sl n

/-- A cyclic proof of a k-step law (a step law, k = 1), checked against the machine's encoding (`cycKOk`): from every
reachable state, every k requests in a row the machine allows, each meeting its `when`, end where `then` holds. -/
theorem cyc_kstep_sound (s : SMachine) (ce : CycEnc) (facts : List Fact) (nodes : List CNode) (hc : checkCyclic facts nodes = true)
    (sl : SKStep) (n : CNode) (hn : n ∈ nodes) (hok : cycKOk s ce facts sl n = true) : SKStepHolds s sl := by
  simp only [cycKOk, Bool.or_eq_true] at hok
  rcases hok with h | h
  · exact cyc_kstep_sound_at true s ce facts nodes hc sl n hn h
  · exact cyc_kstep_sound_at false s ce facts nodes hc sl n hn h

/-! Liveness from step laws -/

-- A step law Lean builds from a liveness (Live.lean's `sliveStep`), with no certificate: one `when`, its `then`, the
-- liveness's primed names.
def liveK (l : Live) (w t : C) : SKStep := ⟨⟨[w], t, [[]], l.prime, l.primeMaps, [], ([], .leaf [] [] [] [])⟩, [[]], [], [], [], [], [], []⟩

/-- Liveness under fairness from its step laws: if the liveness reads what it may (`sliveOk`) and the step laws Lean
builds from it hold (`SKStepHolds`, a cyclic proof's through `cyc_kstep_sound`), then along every run that takes each
helpful request infinitely often, each state where `from` holds is followed by one where `to` holds. `sleads_sound`
with the step laws' meaning in place of their certificates. -/
theorem sleads_of_holds (s : SMachine) (l : Live) (hok : sliveOk s l = true)
    (hs : SKStepHolds s (liveK l l.pend (liveStayC l))) (hc : SKStepHolds s (liveK l l.pend (liveCoverC l)))
    (hh : ∀ h ∈ l.helps, SKStepHolds s (liveK l (liveHelpWhen l h) (liveHelpThen l))) (run : SRun s)
    (fair : ∀ h ∈ l.helps, ∀ n, ∃ m, n ≤ m ∧ ∀ p ∈ h.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 l.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 l.to = true := by
  have hok0 := hok
  simp only [sliveOk, Bool.and_eq_true, List.all_eq_true] at hok0
  obtain ⟨⟨⟨hd1, hd2⟩, _⟩, hreqs⟩ := hok0
  refine leads_view l run.st (fun n => withExt s (run.st n).1 (sReq s (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2))
    (fun n => primed l.prime (run.st (n + 1)).1 (withExt s (run.st n).1 (sReq s (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2)))
    (fun n => withCarried s (run.st n).2 (run.req n).2) (fun n => primedMaps l.primeMaps (run.st (n + 1)).2 (withCarried s (run.st n).2 (run.req n).2))
    (fun h n => ∀ p ∈ h.2, (run.req n).1 p.1 = evalE (run.st n).1 (run.st n).2 p.2) (fun _ _ => True) ?_ ?_ ?_ ?_ ?_ ?_
    (fun _ _ _ _ _ _ => trivial) (fun h hh n _ => fair h hh n)
  · intro n c hc
    obtain ⟨hv, hm, hx, hn⟩ := slive_reads hok hc (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2
    rw [run.next n]
    exact view_C hd1 hd2 hv hm hx hn
  · intro n e he
    obtain ⟨hv, hm, hx, hn⟩ := slive_reads hok (mem_conds_rank he) (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2
    rw [run.next n]
    exact view_E hd1 hd2 hv hm hx hn
  · intro n hB
    have := skstep_holds_one hs rfl rfl rfl _ _ (srun_reach run n) _ _ (run.allowed n) hB
    rw [run.next n]; exact this
  · intro n hB
    have := skstep_holds_one hc rfl rfl rfl _ _ (srun_reach run n) _ _ (run.allowed n) hB
    rw [run.next n]; exact this
  · intro h hmem n hB
    have := skstep_holds_one (hh h hmem) rfl rfl rfl _ _ (srun_reach run n) _ _ (run.allowed n) hB
    rw [run.next n]; exact this
  · intro h hmem n hH
    show evalC (withExt s (run.st n).1 (sReq s (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2)) (withCarried s (run.st n).2 (run.req n).2) (reqC h.2) = true
    exact sreq_list (fun p hp => hreqs h hmem p hp) (fun p hp' => hH p hp')

/-! Histories through their plain machine -/

/-- A machine with a history reaches only states its plain machine reaches, once the record goals and the history's
side conditions check (`checkHMachine` with no laws: `histOk`, the record goals, the plain machine's own conditions). -/
theorem hreach_plain (h : HMachine) (rs : List (List VDef × Tree)) (hc : checkHMachine h [] rs = true) :
    ∀ ρ M hist, HReach h ρ M hist → SReach h.plain ρ M := by
  simp only [checkHMachine, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨hok, hlen⟩, hgoals⟩, hsm⟩ := hc
  have hrs : ∀ r ∈ h.rels, ∃ tt : List VDef × Tree, checkGoal ⟨tt.1, recordGoal h r⟩ tt.2 = true := by
    intro r hr
    obtain ⟨tt, htt⟩ := zip_mem_left h.rels rs hlen.symm r hr
    exact ⟨tt, hgoals (r, tt) htt⟩
  intro ρ M hist hr
  exact hreach_sreach [] (histOk_sound hok) hrs hsm hr

/-! Ghosts -/

/-- A law of a ghosted machine (a cyclic proof's, as `cyc_machine_sound` states it) that reads no ghost holds in every
reachable state of the original, at every value of its keys. -/
theorem cyc_ghost_holds (g : SGhosted) (hg : sghostOk g = true) (law : C) (keys : List Nat) (hav : avoids g.vars law = true)
    (hl : ∀ ρ M, SReach g.full ρ M → ∀ ρ' : Nat → Nat, (∀ i, i ∉ keys → ρ' i = ρ i) → evalC ρ' M law = true) :
    ∀ ρ M, SReach g.orig ρ M → ∀ ρ' : Nat → Nat, (∀ i, i ∉ keys → ρ' i = ρ i) → evalC ρ' M law = true := by
  intro ρ M hr ρ' hρ'
  obtain ⟨ρg, hrg, hag⟩ := sghost_reach g hg hr
  have h := hl ρg M hrg (fun i => if keys.contains i then ρ' i else ρg i) (fun i hi => by
    rw [if_neg (fun h => hi (List.contains_iff_mem.mp h))])
  rw [congrC _ ρ' M law (fun i hi => by
    by_cases hk : keys.contains i = true
    · rw [if_pos hk]
    · rw [if_neg hk, hag i (avoids_occ hav hi), hρ' i (fun h => hk (List.contains_iff_mem.mpr h))])] at h
  exact h

/-! A helpful request allowed, and liveness under weak fairness -/

/-- A request allowed: from every reachable state, every request that meets `w`, carrying empty sets, is one the
machine allows (its assumption holds, the flags decided): what `sallow_sound` proves of the usual certificate. -/
def AllowHolds (s : SMachine) (w : C) : Prop :=
  ∀ ρ M, SReach s ρ M → ∀ ι, evalC (withExt s ρ (sReq s ρ M ι noSets)) (withCarried s M noSets) w = true →
    evalC (sView s ρ M ι noSets).1 (sView s ρ M ι noSets).2 s.f.m.assume = true

-- A carried map's cell at time t, 0: the request at t carries empty sets.
def cycZeroOk (s : SMachine) (ce : CycEnc) : C → Bool
  | .eq (.get m (.add (.var a) (.prod _ (.var b)))) (.const 0) => a == ce.t && b == ce.om && s.carried.any (fun c => cycMM ce c == m)
  | _ => false

/-- A request allowed, as a node at time t over the machine's encoding: the request taken at t (the run's last, which no
step reads) is the one the claim is about. The node's conclusion is the assumption at t, flags inlined; its hypotheses
among the precondition, t ≤ T, T < Ω, `w` at t, and a carried map's cell at t being 0. -/
def cycAOk (s : SMachine) (ce : CycEnc) (facts : List Fact) (w : C) (n : CNode) : Bool :=
  cycShapeOk s ce [] && cycTermsOk s ce [] && s.wits.isEmpty && cycFactsIn s ce facts
    && avoids (ce.special ++ flagVars s.f.flags) w && avoidsMaps ce.tm w
    && beqC n.concl (trC ce (.var ce.t) (inlineC s.f.flags s.f.m.assume))
    && n.hyps.all (fun h => beqC h s.f.m.pre || beqC h (.le (.var ce.t) (.var ce.T)) || beqC h (.lt (.var ce.T) (.var ce.om))
      || beqC h (trC ce (.var ce.t) w) || cycZeroOk s ce h)

theorem cycZeroOk_spec {s : SMachine} {ce : CycEnc} {h : C} (hz : cycZeroOk s ce h = true) :
    ∃ c key, c ∈ s.carried ∧ h = .eq (.get (cycMM ce c) (.add (.var ce.t) (.prod key (.var ce.om)))) (.const 0) := by
  match h, hz with
  | .eq (.get m (.add (.var a) (.prod key (.var b)))) (.const 0), hz =>
    simp only [cycZeroOk, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at hz
    obtain ⟨⟨rfl, rfl⟩, c, hc, hm⟩ := hz
    exact ⟨c, key, hc, by rw [hm]⟩

/-- A cyclic proof of a request's being allowed, checked against the machine's encoding (`cycAOk`). -/
theorem cyc_allow_sound (s : SMachine) (ce : CycEnc) (facts : List Fact) (nodes : List CNode) (hc : checkCyclic facts nodes = true)
    (w : C) (n : CNode) (hn : n ∈ nodes) (hok : cycAOk s ce facts w n = true) : AllowHolds s w := by
  simp only [cycAOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hsh, hte⟩, hwit⟩, hfa⟩, hwv⟩, hwm⟩, hcon⟩, hhy⟩ := hok
  have hS := cycShape_of hsh
  have hT := cycTerms_of hte
  have hW : s.wits = [] := isEmpty_nil hwit
  have hsp := special_parts hS.dsp
  intro ρ M hr ι hw
  obtain ⟨r, T, hr0, hst, hmp⟩ := reach_run hS.q hr
  -- The run with the request at T (the last, which no step takes) the claim's, carrying empty sets.
  let r2 : CRun := ⟨r.ρ0, r.st, r.mp, fun u => if u = T then ι else r.ι u, fun u => if u = T then noSets else r.κ u⟩
  have hNX : ∀ u, u < T → r2.N s u = r.N s u ∧ r2.V s u = r.V s u := fun u hu => by
    have hne : u ≠ T := Nat.ne_of_lt hu
    refine ⟨?_, ?_⟩ <;> simp only [CRun.V, CRun.X, CRun.N, r2, if_neg hne]
  have hr2 : r2.Ok s T := ⟨hr0.maps0, hr0.pre, hr0.facts, hr0.pfacts, hr0.init, fun u hu => by
    rw [(hNX u hu).1, (hNX u hu).2]; exact hr0.step u hu⟩
  have hX : r2.X s T = withInputs s.f.m.inputs ρ ι := by simp only [CRun.X, r2, if_pos rfl, hst, if_true]
  have hN : r2.N s T = withCarried s M noSets := by simp only [CRun.N, r2, if_pos rfl, hmp, if_true]
  obtain ⟨Q, hQt, hQT, hQo, hQr⟩ : ∃ Q : Nat → Nat, Q ce.t = T ∧ Q ce.T = T ∧ Q ce.om = T + 1 ∧ ∀ i, i ∉ ce.special → Q i = r.ρ0 i :=
    ⟨fun i => if i = ce.t then T else if i = ce.T then T else if i = ce.om then T + 1 else r.ρ0 i,
      by simp, by simp [Ne.symm hsp.2.2.2.2.2.1], by simp [Ne.symm hsp.2.2.2.2.2.2, Ne.symm hsp.2.2.2.2.1],
      fun i hi => by
        dsimp only
        rw [if_neg (fun e => hi (in_special (Or.inr (Or.inr (Or.inr (Or.inr e)))))), if_neg (fun e => hi (in_special (Or.inr (Or.inr (Or.inl e))))),
          if_neg (fun e => hi (in_special (Or.inr (Or.inr (Or.inr (Or.inl e))))))]⟩
  have hEnv : EnvOk s ce [] r2 T Q := ⟨hQT, hQo, fun i hi => hQr i (notP hi).1⟩
  have hwt : evalE Q (cycMaps s ce r2 (T + 1)) (.var ce.t) = T := by simp [evalE, hQt]
  have hF : FactsHold facts Q (cycMaps s ce r2 (T + 1)) := by
    intro f hf vals
    have hfi := List.all_eq_true.mp hfa f hf
    simp only [Bool.or_eq_true] at hfi
    rcases hfi with hnc | hcan
    · exact natC_true _ hnc
    · obtain ⟨g, hg, hb⟩ := List.any_eq_true.mp hcan
      simp only [factBeq, Bool.and_eq_true, beq_iff_eq] at hb
      rw [hb.1, beqC_eq hb.2]
      exact canon_holds hS hT hr2 hg hEnv vals
  have hH : ∀ c ∈ n.hyps, evalC Q (cycMaps s ce r2 (T + 1)) c = true := by
    intro c hc
    have h := hhy c hc
    simp only [Bool.or_eq_true] at h
    rcases h with ((((h | h) | h) | h) | h)
    · rw [beqC_eq h, congr2C (ρ' := r2.ρ0) (M' := r2.mp 0) _ (fun j hj => hEnv.2.2 j (avoids_occ hT.prz hj))
        (fun m hm => cm_o (avoidsMaps_occ hT.prm hm))]
      exact hr2.pre
    · rw [beqC_eq h, evalC_iff]; simp only [holdsC, evalE, hQt, hQT]; omega
    · rw [beqC_eq h, evalC_iff]; simp only [holdsC, evalE, hQT, hQo]; omega
    · rw [beqC_eq h, enc_trC hS hT hr2 hEnv hwt (Nat.le_refl T)]
      rw [congr2C (ρ' := withExt s ρ (sReq s ρ M ι noSets)) (M' := withCarried s M noSets) _ ?_ ?_]
      · exact hw
      · intro x hx
        have hxz := avoids_occ hwv hx
        rw [withExt_plain hS.q hW, sReq_plain hS.q hW]
        by_cases hv : x ∈ ce.vtr.map (·.1)
        · rw [enc_σ_in hS hT hr2 hEnv hwt (Nat.le_refl T) hv, hX]; simp only [withInputs]; split <;> rfl
        · have hxi : x ∉ s.f.m.inputs := fun h => hv (hS.inv x h)
          rw [enc_σ_out hS hT hr2 hEnv hwt (Nat.le_refl T) hv, if_neg (fun h => hxi (List.contains_iff_mem.mp h)), ← hst,
            run_frame hr0 T (Nat.le_refl T) x (fun h => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact hv (hS.initv p hp))
              (fun h => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact hv (hS.stepv p hp)) hxi (fun h => hxz (List.mem_append_right _ h))]
          exact hQr x (fun h => hxz (List.mem_append_left _ h))
      · intro m hm
        rw [cv_N (avoidsMaps_occ hwm hm), hN]
    · obtain ⟨cm, key, hcm, rfl⟩ := cycZeroOk_spec h
      rw [evalC_iff]
      simp only [holdsC, evalE, hQt, hQo]
      rw [read_mm hS.dtm (hS.carm cm hcm) (Nat.le_refl T), hN]
      simp only [withCarried, List.contains_iff_mem.mpr hcm, if_true, noSets]
  have hc0 := cyclic_sound facts nodes hc (cycMaps s ce r2 (T + 1)) Q hF n hn hH
  rw [beqC_eq hcon, enc_nowC hS hT hr2 hEnv hwt (Nat.le_refl T) s.f.m.assume hT.asz hT.asm] at hc0
  have hv : sView s ρ M ι noSets = (r2.V s T, r2.N s T) := by
    simp only [sView, decideQ_nil hS.q, CRun.V, hX, hN]
  rw [hv]; exact hc0

/-- Liveness under weak fairness from its step laws and its helpful requests allowed: `sleads_wf_sound` with the step
laws' meaning (`SKStepHolds`) and each helpful request's being allowed in its region, with its named inputs and a
witness for the rest, carrying empty sets (`AllowHolds`, a cyclic proof's through `cyc_allow_sound`), in place of their
certificates. -/
theorem sleads_wf_of_holds (s : SMachine) (l : Live) (hok : sliveOk s l = true)
    (hs : SKStepHolds s (liveK l l.pend (liveStayC l))) (hc : SKStepHolds s (liveK l l.pend (liveCoverC l)))
    (hh : ∀ h ∈ l.helps, SKStepHolds s (liveK l (liveHelpWhen l h) (liveHelpThen l)))
    (ha : ∀ h ∈ l.helps, ∃ wit : List (Nat × E), distinct ((h.2 ++ wit).map (·.1)) = true
      ∧ (∀ p ∈ wit, (s.f.m.inputs.contains p.1 = true ∧ avoids s.extVars (.eq p.2 p.2) = true) ∧ avoidsMaps s.carried (.eq p.2 p.2) = true)
      ∧ AllowHolds s (.and (liveHelpWhen l h) (reqC wit))) (run : SRun s)
    (fair : ∀ h ∈ l.helps, ∀ n, (∀ m, n ≤ m → ∃ ι κ, (∀ p ∈ h.2, ι p.1 = evalE (run.st m).1 (run.st m).2 p.2)
        ∧ evalC (sView s (run.st m).1 (run.st m).2 ι κ).1 (sView s (run.st m).1 (run.st m).2 ι κ).2 s.f.m.assume = true) →
      ∃ m, n ≤ m ∧ ∀ p ∈ h.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 l.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 l.to = true := by
  have hok0 := hok
  simp only [sliveOk, Bool.and_eq_true, List.all_eq_true] at hok0
  obtain ⟨⟨⟨hd1, hd2⟩, _⟩, hreqs⟩ := hok0
  refine leads_view l run.st (fun n => withExt s (run.st n).1 (sReq s (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2))
    (fun n => primed l.prime (run.st (n + 1)).1 (withExt s (run.st n).1 (sReq s (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2)))
    (fun n => withCarried s (run.st n).2 (run.req n).2) (fun n => primedMaps l.primeMaps (run.st (n + 1)).2 (withCarried s (run.st n).2 (run.req n).2))
    (fun h n => ∀ p ∈ h.2, (run.req n).1 p.1 = evalE (run.st n).1 (run.st n).2 p.2)
    (fun h m => ∃ ι κ, (∀ p ∈ h.2, ι p.1 = evalE (run.st m).1 (run.st m).2 p.2)
        ∧ evalC (sView s (run.st m).1 (run.st m).2 ι κ).1 (sView s (run.st m).1 (run.st m).2 ι κ).2 s.f.m.assume = true) ?_ ?_ ?_ ?_ ?_ ?_ ?_ fair
  · intro n c hc
    obtain ⟨hv, hm, hx, hn⟩ := slive_reads hok hc (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2
    rw [run.next n]
    exact view_C hd1 hd2 hv hm hx hn
  · intro n e he
    obtain ⟨hv, hm, hx, hn⟩ := slive_reads hok (mem_conds_rank he) (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2
    rw [run.next n]
    exact view_E hd1 hd2 hv hm hx hn
  · intro n hB
    have := skstep_holds_one hs rfl rfl rfl _ _ (srun_reach run n) _ _ (run.allowed n) hB
    rw [run.next n]; exact this
  · intro n hB
    have := skstep_holds_one hc rfl rfl rfl _ _ (srun_reach run n) _ _ (run.allowed n) hB
    rw [run.next n]; exact this
  · intro h hmem n hB
    have := skstep_holds_one (hh h hmem) rfl rfl rfl _ _ (srun_reach run n) _ _ (run.allowed n) hB
    rw [run.next n]; exact this
  · intro h hmem n hH
    show evalC (withExt s (run.st n).1 (sReq s (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2)) (withCarried s (run.st n).2 (run.req n).2) (reqC h.2) = true
    exact sreq_holds hok hmem (fun p hp' => hH p hp')
  · -- Enabled in its region: the request with its named inputs as its terms, the rest as the state has them, carrying
    -- empty sets.
    intro h hmem n hP hnQ hW
    obtain ⟨wit, hdist, hwit, hA⟩ := ha h hmem
    let ρ := (run.st n).1
    let M := (run.st n).2
    let ι := applyS (h.2 ++ wit) ρ M
    have hιp : ∀ p ∈ h.2, ι p.1 = evalE ρ M p.2 := fun p hp' => by
      simp only [ι, applyS, assoc_distinct hdist (List.mem_append_left _ hp')]
    have hιw : ∀ p ∈ wit, ι p.1 = evalE ρ M p.2 := fun p hp' => by
      simp only [ι, applyS, assoc_distinct hdist (List.mem_append_right _ hp')]
    have hX : ∀ c ∈ liveConds l, evalC (withExt s ρ (sReq s ρ M ι noSets)) (withCarried s M noSets) c = evalC ρ M c := fun c hc' => by
      obtain ⟨_, _, hx', hn'⟩ := slive_reads hok hc' ρ M ι noSets
      rw [congrMC _ _ M c hn']; exact congrC _ _ M c hx'
    have memF : l.from_ ∈ liveConds l := by simp [liveConds]
    have memT : l.to ∈ liveConds l := by simp [liveConds]
    have memH : h.1 ∈ liveConds l := by simp only [liveConds, List.mem_append, List.mem_map]; exact Or.inr ⟨h, hmem, rfl⟩
    refine ⟨ι, noSets, hιp, hA ρ M (srun_reach run n) ι ?_⟩
    simp only [liveHelpWhen, Live.pend, evalC, Bool.and_eq_true, Bool.not_eq_true']
    rw [hX _ memF, hX _ memT, hX _ memH]
    exact ⟨⟨⟨hP, hnQ⟩, hW, sreq_holds hok hmem hιp⟩, sreq_list (fun p hp' => hwit p hp') hιw⟩

/-! Refinements from their laws and step law -/

-- A step law's certificate where none is read (SKStepHolds reads no certificate).
def noSProof : SProof := ([], [], [], [], [], ([], [], .leaf [] [] [] []))

/-- What a refinement over sets means, from the meaning of its claims (`srefines` with them in place of their
certificates): with a property `P` of every reachable state of the composite (its laws, a cyclic proof's), the spec's
precondition holding there, and the composite's step law that the spec stutters or allows every request it is sent
(`SKStepHolds`, a cyclic proof's through `cyc_kstep_sound`), every reachable state of the implementation is, outside the
spec's part, a reachable state of the composite where `P` holds, whose spec part is a reachable state of the spec. -/
theorem srefines_of_holds (r : SRefined) (hok : srOk r = true) (hmo : distinct (r.spec.f.m.maps0.map (·.1)) = true)
    (P : (Nat → Nat) → (Nat → Nat → Nat) → Prop) (hlaws : ∀ ρ M, SReach r.full ρ M → P ρ M)
    (hpre : ∀ ρ M, SReach r.full ρ M → evalC ρ M r.spec.f.m.pre = true)
    (prime primeMaps : List (Nat × Nat)) (p : SProof) (hs : SKStepHolds r.full (srStep r prime primeMaps p))
    (hfresh : avoids (prime.map (·.2)) r.allowed = true ∧ avoidsMaps (primeMaps.map (·.2)) r.allowed = true)
    (hw : avoids r.full.wVars r.allowed = true) (hiq : r.full.f.m.inputs.all (fun i => !r.full.qVars.contains i) = true) :
    ∀ ρ M, SReach r.impl ρ M → ∃ ρc Mc σ Ms, SReach r.full ρc Mc ∧ Agree r.SV ρc ρ ∧ (∀ mp, mp ∉ r.SM → Mc mp = M mp)
      ∧ SReach r.spec σ Ms ∧ Agree r.X σ ρc ∧ (∀ mp, mp ∉ r.IM → mp ∉ r.spec.carried → Ms mp = Mc mp) ∧ P ρc Mc := by
  have hiq' : ∀ i, i ∈ r.full.f.m.inputs → i ∉ r.full.qVars := fun i hi hq => by
    simp only [List.all_eq_true, Bool.not_eq_true'] at hiq
    have := hiq i hi; rw [List.contains_iff_mem.mpr hq] at this; cases this
  have hallow : ∀ ρ M, SReach r.full ρ M → ∀ ι κ, evalC (sView r.full ρ M ι κ).1 (sView r.full ρ M ι κ).2 r.full.f.m.assume = true →
      evalC (sView r.full ρ M ι κ).1 (sView r.full ρ M ι κ).2 (.or r.stutter (substC r.wit r.spec.f.m.assume)) = true := by
    intro ρ M hr ι κ hA
    have h := hs ρ M hr (ι, κ) [] rfl ⟨hA, by simp [trueC, evalC, evalE], trivial⟩
    have h' : evalC (primed prime (sNext r.full ρ M ι κ).1 (withExt r.full ρ (sReq r.full ρ M ι κ)))
        (primedMaps primeMaps (sNext r.full ρ M ι κ).2 (withCarried r.full M κ)) r.allowed = true := by
      simpa [srStep, sEnd, sExts, renEnv, renMaps, lookup] using h
    rw [unprimed_evalC hfresh.1 hfresh.2] at h'
    -- The request's extended variables, read as the step reads them: the inputs, and each quantified flag decided.
    have hE : ∀ v, v ∉ r.full.wVars → withExt r.full ρ (sReq r.full ρ M ι κ) v
        = decideQ r.full (withInputs r.full.f.m.inputs ρ ι) (withCarried r.full M κ) v := by
      intro v hv
      simp only [withExt, sReq]
      by_cases hi : v ∈ r.full.f.m.inputs
      · have hext : r.full.extVars.contains v = true := List.contains_iff_mem.mpr (by simp [SMachine.extVars, hi])
        rw [decideQ_other (hiq' v hi)]
        simp only [hext, if_true, List.contains_iff_mem.mpr hi, withInputs]
      · have hin : r.full.f.m.inputs.contains v = false := by simpa [List.contains_iff_mem] using hi
        by_cases hq : v ∈ r.full.qVars
        · have hext : r.full.extVars.contains v = true := List.contains_iff_mem.mpr (by simp [SMachine.extVars, hq])
          obtain ⟨q, hq0, rfl⟩ := List.mem_map.mp hq
          cases hl : lookup (fun q' => q'.1 == q.1) r.full.qflags with
          | none => have := lookup_none_all hl q hq0; simp at this
          | some q' => simp only [hext, if_true, hin, Bool.false_eq_true, if_false, hl]
        · have hext : r.full.extVars.contains v = false := by
            simp only [SMachine.extVars, List.contains_iff_mem, List.mem_append, not_or]
            simpa [List.contains_iff_mem] using (⟨hi, hq, hv⟩ : v ∉ r.full.f.m.inputs ∧ v ∉ r.full.qVars ∧ v ∉ r.full.wVars)
          rw [decideQ_other hq, withInputs_other hi]
          simp only [hext, Bool.false_eq_true, if_false]
    rw [congrC _ _ _ r.allowed (fun i hi => hE i (avoids_occ hw hi))] at h'
    simp only [SRefined.allowed] at h'
    rw [inline_evalC] at h'
    exact h'
  intro ρ M hr
  obtain ⟨ρc, Mc, hrc, hag, hmag⟩ := srefine_lift r hok hmo hr
  obtain ⟨σ, Ms, hrs, hags, hmags⟩ := srefine_project r hok hpre hallow hrc
  exact ⟨ρc, Mc, σ, Ms, hrc, hag, hmag, hrs, hags, hmags, hlaws ρc Mc hrc⟩

/-! Flags that hold at every key -/

-- The machine with its quantified flags and their witnesses as inputs a request names: no flag holds at every key in
-- it. A request of the machine is one of its, the flags decided and the witnesses chosen as a goal reads them (`sReq`).
def SMachine.sk (s : SMachine) : SMachine :=
  ⟨⟨⟨s.extVars, s.f.m.init, s.f.m.maps0, s.f.m.step, s.f.m.writes, s.f.m.pre, s.f.m.assume⟩, s.f.flags⟩, s.carried, s.every, [], [], s.facts, s.pfacts⟩

section sk
variable {s : SMachine}

theorem sk_q : s.sk.qflags = [] := rfl
theorem sk_inputs : s.sk.f.m.inputs = s.extVars := rfl

-- sReq reads the request's inputs alone (and the state where the flags' bodies read it, off the witnesses).
theorem sReq_inputs {ρ : Nat → Nat} {M : Nat → Nat → Nat} {ι ι' : Nat → Nat} {κ : Nat → Nat → Nat}
    (h : ∀ v ∈ s.f.m.inputs, ι' v = ι v) : sReq s ρ M ι' κ = sReq s ρ M ι κ := by
  have hw : withInputs s.f.m.inputs ρ ι' = withInputs s.f.m.inputs ρ ι := by
    funext v; simp only [withInputs]; split
    · rename_i hv; exact h v (List.contains_iff_mem.mp hv)
    · rfl
  funext v; simp only [sReq, hw]; split
  · rename_i hv; exact h v (List.contains_iff_mem.mp hv)
  · rfl

theorem sReq_input {ρ : Nat → Nat} {M : Nat → Nat → Nat} {ι : Nat → Nat} {κ : Nat → Nat → Nat} {v : Nat} (hv : v ∈ s.f.m.inputs) :
    sReq s ρ M ι κ v = ι v := by simp only [sReq]; rw [if_pos (List.contains_iff_mem.mpr hv)]

theorem sReq_idem (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    sReq s ρ M (sReq s ρ M ι κ) κ = sReq s ρ M ι κ := sReq_inputs (fun _ hv => sReq_input hv)

-- The flags' bodies read no witness, so states that agree off the witnesses decide them alike.
theorem decideQ_agree (hs : sOk s = true) {X X' : Nat → Nat} (hag : Agree s.wVars X' X) (N : Nat → Nat → Nat) :
    Agree s.wVars (decideQ s X' N) (decideQ s X N) := by
  obtain ⟨_, _, _, _, _, hbody, _⟩ := sOk_parts s hs
  intro v hv
  simp only [decideQ]
  cases hl : lookup (fun q => q.1 == v) s.qflags with
  | none => exact hag v hv
  | some q =>
    have hq := (lookup_some hl).1
    have hb : ∀ k, holdsC (atKeys X' q.2.1 k) N q.2.2 = holdsC (atKeys X q.2.1 k) N q.2.2 := fun k => propext (by
      rw [← evalC_iff, ← evalC_iff, congrC _ (atKeys X q.2.1 k) N q.2.2 (fun j hj => by
        simp only [atKeys]; split
        · rfl
        · exact hag j (fun h => avoids_occ (hbody q hq).1 hj (List.mem_append_left _ (List.mem_append_right _ h))))])
    have hiff : (∀ k, holdsC (atKeys X' q.2.1 k) N q.2.2) ↔ (∀ k, holdsC (atKeys X q.2.1 k) N q.2.2) :=
      forall_congr' (fun k => by rw [hb k])
    dsimp only
    by_cases h1 : ∀ k, holdsC (atKeys X q.2.1 k) N q.2.2
    · rw [if_pos (hiff.mpr h1), if_pos h1]
    · rw [if_neg (fun h => h1 (hiff.mp h)), if_neg h1]

theorem choose_congr {α : Type} {p q : α → Prop} (h : p = q) (hp : ∃ x, p x) (hq : ∃ x, q x) : Classical.choose hp = Classical.choose hq := by
  subst h; rfl

theorem witnessKeys_agree (hs : sOk s = true) {X X' : Nat → Nat} (hag : Agree s.wVars X' X) (N : Nat → Nat → Nat) {q : Nat × List Nat × C}
    (hq : q ∈ s.qflags) : witnessKeys X' N q = witnessKeys X N q := by
  obtain ⟨_, _, _, _, _, hbody, _⟩ := sOk_parts s hs
  have hb : ∀ k, holdsC (atKeys X' q.2.1 k) N q.2.2 = holdsC (atKeys X q.2.1 k) N q.2.2 := fun k => propext (by
    rw [← evalC_iff, ← evalC_iff, congrC _ (atKeys X q.2.1 k) N q.2.2 (fun j hj => by
      simp only [atKeys]; split
      · rfl
      · exact hag j (fun h => avoids_occ (hbody q hq).1 hj (List.mem_append_left _ (List.mem_append_right _ h))))])
  have hP : (fun k => holdsC (atKeys X' q.2.1 k) N q.2.2) = (fun k => holdsC (atKeys X q.2.1 k) N q.2.2) := funext hb
  have hp2 : (fun k => ¬holdsC (atKeys X' q.2.1 k) N q.2.2) = (fun k => ¬holdsC (atKeys X q.2.1 k) N q.2.2) := funext fun k => by rw [hb k]
  unfold witnessKeys
  split
  · rename_i h1
    have h2 : ∃ k, ¬holdsC (atKeys X q.2.1 k) N q.2.2 := by obtain ⟨k, hk⟩ := h1; exact ⟨k, by rwa [← hb k]⟩
    rw [dif_pos h2]
    exact choose_congr hp2 h1 h2
  · rename_i h1
    have h2 : ¬∃ k, ¬holdsC (atKeys X q.2.1 k) N q.2.2 := fun ⟨k, hk⟩ => h1 ⟨k, by rwa [hb k]⟩
    rw [dif_neg h2]

theorem sReq_agree (hs : sOk s = true) {ρ ρ' : Nat → Nat} (hag : Agree s.wVars ρ' ρ) (M : Nat → Nat → Nat) (ι : Nat → Nat)
    (κ : Nat → Nat → Nat) : sReq s ρ' M ι κ = sReq s ρ M ι κ := by
  have hX : Agree s.wVars (withInputs s.f.m.inputs ρ' ι) (withInputs s.f.m.inputs ρ ι) := fun v hv => by
    simp only [withInputs]; split
    · rfl
    · exact hag v hv
  funext v
  simp only [sReq]
  split
  · rfl
  · split
    · rename_i q hq
      exact decideQ_agree hs hX _ v (fun h => (ext_apart s hs).2 v (by
        have := (lookup_some hq); simp only [beq_iff_eq] at this; rw [← this.2]; exact List.mem_map_of_mem this.1) h)
    · split
      · split
        · rename_i q hq
          split
          · rw [witnessKeys_agree hs hX _ (lookup_some hq).1]
          · rfl
        · rfl
      · rfl

-- A machine's request read by its sk machine: the view is the goal's view, which agrees with the machine's off the
-- witnesses.
theorem sk_inputsView (ρ ρ' : Nat → Nat) (hag : Agree s.wVars ρ' ρ) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    withInputs s.sk.f.m.inputs ρ' (sReq s ρ M ι κ) = withExt s ρ (sReq s ρ M ι κ) := by
  funext v
  simp only [withInputs, withExt, sk_inputs]
  by_cases hv : s.extVars.contains v = true
  · simp only [hv, ↓reduceIte]
  · simp only [hv, Bool.false_eq_true, ↓reduceIte]
    exact hag v (fun h => hv (by simp only [SMachine.extVars, List.contains_iff_mem, List.mem_append]; exact Or.inr h))

theorem sk_view (hs : sOk s = true) {ρ ρ' : Nat → Nat} (hag : Agree s.wVars ρ' ρ) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    Agree s.wVars (sView s.sk ρ' M (sReq s ρ M ι κ) κ).1 (sView s ρ M ι κ).1 ∧ (sView s.sk ρ' M (sReq s ρ M ι κ) κ).2 = (sView s ρ M ι κ).2 := by
  obtain ⟨hfl, _, _, _, _, _, hflw⟩ := sOk_parts s hs
  refine ⟨fun i hi => ?_, rfl⟩
  simp only [sView]
  rw [decideQ_nil sk_q, sk_inputsView ρ ρ' hag]
  exact decide_view (Z := s.wVars) (TM := []) hfl hflw (fun _ _ => rfl) (fun j hj _ => (view_agree s ρ M ι κ hs j hj).symm)
    (fun _ _ => rfl) hi

-- Inlining the flags keeps every variable a term reads but the flags'.
mutual
theorem occE_inline (fl : List (Nat × C)) {i : Nat} (hi : flagOf fl i = none) : ∀ e : E, occE i e = true → occE i (inlineE fl e) = true
  | .var j, h => by
    have hj : j = i := by simpa [occE] using h
    subst hj; simp [inlineE, hi, occE]
  | .const _, h => by simp [occE] at h
  | .add a b, h => by
    simp only [occE, Bool.or_eq_true] at h; simp only [inlineE, occE, Bool.or_eq_true]
    exact h.imp (occE_inline fl hi a) (occE_inline fl hi b)
  | .sub a b, h => by
    simp only [occE, Bool.or_eq_true] at h; simp only [inlineE, occE, Bool.or_eq_true]
    exact h.imp (occE_inline fl hi a) (occE_inline fl hi b)
  | .mul _ a, h => by simp only [occE] at h; simp only [inlineE, occE]; exact occE_inline fl hi a h
  | .min a b, h => by
    simp only [occE, Bool.or_eq_true] at h; simp only [inlineE, occE, Bool.or_eq_true]
    exact h.imp (occE_inline fl hi a) (occE_inline fl hi b)
  | .max a b, h => by
    simp only [occE, Bool.or_eq_true] at h; simp only [inlineE, occE, Bool.or_eq_true]
    exact h.imp (occE_inline fl hi a) (occE_inline fl hi b)
  | .prod a b, h => by
    simp only [occE, Bool.or_eq_true] at h; simp only [inlineE, occE, Bool.or_eq_true]
    exact h.imp (occE_inline fl hi a) (occE_inline fl hi b)
  | .ite c t f, h => by
    simp only [occE, Bool.or_eq_true] at h; simp only [inlineE, occE, Bool.or_eq_true]
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (occC_inline fl hi c h))
    · exact Or.inl (Or.inr (occE_inline fl hi t h))
    · exact Or.inr (occE_inline fl hi f h)
  | .get _ key, h => by simp only [occE] at h; simp only [inlineE, occE]; exact occE_inline fl hi key h
theorem occC_inline (fl : List (Nat × C)) {i : Nat} (hi : flagOf fl i = none) : ∀ c : C, occC i c = true → occC i (inlineC fl c) = true
  | .le a b, h => by
    simp only [occC, Bool.or_eq_true] at h; simp only [inlineC, occC, Bool.or_eq_true]
    exact h.imp (occE_inline fl hi a) (occE_inline fl hi b)
  | .lt a b, h => by
    simp only [occC, Bool.or_eq_true] at h; simp only [inlineC, occC, Bool.or_eq_true]
    exact h.imp (occE_inline fl hi a) (occE_inline fl hi b)
  | .eq a b, h => by
    simp only [occC, Bool.or_eq_true] at h
    have hd : occC i (.eq (inlineE fl a) (inlineE fl b)) = true := by
      simp only [occC, Bool.or_eq_true]; exact h.imp (occE_inline fl hi a) (occE_inline fl hi b)
    simp only [inlineC, eqOrFlag]
    split
    · split
      · rename_i c hc
        exfalso
        rcases h with h | h
        · simp only [occE, beq_iff_eq] at h; subst h; rw [hi] at hc; cases hc
        · simp [occE] at h
      · exact hd
    · exact hd
  | .and a b, h => by
    simp only [occC, Bool.or_eq_true] at h; simp only [inlineC, occC, Bool.or_eq_true]
    exact h.imp (occC_inline fl hi a) (occC_inline fl hi b)
  | .or a b, h => by
    simp only [occC, Bool.or_eq_true] at h; simp only [inlineC, occC, Bool.or_eq_true]
    exact h.imp (occC_inline fl hi a) (occC_inline fl hi b)
  | .not a, h => by simp only [occC] at h; simp only [inlineC, occC]; exact occC_inline fl hi a h
end

theorem avoidsE_of_inline {fl : List (Nat × C)} {Z : List Nat} (hz : ∀ i ∈ Z, i ∉ flagVars fl) {e : E}
    (h : avoidsE Z (inlineE fl e) = true) : avoidsE Z e = true := by
  simp only [avoidsE, List.all_eq_true, Bool.not_eq_true'] at h ⊢
  intro i hi
  cases ho : occE i e
  · rfl
  · have hn : flagOf fl i = none := by
      simp only [flagOf]
      rw [lookup_none (fun p hp => by
        simp only [beq_eq_false_iff_ne]; intro he; exact hz _ hi (by rw [← he]; exact List.mem_map_of_mem hp))]
      rfl
    have := h i hi; rw [occE_inline fl hn e ho] at this; cases this

theorem sOk_terms (hs : sOk s = true) : (∀ p ∈ s.f.m.step, avoidsE s.wVars (inlineE s.f.flags p.2) = true)
    ∧ (∀ w ∈ s.f.m.writes, avoidsE s.wVars (inlineE s.f.flags w.2.1) = true ∧ avoidsE s.wVars (inlineE s.f.flags w.2.2) = true)
    ∧ (∀ w ∈ s.every, avoidsE s.wVars (inlineE s.f.flags w.2.2) = true) ∧ avoids s.wVars s.f.m.assume = true
    ∧ avoids (s.wVars ++ s.qVars) s.f.m.pre = true := by
  simp only [sOk, Bool.and_eq_true, List.all_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hpre⟩, hst⟩, hwr⟩, hev⟩, has⟩ := hs
  exact ⟨hst, fun w hw => hwr w hw, fun w hw => (hev w hw).1.1.1, has, hpre⟩

-- The witnesses are no flags.
theorem wVars_flags (hs : sOk s = true) : ∀ i ∈ s.wVars, i ∉ flagVars s.f.flags := by
  obtain ⟨_, _, _, _, hd, _, _⟩ := sOk_parts s hs
  intro i hi hf
  exact (distinct_append hd).2.2 i (by simp only [SMachine.extVars, List.mem_append]; exact Or.inr hi) hf

theorem sk_view_eq (ρ ρ' : Nat → Nat) (hag : Agree s.wVars ρ' ρ) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    sView s.sk ρ' M (sReq s ρ M ι κ) κ = (decideFlags s.f.flags (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ), withCarried s M κ) := by
  simp only [sView]; rw [decideQ_nil sk_q, sk_inputsView ρ ρ' hag]; rfl

-- A step of the machine is a step of its sk machine, its request decided: allowed alike, the state after it agreeing
-- off the witnesses, the maps the same.
theorem sk_step (hs : sOk s = true) {ρ ρ' : Nat → Nat} (hag : Agree s.wVars ρ' ρ) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    evalC (sView s.sk ρ' M (sReq s ρ M ι κ) κ).1 (sView s.sk ρ' M (sReq s ρ M ι κ) κ).2 s.f.m.assume
      = evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume
    ∧ Agree s.wVars (sNext s.sk ρ' M (sReq s ρ M ι κ) κ).1 (sNext s ρ M ι κ).1
    ∧ (sNext s.sk ρ' M (sReq s ρ M ι κ) κ).2 = (sNext s ρ M ι κ).2 := by
  obtain ⟨hV, hN⟩ := sk_view hs hag M ι κ
  obtain ⟨hst, hwr, hev, has, _⟩ := sOk_terms hs
  have hz := wVars_flags hs
  have hraw : ∀ e : E, avoidsE s.wVars (inlineE s.f.flags e) = true → ∀ j, occE j e = true → j ∉ s.wVars :=
    fun e he j hj => avoidsE_occ (avoidsE_of_inline hz he) hj
  have hEq : ∀ e : E, avoidsE s.wVars (inlineE s.f.flags e) = true → ∀ (A B : Nat → Nat), Agree s.wVars A B → ∀ N : Nat → Nat → Nat,
      evalE A N e = evalE B N e := fun e he A B hab N => congrE A B N e (fun j hj => hab j (hraw e he j hj))
  refine ⟨?_, fun i hi => ?_, ?_⟩
  · rw [hN, congrC _ (sView s ρ M ι κ).1 _ s.f.m.assume (fun j hj => hV j (avoids_occ has hj))]
  · simp only [sNext, applyS]
    rw [show s.sk.f.m.step = s.f.m.step from rfl]
    cases ha : assoc s.f.m.step i with
    | none => show (sView s.sk ρ' M (sReq s ρ M ι κ) κ).1 i = (sView s ρ M ι κ).1 i; exact hV i hi
    | some e =>
      show evalE (sView s.sk ρ' M (sReq s ρ M ι κ) κ).1 (sView s.sk ρ' M (sReq s ρ M ι κ) κ).2 e = evalE (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 e
      obtain ⟨p, hp, rfl⟩ : ∃ p ∈ s.f.m.step, p.2 = e := by
        simp only [assoc, Option.map_eq_some_iff] at ha; obtain ⟨p, hl, rfl⟩ := ha; exact ⟨p, (lookup_some hl).1, rfl⟩
      rw [hN]; exact hEq p.2 (hst p hp) _ _ hV _
  · simp only [sNext]
    funext mp key
    show everyMaps s (sView s.sk ρ' M (sReq s ρ M ι κ) κ).1 (sView s.sk ρ' M (sReq s ρ M ι κ) κ).2 mp key = everyMaps s (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 mp key
    rw [hN]
    simp only [everyMaps]
    cases hl : lookup (fun w => w.1 == mp) s.every with
    | some w =>
      have hu : Agree s.wVars (upd (sView s.sk ρ' M (sReq s ρ M ι κ) κ).1 w.2.1 key) (upd (sView s ρ M ι κ).1 w.2.1 key) := by
        intro j hj; simp only [upd]; split
        · rfl
        · exact hV j hj
      exact hEq w.2.2 (hev w (lookup_some hl).1) _ _ hu _
    | none =>
      simp only [writeMaps]
      cases hl2 : lookup (fun w => w.1 == mp) s.f.m.writes with
      | none => rfl
      | some w =>
        obtain ⟨h1, h2⟩ := hwr w (lookup_some hl2).1
        simp only [hEq w.2.1 h1 _ _ hV, hEq w.2.2 h2 _ _ hV]

-- A run's request at time u decided: its flags and witnesses as a goal reads them from its inputs.
def CRun.Decided (s : SMachine) (r : CRun) (u : Nat) : Prop := r.ι u = sReq s (r.st u) (r.mp u) (r.ι u) (r.κ u)

-- The run with the request at T (the last, which no step takes) replaced.
def CRun.last (r : CRun) (T : Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) : CRun :=
  ⟨r.ρ0, r.st, r.mp, fun u => if u = T then ι else r.ι u, fun u => if u = T then κ else r.κ u⟩

theorem last_ok {s' : SMachine} {r : CRun} {T : Nat} (hr : r.Ok s' T) (ι : Nat → Nat) (κ : Nat → Nat → Nat) : (r.last T ι κ).Ok s' T := by
  have hNX : ∀ u, u < T → (r.last T ι κ).N s' u = r.N s' u ∧ (r.last T ι κ).V s' u = r.V s' u := fun u hu => by
    have hne : u ≠ T := Nat.ne_of_lt hu
    refine ⟨?_, ?_⟩ <;> simp only [CRun.V, CRun.X, CRun.N, CRun.last, if_neg hne]
  exact ⟨hr.maps0, hr.pre, hr.facts, hr.pfacts, hr.init, fun u hu => by rw [(hNX u hu).1, (hNX u hu).2]; exact hr.step u hu⟩

-- The request at T decided from no inputs: a decided last request.
theorem last_decided {r : CRun} {T : Nat} : (r.last T (sReq s (r.st T) (r.mp T) (fun _ => 0) noSets) noSets).Decided s T := by
  simp only [CRun.Decided, CRun.last, if_pos rfl]; exact (sReq_idem _ _ _ _).symm

theorem last_other {r : CRun} {T u : Nat} (hu : u ≠ T) (ι : Nat → Nat) (κ : Nat → Nat → Nat) (h : r.Decided s u) : (r.last T ι κ).Decided s u := by
  simp only [CRun.Decided, CRun.last, if_neg hu]; exact h

-- A reachable state of the machine ends a run of its sk machine, every request of it decided, off the witnesses.
theorem sk_run (hs : sOk s = true) : ∀ {ρ M}, SReach s ρ M → ∃ (r : CRun) (T : Nat), r.Ok s.sk T ∧ (∀ u, u ≤ T → r.Decided s u)
    ∧ Agree s.wVars (r.st T) ρ ∧ r.mp T = M := by
  intro ρ M h
  induction h with
  | start ρ M hM hp hf hpf =>
    exact ⟨⟨ρ, fun _ => applyS s.f.m.init ρ M, fun _ => M, fun _ => sReq s (applyS s.f.m.init ρ M) M (fun _ => 0) noSets, fun _ => noSets⟩, 0,
      ⟨hM, hp, hf, hpf, rfl, fun u hu => absurd hu (Nat.not_lt_zero u)⟩, fun _ _ => (sReq_idem _ _ _ _).symm, fun _ _ => rfl, rfl⟩
  | step ρ M ι κ _ ha ih =>
    obtain ⟨r, T, hr, hd, hag, hmp⟩ := ih
    obtain ⟨hA, hS, hMn⟩ := sk_step hs hag M ι κ
    have hr1 := run_snoc_ok sk_q hr rfl hmp (sReq s ρ M ι κ) κ (by show evalC _ _ s.f.m.assume = true; rw [hA]; exact ha)
    let r1 := r.snoc T (sNext s.sk (r.st T) M (sReq s ρ M ι κ) κ).1 (sNext s.sk (r.st T) M (sReq s ρ M ι κ) κ).2 (sReq s ρ M ι κ) κ
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := snoc_last (r := r) (T := T) (sNext s.sk (r.st T) M (sReq s ρ M ι κ) κ).1 (sNext s.sk (r.st T) M (sReq s ρ M ι κ) κ).2 (sReq s ρ M ι κ) κ
    refine ⟨r1.last (T + 1) (sReq s (r1.st (T + 1)) (r1.mp (T + 1)) (fun _ => 0) noSets) noSets, T + 1, last_ok hr1 _ _, fun u hu => ?_, ?_, ?_⟩
    · rcases Nat.lt_or_ge u T with hlt | hge
      · refine last_other (Nat.ne_of_lt (by omega)) _ _ ?_
        obtain ⟨e1, _, e3, e4⟩ := snoc_early (s := s.sk) (r := r) hlt (sNext s.sk (r.st T) M (sReq s ρ M ι κ) κ).1 (sNext s.sk (r.st T) M (sReq s ρ M ι κ) κ).2 (sReq s ρ M ι κ) κ
        have h := hd u (Nat.le_of_lt hlt)
        simp only [CRun.Decided, r1, CRun.snoc, if_pos hlt, if_pos (Nat.le_of_lt hlt)] at h ⊢
        exact h
      · rcases Nat.lt_or_ge u (T + 1) with hlt | hge'
        · have hu : u = T := by omega
          subst hu
          refine last_other (by omega) _ _ ?_
          simp only [CRun.Decided, r1, l3, l4, l5, l6, hmp]
          rw [sReq_agree hs hag, sReq_idem]
        · have hu : u = T + 1 := by omega
          subst hu; exact last_decided
    · show Agree s.wVars (r1.st (T + 1)) (sNext s ρ M ι κ).1
      rw [l1]; exact hS
    · show r1.mp (T + 1) = (sNext s ρ M ι κ).2
      rw [l2]; exact hMn

-- A guard: where u ≤ T.
def cycUpTo (ce : CycEnc) (c : C) : C := .or (.not (.le (.var ce.u) (.var ce.T))) (trC ce (.var ce.u) c)

-- The facts the encoding adds for each flag that holds at every key, at each time u ≤ T (Sets.lean's closingHyps read
-- at u): the flag is 0 or 1; it is 0 or its body holds at every value of its keys; it is 1 or its body fails at the
-- witness.
def cycQFacts (s : SMachine) (ce : CycEnc) : List Fact :=
  s.qflags.flatMap fun q =>
    [⟨[ce.u], cycUpTo ce (.le (.var q.1) (.const 1))⟩, ⟨ce.u :: q.2.1, cycUpTo ce (.or (.eq (.var q.1) (.const 0)) q.2.2)⟩]
      ++ (match lookup (fun w => w.1 == q.1) s.wits with
          | some w => [⟨[ce.u], cycUpTo ce (.or (.eq (.var q.1) (.const 1)) (.not (substC (q.2.1.zip (w.2.map .var)) q.2.2)))⟩]
          | none => [])

theorem assoc_zip_none : ∀ (ks : List Nat) (ts : List E), ks.length ≤ ts.length → ∀ {j : Nat}, assoc (ks.zip ts) j = none → j ∉ ks
  | [], _, _, _, _ => by simp
  | _ :: _, [], h, _, _ => by simp at h
  | k :: ks, t :: ts, h, j, ha => by
    simp only [List.zip_cons_cons, assoc, lookup] at ha
    by_cases hk : k = j
    · subst hk; simp at ha
    · simp only [hk, beq_iff_eq, if_false] at ha
      intro hm
      rcases List.mem_cons.mp hm with hm | hm
      · exact hk hm.symm
      · exact assoc_zip_none ks ts (by simpa using h) (by simpa [assoc] using ha) hm

theorem assoc_zip_self (g : Nat → E) : ∀ (ks : List Nat) {j : Nat}, j ∈ ks → assoc (ks.zip (ks.map g)) j = some (g j)
  | [], _, h => by simp at h
  | k :: ks, j, h => by
    simp only [List.map_cons, List.zip_cons_cons, assoc, lookup]
    by_cases hk : k = j
    · subst hk; simp
    · have hj : j ∈ ks := by rcases List.mem_cons.mp h with h | h; exact absurd h.symm hk; exact h
      have := assoc_zip_self g ks hj
      simp only [assoc] at this
      simp [hk, this]

-- On a decided run, the encoding at a time up to T reads the goal's view of that step (Sets.lean's withExt, sReq).
theorem sk_X {r : CRun} {u : Nat} (hd : r.Decided s u) :
    r.X s.sk u = withExt s (r.st u) (sReq s (r.st u) (r.mp u) (r.ι u) (r.κ u)) := by
  funext v
  simp only [CRun.X, withInputs, withExt, sk_inputs]
  by_cases hv : s.extVars.contains v = true
  · simp only [hv, ↓reduceIte]; exact congrFun hd v
  · simp only [hv, Bool.false_eq_true, ↓reduceIte]

-- A quantified flag's body reads no added variable, no flag, no map over time, and of the keys none but its own.
def cycBodyOk (s : SMachine) (ce : CycEnc) (keys : List Nat) : Bool :=
  s.qflags.all fun q => avoids ce.special q.2.2 && avoidsMaps ce.tm q.2.2 && keys.all (fun k => q.2.1.contains k || !occC k q.2.2)
    && q.2.1.all (fun k => keys.contains k)

section qfacts
variable {ce : CycEnc} {keys : List Nat} (hs : sOk s = true) (hS : CycShape s.sk ce keys) (hT : CycTerms s.sk ce keys)
  {r : CRun} {T : Nat} (hr : r.Ok s.sk T) (hd : ∀ u, u ≤ T → r.Decided s u) (hb : cycBodyOk s ce keys = true)
  {Q : Nat → Nat} (hQ : EnvOk s.sk ce keys r T Q)
include hs hS hT hr hd hb hQ

-- A fact over u and some keys, guarded by u ≤ T: true when its condition is, read at the run's step at u.
theorem upto_true {ks : List Nat} (hks : ∀ x ∈ ks, x = ce.u ∨ x ∈ keys) (hu : ce.u ∈ ks) (vals : Nat → Nat) (c : C)
    (h : vals ce.u ≤ T → evalC (applyS (cycσ ce (.var ce.u)) (override ks vals Q) (cycMaps s.sk ce r (T + 1))) (cycView s.sk ce r (T + 1) (vals ce.u)) c = true) :
    evalC (override ks vals Q) (cycMaps s.sk ce r (T + 1)) (cycUpTo ce c) = true := by
  have hsp := special_parts hS.dsp
  have hnk : ∀ i, (i = ce.T ∨ i = ce.om) → i ∉ ks := fun i hi hm => by
    rcases hks i hm with h1 | h1
    · rcases hi with rfl | rfl
      · exact hsp.1 h1.symm
      · exact hsp.2.1 h1.symm
    · exact hS.ks i h1 (in_special (by rcases hi with rfl | rfl; exact Or.inr (Or.inr (Or.inl rfl)); exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hQ1 : EnvOk s.sk ce keys r T (override ks vals Q) := by
    refine ⟨?_, ?_, fun i hi => ?_⟩
    · simp only [override]; rw [if_neg (fun h => hnk ce.T (Or.inl rfl) (List.contains_iff_mem.mp h))]; exact hQ.1
    · simp only [override]; rw [if_neg (fun h => hnk ce.om (Or.inr rfl) (List.contains_iff_mem.mp h))]; exact hQ.2.1
    · simp only [override]
      rw [if_neg (fun h => by
        rcases hks i (List.contains_iff_mem.mp h) with h1 | h1
        · exact (notP hi).1 (in_special (Or.inl h1))
        · exact (notP hi).2.1 h1)]
      exact hQ.2.2 i hi
  have hw : evalE (override ks vals Q) (cycMaps s.sk ce r (T + 1)) (.var ce.u) = vals ce.u := by
    simp only [evalE, override, List.contains_iff_mem.mpr hu, ite_true]
  simp only [cycUpTo, evalC, Bool.or_eq_true, Bool.not_eq_true']
  by_cases hle : vals ce.u ≤ T
  · right; rw [enc_trC hS hT hr hQ1 hw hle]; exact h hle
  · left; simp only [evalE] at hw; simp only [decide_eq_false_iff_not, evalE, hw, hQ1.1]; exact hle

theorem qbody_parts {q : Nat × List Nat × C} (hq : q ∈ s.qflags) :
    avoids ce.special q.2.2 = true ∧ avoidsMaps ce.tm q.2.2 = true ∧ (∀ k ∈ keys, q.2.1.contains k = true ∨ occC k q.2.2 = false)
      ∧ (∀ k ∈ q.2.1, k ∈ keys) := by
  have h := List.all_eq_true.mp hb q hq
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, fun k hk => List.contains_iff_mem.mp (h.2 k hk)⟩

-- At a time u0 ≤ T, a variable no added name or flag is reads the goal's view of the run's step there.
theorem upto_view {ks : List Nat} (hks : ∀ x ∈ ks, x = ce.u ∨ x ∈ keys) (vals : Nat → Nat) (hu0 : vals ce.u ≤ T) (hu : ce.u ∈ ks)
    {j : Nat} (hz : j ∉ cycZ ce keys) (hf : j ∉ flagVars s.f.flags) :
    applyS (cycσ ce (.var ce.u)) (override ks vals Q) (cycMaps s.sk ce r (T + 1)) j
      = withExt s (r.st (vals ce.u)) (sReq s (r.st (vals ce.u)) (r.mp (vals ce.u)) (r.ι (vals ce.u)) (r.κ (vals ce.u))) j := by
  have hsp := special_parts hS.dsp
  have hQ1 : EnvOk s.sk ce keys r T (override ks vals Q) := by
    have hnk : ∀ i, (i = ce.T ∨ i = ce.om) → i ∉ ks := fun i hi hm => by
      rcases hks i hm with h1 | h1
      · rcases hi with rfl | rfl
        · exact hsp.1 h1.symm
        · exact hsp.2.1 h1.symm
      · exact hS.ks i h1 (in_special (by rcases hi with rfl | rfl; exact Or.inr (Or.inr (Or.inl rfl)); exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    refine ⟨?_, ?_, fun i hi => ?_⟩
    · simp only [override]; rw [if_neg (fun h => hnk ce.T (Or.inl rfl) (List.contains_iff_mem.mp h))]; exact hQ.1
    · simp only [override]; rw [if_neg (fun h => hnk ce.om (Or.inr rfl) (List.contains_iff_mem.mp h))]; exact hQ.2.1
    · simp only [override]
      rw [if_neg (fun h => by
        rcases hks i (List.contains_iff_mem.mp h) with h1 | h1
        · exact (notP hi).1 (in_special (Or.inl h1))
        · exact (notP hi).2.1 h1)]
      exact hQ.2.2 i hi
  have hw : evalE (override ks vals Q) (cycMaps s.sk ce r (T + 1)) (.var ce.u) = vals ce.u := by
    simp only [evalE, override, List.contains_iff_mem.mpr hu, ite_true]
  rw [enc_Y hS hT hr hQ1 hw hu0 hz hf, sk_X (hd _ hu0)]

-- A variable of the goal's view: a quantified flag or a witness is traced, no added name, no flag.
theorem ext_free {v : Nat} (hv : v ∈ s.extVars) : v ∉ cycZ ce keys ∧ v ∉ flagVars s.f.flags := by
  obtain ⟨_, _, _, _, hd', _, _⟩ := sOk_parts s hs
  exact ⟨fun h => hS.zv v h (hS.inv v (by rw [sk_inputs]; exact hv)), (distinct_append hd').2.2 v hv⟩

theorem qflag_ext {q : Nat × List Nat × C} (hq : q ∈ s.qflags) : q.1 ∈ s.extVars := by
  simp only [SMachine.extVars, SMachine.qVars, List.mem_append, List.mem_map]; exact Or.inl (Or.inr ⟨q, hq, rfl⟩)

-- A body variable, not one of the body's keys: no added name, no flag.
theorem body_free {q : Nat × List Nat × C} (hq : q ∈ s.qflags) {j : Nat} (hj : occC j q.2.2 = true) (hk : j ∉ q.2.1) :
    j ∉ cycZ ce keys ∧ j ∉ flagVars s.f.flags := by
  obtain ⟨hsb, _, hkb, _⟩ := qbody_parts hs hS hT hr hd hb hQ hq
  obtain ⟨_, _, _, _, _, hbody, _⟩ := sOk_parts s hs
  refine ⟨fun h => ?_, fun h => avoids_occ (hbody q hq).1 hj (List.mem_append_right _ h)⟩
  simp only [cycZ, List.mem_append] at h
  rcases h with h | h
  · exact avoids_occ hsb hj h
  · rcases hkb j h with h1 | h1
    · exact hk (List.contains_iff_mem.mp h1)
    · rw [hj] at h1; cases h1

theorem qfacts_hold {f : Fact} (hf : f ∈ cycQFacts s ce) (vals : Nat → Nat) :
    evalC (override f.keys vals Q) (cycMaps s.sk ce r (T + 1)) f.holds = true := by
  simp only [cycQFacts, List.mem_flatMap, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  obtain ⟨q, hq, hf⟩ := hf
  obtain ⟨_, hmb, _, hbk⟩ := qbody_parts hs hS hT hr hd hb hQ hq
  have hqv := ext_free hs hS hT hr hd hb hQ (qflag_ext hs hS hT hr hd hb hQ hq)
  -- The maps a body reads, at u0: the step's.
  have hN : ∀ u0 m, m ∉ ce.tm → cycView s.sk ce r (T + 1) u0 m = withCarried s (r.mp u0) (r.κ u0) m := fun u0 m hm => by
    rw [cv_N hm]; rfl
  rcases hf with (rfl | rfl) | hf
  · -- 0 or 1
    refine upto_true hs hS hT hr hd hb hQ (fun x hx => by simp at hx; exact Or.inl hx) (by simp) vals _ (fun hu0 => ?_)
    have hc := closing_true s (r.st (vals ce.u)) (r.mp (vals ce.u)) (r.ι (vals ce.u)) (r.κ (vals ce.u)) hs [] (.le (.var q.1) (.const 1)) (by
      simp only [closingHyps, List.mem_flatMap]; exact ⟨q, hq, by simp⟩)
    rw [evalC_iff] at hc ⊢
    simp only [holdsC, evalE] at hc ⊢
    rw [upto_view hs hS hT hr hd hb hQ (fun x hx => by simp at hx; exact Or.inl hx) vals hu0 (by simp) hqv.1 hqv.2]; exact hc
  · -- 0, or the body at every value of the keys
    have hks : ∀ x ∈ ce.u :: q.2.1, x = ce.u ∨ x ∈ keys := fun x hx => by
      rcases List.mem_cons.mp hx with h | h; exact Or.inl h; exact Or.inr (hbk x h)
    refine upto_true hs hS hT hr hd hb hQ hks List.mem_cons_self vals _ (fun hu0 => ?_)
    let u0 := vals ce.u
    let consts := q.2.1.map (fun k => E.const (vals k))
    have hc := closing_true s (r.st u0) (r.mp u0) (r.ι u0) (r.κ u0) hs [(q.1, consts)] (.or (.eq (.var q.1) (.const 0)) (substC (q.2.1.zip consts) q.2.2)) (by
      simp only [closingHyps, List.mem_flatMap]; exact ⟨q, hq, by simp⟩)
    rw [evalC_iff] at hc ⊢
    simp only [holdsC, evalE] at hc ⊢
    rw [upto_view hs hS hT hr hd hb hQ hks vals hu0 List.mem_cons_self hqv.1 hqv.2]
    rcases hc with hc | hc
    · exact Or.inl hc
    · right
      rw [← evalC_iff] at hc ⊢
      rw [subst_evalC] at hc
      rw [congr2C (ρ' := applyS (q.2.1.zip consts) (withExt s (r.st u0) (sReq s (r.st u0) (r.mp u0) (r.ι u0) (r.κ u0))) (withCarried s (r.mp u0) (r.κ u0)))
        (M' := withCarried s (r.mp u0) (r.κ u0)) q.2.2 (fun j hj => ?_) (fun m hm => hN u0 m (avoidsMaps_occ hmb hm))]
      · exact hc
      · by_cases hjk : j ∈ q.2.1
        · have hr1 : applyS (q.2.1.zip consts) (withExt s (r.st u0) (sReq s (r.st u0) (r.mp u0) (r.ι u0) (r.κ u0))) (withCarried s (r.mp u0) (r.κ u0)) j = vals j := by
            simp only [applyS, consts, assoc_zip_self (fun k => E.const (vals k)) q.2.1 hjk, evalE]
          have hz : (cycσ ce (.var ce.u)).map (·.1) = ce.vtr.map (·.1) := by simp [cycσ]
          rw [hr1, applyS_other (by rw [hz]; exact fun h => hS.zv j (by simp only [cycZ, List.mem_append]; exact Or.inr (hbk j hjk)) h)]
          simp only [override, List.contains_iff_mem.mpr (List.mem_cons_of_mem _ hjk), ite_true]
        · obtain ⟨hz, hfl⟩ := body_free hs hS hT hr hd hb hQ hq hj hjk
          rw [upto_view hs hS hT hr hd hb hQ hks vals hu0 List.mem_cons_self hz hfl, applyS_other (fun h => hjk (by
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact (List.of_mem_zip hp).1))]
  · -- 1, or the body failing at the witness
    cases hl : lookup (fun w => w.1 == q.1) s.wits with
    | none => rw [hl] at hf; simp at hf
    | some w =>
      rw [hl] at hf; simp only [List.mem_singleton] at hf; subst hf
      refine upto_true hs hS hT hr hd hb hQ (fun x hx => by simp at hx; exact Or.inl hx) (by simp) vals _ (fun hu0 => ?_)
      let u0 := vals ce.u
      have hc := closing_true s (r.st u0) (r.mp u0) (r.ι u0) (r.κ u0) hs [] (.or (.eq (.var q.1) (.const 1)) (.not (substC (q.2.1.zip (w.2.map .var)) q.2.2))) (by
        simp only [closingHyps, List.mem_flatMap]; exact ⟨q, hq, by simp [hl]⟩)
      have hwv : ∀ v ∈ w.2, v ∈ s.extVars := fun v hv => by
        simp only [SMachine.extVars, SMachine.wVars, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨w, (lookup_some hl).1, hv⟩
      have hσ : ∀ j, applyS (q.2.1.zip (w.2.map .var)) (applyS (cycσ ce (.var ce.u)) (override [ce.u] vals Q) (cycMaps s.sk ce r (T + 1))) (cycView s.sk ce r (T + 1) u0) j
          = applyS (q.2.1.zip (w.2.map .var)) (withExt s (r.st u0) (sReq s (r.st u0) (r.mp u0) (r.ι u0) (r.κ u0))) (withCarried s (r.mp u0) (r.κ u0)) j ∨ occC j q.2.2 = false := by
        intro j
        by_cases hjo : occC j q.2.2 = true
        · left
          simp only [applyS]
          cases ha : assoc (q.2.1.zip (w.2.map .var)) j with
          | some e =>
            obtain ⟨v, hv, rfl⟩ : ∃ v ∈ w.2, e = .var v := by
              simp only [assoc, Option.map_eq_some_iff] at ha
              obtain ⟨p, hp, rfl⟩ := ha
              have := (lookup_some hp).1
              obtain ⟨_, hpw⟩ := List.of_mem_zip this
              obtain ⟨v, hv, he⟩ := List.mem_map.mp hpw
              exact ⟨v, hv, he.symm⟩
            simp only [evalE]
            have hf := ext_free hs hS hT hr hd hb hQ (hwv v hv)
            exact upto_view hs hS hT hr hd hb hQ (fun x hx => by simp at hx; exact Or.inl hx) vals hu0 (by simp) hf.1 hf.2
          | none =>
            have hjk : j ∉ q.2.1 := by
              obtain ⟨_, _, hwd, hcov, _, _, _⟩ := sOk_parts s hs
              obtain ⟨⟨w', hw', hw1, hlen⟩, _⟩ := hcov q hq
              simp only [distinctPairs, Bool.and_eq_true] at hwd
              have hww : w = w' := by
                have h1 := lookup_unique hwd.1 hw'
                rw [hw1, hl] at h1; exact Option.some.inj h1
              subst hww
              exact assoc_zip_none q.2.1 (w.2.map .var) (by simp [hlen]) ha
            obtain ⟨hz, hfl⟩ := body_free hs hS hT hr hd hb hQ hq hjo hjk
            exact upto_view hs hS hT hr hd hb hQ (fun x hx => by simp at hx; exact Or.inl hx) vals hu0 (by simp) hz hfl
        · right; simpa using hjo
      rw [evalC_iff] at hc ⊢
      simp only [holdsC, evalE] at hc ⊢
      rw [upto_view hs hS hT hr hd hb hQ (fun x hx => by simp at hx; exact Or.inl hx) vals hu0 (by simp) hqv.1 hqv.2]
      rcases hc with hc | hc
      · exact Or.inl hc
      · right
        intro hn; apply hc
        rw [← evalC_iff] at hn ⊢
        rw [subst_evalC]
        rw [subst_evalC] at hn
        rw [← congr2C (ρ' := applyS (q.2.1.zip (w.2.map .var)) (withExt s (r.st u0) (sReq s (r.st u0) (r.mp u0) (r.ι u0) (r.κ u0))) (withCarried s (r.mp u0) (r.κ u0)))
          (M' := withCarried s (r.mp u0) (r.κ u0)) q.2.2 (fun j hj => by rcases hσ j with h | h; exact h; rw [hj] at h; cases h)
          (fun m hm => hN u0 m (avoidsMaps_occ hmb hm))]
        exact hn

end qfacts

end sk

section skseq
variable {s : SMachine}

-- Requests in a row, read by the sk machine: each decided at the machine's state it is taken in.
noncomputable def skReqs (s : SMachine) : (Nat → Nat) → (Nat → Nat → Nat) → List SRequest → List SRequest
  | _, _, [] => []
  | ρ, M, q :: qs => (sReq s ρ M q.1 q.2, q.2) :: skReqs s (sNext s ρ M q.1 q.2).1 (sNext s ρ M q.1 q.2).2 qs

theorem skReqs_length : ∀ (ρ : Nat → Nat) (M : Nat → Nat → Nat) (qs : List SRequest), (skReqs s ρ M qs).length = qs.length
  | _, _, [] => rfl
  | ρ, M, q :: qs => by simp [skReqs, skReqs_length _ _ qs]

theorem skReqs_take : ∀ (ρ : Nat → Nat) (M : Nat → Nat → Nat) (qs : List SRequest) (j : Nat), (skReqs s ρ M qs).take j = skReqs s ρ M (qs.take j)
  | _, _, [], _ => by simp [skReqs]
  | _, _, _ :: _, 0 => by simp [skReqs]
  | ρ, M, q :: qs, j + 1 => by simp [skReqs, skReqs_take _ _ qs j]

-- Along requests the machine allows, its sk machine allows theirs, each state agreeing off the witnesses, the maps the
-- same; each `when` read alike.
theorem sk_allowed (hs : sOk s = true) : ∀ (ws : List C) (qs : List SRequest) (ρ ρ' : Nat → Nat) (M : Nat → Nat → Nat),
    Agree s.wVars ρ' ρ → SAllowed s ws ρ M qs → SAllowed s.sk ws ρ' M (skReqs s ρ M qs)
  | [], _, _, _, _, _, _ => by cases (skReqs _ _ _ _) <;> trivial
  | _ :: _, [], _, _, _, _, _ => trivial
  | w :: ws, q :: qs, ρ, ρ', M, hag, hK => by
    obtain ⟨hA, hW, hrest⟩ := hK
    obtain ⟨hA', hS', hM'⟩ := sk_step hs hag M q.1 q.2
    refine ⟨by show evalC _ _ s.f.m.assume = true; rw [hA']; exact hA, ?_, ?_⟩
    · show evalC (withExt s.sk ρ' (sReq s.sk ρ' M (sReq s ρ M q.1 q.2) q.2)) (withCarried s.sk M q.2) w = true
      have he : withExt s.sk ρ' (sReq s.sk ρ' M (sReq s ρ M q.1 q.2) q.2) = withInputs s.sk.f.m.inputs ρ' (sReq s ρ M q.1 q.2) := by
        funext v
        rw [withExt_plain sk_q rfl, sReq_plain sk_q rfl]
        simp only [withInputs]; split <;> rfl
      rw [he, sk_inputsView ρ ρ' hag]; exact hW
    · show SAllowed s.sk ws (sNext s.sk ρ' M (sReq s ρ M q.1 q.2) q.2).1 (sNext s.sk ρ' M (sReq s ρ M q.1 q.2) q.2).2
        (skReqs s (sNext s ρ M q.1 q.2).1 (sNext s ρ M q.1 q.2).2 qs)
      rw [hM']
      exact sk_allowed hs ws qs _ _ _ hS' hrest

theorem sk_end (hs : sOk s = true) : ∀ (qs : List SRequest) (ρ ρ' : Nat → Nat) (M : Nat → Nat → Nat), Agree s.wVars ρ' ρ →
    Agree s.wVars (sEnd s.sk ρ' M (skReqs s ρ M qs)).1 (sEnd s ρ M qs).1 ∧ (sEnd s.sk ρ' M (skReqs s ρ M qs)).2 = (sEnd s ρ M qs).2
  | [], _, _, _, hag => ⟨hag, rfl⟩
  | q :: qs, ρ, ρ', M, hag => by
    obtain ⟨_, hS', hM'⟩ := sk_step hs hag M q.1 q.2
    simp only [skReqs, sEnd]
    rw [hM']
    exact sk_end hs qs _ _ _ hS'

-- The j-th request of a row, read by the sk machine.
theorem skReqs_get : ∀ (ρ : Nat → Nat) (M : Nat → Nat → Nat) (qs : List SRequest) (j : Nat) (h : j < qs.length),
    (skReqs s ρ M qs)[j]'(by rw [skReqs_length]; exact h)
      = (sReq s (sEnd s ρ M (qs.take j)).1 (sEnd s ρ M (qs.take j)).2 qs[j].1 qs[j].2, qs[j].2)
  | _, _, [], _, h => absurd h (Nat.not_lt_zero _)
  | ρ, M, q :: qs, 0, _ => by simp [skReqs, sEnd]
  | ρ, M, q :: qs, j + 1, h => by
    simp only [skReqs, List.getElem_cons_succ, List.take_succ_cons, sEnd, List.length_cons] at h ⊢
    exact skReqs_get _ _ qs j (by omega)

-- Each step's extended request, as SKStepHolds reads it.
theorem sExts_get : ∀ (ρ : Nat → Nat) (M : Nat → Nat → Nat) (qs : List SRequest) (j : Nat) (h : j < qs.length),
    (sExts s ρ M qs)[j]'(by
      have : ∀ ρ M (qs : List SRequest), (sExts s ρ M qs).length = qs.length := by
        intro ρ M qs; induction qs generalizing ρ M with
        | nil => rfl
        | cons q qs ih => simp [sExts, ih]
      rw [this]; exact h)
      = sReq s (sEnd s ρ M (qs.take j)).1 (sEnd s ρ M (qs.take j)).2 qs[j].1 qs[j].2
  | _, _, [], _, h => absurd h (Nat.not_lt_zero _)
  | ρ, M, q :: qs, 0, _ => by simp [sExts, sEnd]
  | ρ, M, q :: qs, j + 1, h => by
    simp only [sExts, List.getElem_cons_succ, List.take_succ_cons, sEnd, List.length_cons] at h ⊢
    exact sExts_get _ _ qs j (by omega)

end skseq

-- The keys the quantified flags bind.
def SMachine.bk (s : SMachine) : List Nat := s.qflags.flatMap (·.2.1)

-- Each exported fact is one of the sk machine's encoding, one a flag that holds at every key adds, or true of every natural.
def cycQFactsIn (s : SMachine) (ce : CycEnc) (facts : List Fact) : Bool :=
  facts.all fun f => natC f.holds || (cycCanon s.sk ce ++ cycQFacts s ce).any (factBeq f)

theorem qfacts_all {s : SMachine} {ce : CycEnc} {keys : List Nat} (hs : sOk s = true) (hS : CycShape s.sk ce keys) (hT : CycTerms s.sk ce keys)
    {r : CRun} {T : Nat} (hr : r.Ok s.sk T) (hd : ∀ u, u ≤ T → r.Decided s u) (hb : cycBodyOk s ce keys = true)
    {Q : Nat → Nat} (hQ : EnvOk s.sk ce keys r T Q) {facts : List Fact} (hfa : cycQFactsIn s ce facts = true) :
    FactsHold facts Q (cycMaps s.sk ce r (T + 1)) := by
  intro f hf vals
  have hfi := List.all_eq_true.mp hfa f hf
  simp only [Bool.or_eq_true] at hfi
  rcases hfi with hnc | hcan
  · exact natC_true _ hnc
  · obtain ⟨g, hg, hb'⟩ := List.any_eq_true.mp hcan
    simp only [factBeq, Bool.and_eq_true, beq_iff_eq] at hb'
    rw [hb'.1, beqC_eq hb'.2]
    rcases List.mem_append.mp hg with hg | hg
    · exact canon_holds hS hT hr hg hQ vals
    · exact qfacts_hold hs hS hT hr hd hb hQ hg vals

/-- A cyclic proof of a law of a machine with flags that hold at every key, checked against its sk machine's encoding
with those flags' facts (`cycQMOk`): the law holds in every state the machine reaches, at every value of its keys. -/
def cycQMOk (s : SMachine) (ce : CycEnc) (facts : List Fact) (law : C) (keys : List Nat) (n : CNode) : Bool :=
  sOk s && cycShapeOk s.sk ce (keys ++ s.bk) && cycTermsOk s.sk ce (keys ++ s.bk) && cycBodyOk s ce (keys ++ s.bk)
    && cycLawOk s.sk ce law && cycQFactsIn s ce facts && cycNodeOk s.sk ce law n

theorem cyc_qmachine_sound (s : SMachine) (ce : CycEnc) (facts : List Fact) (nodes : List CNode) (hc : checkCyclic facts nodes = true)
    (law : C) (keys : List Nat) (n : CNode) (hn : n ∈ nodes) (hok : cycQMOk s ce facts law keys n = true) :
    ∀ ρ M, SReach s ρ M → ∀ ρ' : Nat → Nat, (∀ i, i ∉ keys → ρ' i = ρ i) → evalC ρ' M law = true := by
  simp only [cycQMOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨hs, hsh⟩, hte⟩, hbo⟩, hlaw⟩, hfa⟩, hnd⟩ := hok
  have hS := cycShape_of hsh
  have hT := cycTerms_of hte
  simp only [cycNodeOk, Bool.and_eq_true] at hnd
  simp only [cycLawOk, Bool.and_eq_true] at hlaw
  intro ρ M hreach ρ' hρ'
  obtain ⟨r, T, hr, hd, hag, hmp⟩ := sk_run hs hreach
  have hsp := special_parts hS.dsp
  have hnot : ∀ i, i ∉ ce.special → cycEnv ce T ρ' i = ρ' i := fun i hi => by
    simp only [cycEnv]
    rw [if_neg (fun e => hi (in_special (Or.inr (Or.inr (Or.inr (Or.inr e)))))),
      if_neg (fun e => hi (in_special (Or.inr (Or.inr (Or.inl e))))), if_neg (fun e => hi (in_special (Or.inr (Or.inr (Or.inr (Or.inl e))))))]
  have hEnv : EnvOk s.sk ce (keys ++ s.bk) r T (cycEnv ce T ρ') := by
    refine ⟨by simp [cycEnv], by simp [cycEnv, Ne.symm hsp.2.2.2.2.2.2, Ne.symm hsp.2.2.2.2.1], ?_⟩
    intro i hi
    obtain ⟨h1, h2, h3, h4⟩ := notP hi
    have hwi : i ∉ s.wVars := fun h => h3 (hS.inv i (by rw [sk_inputs]; simp only [SMachine.extVars, List.mem_append]; exact Or.inr h))
    rw [hnot i h1, hρ' i (fun h => h2 (List.mem_append_left _ h)), ← hag i hwi]
    exact run_frame hr T (Nat.le_refl T) i (fun h => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact h3 (hS.initv p hp))
      (fun h => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact h3 (hS.stepv p hp)) (fun h => h3 (hS.inv i h)) h4
  have hF : FactsHold facts (cycEnv ce T ρ') (cycMaps s.sk ce r (T + 1)) := qfacts_all hs hS hT hr hd hbo hEnv hfa
  have htT : cycEnv ce T ρ' ce.t = T := by simp [cycEnv]
  have hH : ∀ c ∈ n.hyps, evalC (cycEnv ce T ρ') (cycMaps s.sk ce r (T + 1)) c = true := by
    intro c hc
    have h := List.all_eq_true.mp hnd.2 c hc
    simp only [Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · rw [beqC_eq h, congr2C (ρ' := r.ρ0) (M' := r.mp 0) _ (fun j hj => hEnv.2.2 j (avoids_occ hT.prz hj))
        (fun m hm => cm_o (avoidsMaps_occ hT.prm hm))]
      exact hr.pre
    · rw [beqC_eq h, evalC_iff]; simp only [holdsC, evalE, htT, hEnv.1] <;> omega
    · rw [beqC_eq h, evalC_iff]; simp only [holdsC, evalE, hEnv.1, hEnv.2.1] <;> omega
  have hc0 := cyclic_sound facts nodes hc (cycMaps s.sk ce r (T + 1)) (cycEnv ce T ρ') hF n hn hH
  have htT' : evalE (cycEnv ce T ρ') (cycMaps s.sk ce r (T + 1)) (.var ce.t) = T := htT
  rw [beqC_eq hnd.1, enc_trC hS hT hr hEnv htT' (Nat.le_refl T)] at hc0
  rw [congr2C (ρ' := applyS (cycσ ce (.var ce.t)) (cycEnv ce T ρ') (cycMaps s.sk ce r (T + 1))) (M' := cycView s.sk ce r (T + 1) T) law
    (fun j hj => ?_) (fun m hm => ?_)]
  · exact hc0
  · have hj' := avoids_occ hlaw.1 hj
    have hjs : j ∉ ce.special := fun h => hj' (List.mem_append_left _ h)
    have hji : j ∉ s.sk.f.m.inputs := fun h => hj' (List.mem_append_right _ h)
    by_cases hv : j ∈ ce.vtr.map (·.1)
    · rw [enc_σ_in hS hT hr hEnv htT' (Nat.le_refl T) hv, CRun.X, withInputs_other hji]
      have hwj : j ∉ s.wVars := fun h => hji (by rw [sk_inputs]; simp only [SMachine.extVars, List.mem_append]; exact Or.inr h)
      rw [hag j hwj]
      exact hρ' j (fun hk => hS.zv j (List.mem_append_right _ (List.mem_append_left _ hk)) hv)
    · rw [enc_σ_out hS hT hr hEnv htT' (Nat.le_refl T) hv, hnot j hjs]
  · have hm' := avoidsMaps_occ hlaw.2 hm
    rw [cv_N (fun h => hm' (List.mem_append_left _ h)), N_not_carried (fun h => hm' (List.mem_append_right _ h)), hmp]


/-- A k-step law's node for a machine with flags that hold at every key, checked against its sk machine's encoding with
those flags' facts (`cycKOk` over the sk machine, the flags' keys apart). -/
def cycQKOkAt (tb : Bool) (s : SMachine) (ce : CycEnc) (facts : List Fact) (sl : SKStep) (n : CNode) : Bool :=
  sOk s && cycShapeOk s.sk ce s.bk && cycTermsOk s.sk ce s.bk && cycBodyOk s ce s.bk && cycQFactsIn s ce facts
    && sl.k.ren.length == sl.k.whens.length && sl.mren.length == sl.k.whens.length
    && sl.k.ren.all (fun r => r.all fun p => s.sk.f.m.inputs.contains p.1)
    && sl.k.prime.all (fun q => (ce.vtr.map (·.1)).contains q.1 && !s.sk.f.m.inputs.contains q.1)
    && sl.mren.all (fun r => r.all fun p => s.carried.contains p.1 && !ce.tm.contains p.2)
    && sl.k.primeMaps.all (fun q => (ce.mtr.map (·.1)).contains q.1 && !s.carried.contains q.1 && !ce.tm.contains q.2)
    && avoids (ce.special ++ s.bk ++ flagVars s.f.flags) sl.k.then_ && avoidsMaps ce.tm sl.k.then_
    && sl.k.whens.all (fun w => avoids (ce.special ++ s.bk ++ flagVars s.f.flags) w && avoidsMaps ce.tm w)
    && beqC n.concl (substRC (kσ tb ce sl) (kRd tb ce sl) sl.k.then_)
    && n.hyps.all (fun h => beqC h s.f.m.pre || beqC h (.le (.const sl.k.whens.length) (.var ce.t)) || beqC h (.le (.var ce.t) (.var ce.T))
      || beqC h (.lt (.var ce.T) (.var ce.om)) || (kWhens tb ce sl.k.whens.length 0 sl.k.whens).any (beqC h))

theorem cyc_qkstep_sound_at (tb : Bool) (s : SMachine) (ce : CycEnc) (facts : List Fact) (nodes : List CNode) (hc : checkCyclic facts nodes = true)
    (sl : SKStep) (n : CNode) (hn : n ∈ nodes) (hok : cycQKOkAt tb s ce facts sl n = true) : SKStepHolds s sl := by
  simp only [cycQKOkAt, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs, hsh⟩, hte⟩, hbo⟩, hfa⟩, hrl⟩, hml⟩, hrin⟩, hpr⟩, hmr⟩, hpm⟩, hthv⟩, hthm⟩, hwh⟩, hcon⟩, hhy⟩ := hok
  have hS := cycShape_of hsh
  have hT := cycTerms_of hte
  have hsp := special_parts hS.dsp
  have hcz : ∀ x, x ∉ ce.special ++ s.bk ++ flagVars s.f.flags → x ∉ cycZ ce s.bk ∧ x ∉ flagVars s.f.flags := fun x hx =>
    ⟨fun h => hx (List.mem_append_left _ h), fun h => hx (List.mem_append_right _ h)⟩
  intro ρ M hr q₁ qs hlen hK
  obtain ⟨r, T0, hr0, hdec, hag, hmp⟩ := sk_run hs hr
  have hK' := sk_allowed hs sl.k.whens (q₁ :: qs) ρ (r.st T0) M hag hK
  have hql : (skReqs s ρ M (q₁ :: qs)).length = (q₁ :: qs).length := skReqs_length _ _ _
  obtain ⟨r1, hr1, _, hle, hlt, hj, hι⟩ := run_ext sk_q (skReqs s ρ M (q₁ :: qs)) sl.k.whens r T0 (r.st T0) M hr0 rfl hmp (by rw [hql]; simp; omega) hK'
  rw [hql] at hr1 hj
  have hk : sl.k.whens.length = (q₁ :: qs).length := by simp; omega
  -- The state after the first j requests, and the j-th request, as the sk machine's run has them.
  have hagj : ∀ j, j ≤ (q₁ :: qs).length → Agree s.wVars (r1.st (T0 + j)) (sEnd s ρ M ((q₁ :: qs).take j)).1
      ∧ r1.mp (T0 + j) = (sEnd s ρ M ((q₁ :: qs).take j)).2 := fun j hj' => by
    obtain ⟨a, b⟩ := hj j hj'
    rw [a, b, skReqs_take]; exact sk_end hs _ _ _ M hag
  have hreqj : ∀ j (h : j < (q₁ :: qs).length), r1.ι (T0 + j) = sReq s (sEnd s ρ M ((q₁ :: qs).take j)).1 (sEnd s ρ M ((q₁ :: qs).take j)).2 (q₁ :: qs)[j].1 (q₁ :: qs)[j].2
      ∧ r1.κ (T0 + j) = (q₁ :: qs)[j].2 := fun j h => by
    obtain ⟨a, b⟩ := hι j (by rw [hql]; exact h)
    have hg := skReqs_get (s := s) ρ M (q₁ :: qs) j h
    rw [a, b]; simp only [hg, and_self]
  -- The last request (no step takes it) decided too: every request of the run is.
  let T' := T0 + (q₁ :: qs).length
  let r' := r1.last T' (sReq s (r1.st T') (r1.mp T') (fun _ => 0) noSets) noSets
  have hr' : r'.Ok s.sk T' := last_ok hr1 _ _
  have hd' : ∀ u, u ≤ T' → r'.Decided s u := by
    intro u hu
    by_cases huT : u = T'
    · subst huT; exact last_decided
    · refine last_other huT _ _ ?_
      rcases Nat.lt_or_ge u T0 with hlt0 | hge0
      · have h := hdec u (Nat.le_of_lt hlt0)
        obtain ⟨a, b⟩ := hle u (Nat.le_of_lt hlt0)
        obtain ⟨c', d⟩ := hlt u hlt0
        simp only [CRun.Decided, a, b, c', d] at h ⊢; exact h
      · obtain ⟨j, rfl⟩ : ∃ j, u = T0 + j := ⟨u - T0, by omega⟩
        have hjl : j < (q₁ :: qs).length := by simp only [T'] at hu huT; omega
        obtain ⟨ha, hm⟩ := hagj j (Nat.le_of_lt hjl)
        obtain ⟨hι', hκ'⟩ := hreqj j hjl
        simp only [CRun.Decided, hι', hκ', hm]
        rw [sReq_agree hs ha, sReq_idem]
  -- The node's environment: t and T the run's end, Ω one above it, the rest from before the start.
  obtain ⟨Q, hQt, hQT, hQo, hQr⟩ : ∃ Q : Nat → Nat, Q ce.t = T' ∧ Q ce.T = T' ∧ Q ce.om = T' + 1 ∧ ∀ i, i ∉ ce.special → Q i = r'.ρ0 i :=
    ⟨fun i => if i = ce.t then T' else if i = ce.T then T' else if i = ce.om then T' + 1 else r'.ρ0 i,
      by simp, by simp [Ne.symm hsp.2.2.2.2.2.1], by simp [Ne.symm hsp.2.2.2.2.2.2, Ne.symm hsp.2.2.2.2.1],
      fun i hi => by
        dsimp only
        rw [if_neg (fun e => hi (in_special (Or.inr (Or.inr (Or.inr (Or.inr e)))))), if_neg (fun e => hi (in_special (Or.inr (Or.inr (Or.inl e))))),
          if_neg (fun e => hi (in_special (Or.inr (Or.inr (Or.inr (Or.inl e))))))]⟩
  have hEnv : EnvOk s.sk ce s.bk r' T' Q := ⟨hQT, hQo, fun i hi => hQr i (notP hi).1⟩
  have hF : FactsHold facts Q (cycMaps s.sk ce r' (T' + 1)) := qfacts_all hs hS hT hr' hd' hbo hEnv hfa
  have hframe : ∀ u, u ≤ T' → ∀ i, i ∉ ce.vtr.map (·.1) → i ∉ flagVars s.f.flags → r'.st u i = r'.ρ0 i := fun u hu i hv hf =>
    run_frame hr' u hu i (fun h => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact hv (hS.initv p hp))
      (fun h => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact hv (hS.stepv p hp)) (fun h => hv (hS.inv i h)) hf
  have hwV : ∀ x, x ∉ ce.vtr.map (·.1) → x ∉ s.extVars := fun x hv h => hv (hS.inv x (by rw [sk_inputs]; exact h))
  have hwW : ∀ x, x ∉ ce.vtr.map (·.1) → x ∉ s.wVars := fun x hv h => hwV x hv (by simp only [SMachine.extVars, List.mem_append]; exact Or.inr h)
  -- What the run reads at T0 + j: the goal's view of the j-th step of the machine.
  have hXj : ∀ j (h : j < (q₁ :: qs).length), r'.X s.sk (T0 + j) = withExt s (sEnd s ρ M ((q₁ :: qs).take j)).1
      (sReq s (sEnd s ρ M ((q₁ :: qs).take j)).1 (sEnd s ρ M ((q₁ :: qs).take j)).2 (q₁ :: qs)[j].1 (q₁ :: qs)[j].2) := fun j h => by
    have hne : T0 + j ≠ T' := by simp only [T']; omega
    show withInputs s.sk.f.m.inputs (r1.st (T0 + j)) (if T0 + j = T' then _ else r1.ι (T0 + j)) = _
    rw [if_neg hne, (hreqj j h).1]
    exact sk_inputsView _ _ (hagj j (Nat.le_of_lt h)).1 _ _ _
  have hNj : ∀ j (h : j < (q₁ :: qs).length), r'.N s.sk (T0 + j) = withCarried s (sEnd s ρ M ((q₁ :: qs).take j)).2 (q₁ :: qs)[j].2 := fun j h => by
    have hne : T0 + j ≠ T' := by simp only [T']; omega
    show withCarried s.sk (r1.mp (T0 + j)) (if T0 + j = T' then _ else r1.κ (T0 + j)) = _
    rw [if_neg hne, (hreqj j h).2, (hagj j (Nat.le_of_lt h)).2]; rfl
  have hq0 : 0 < (q₁ :: qs).length := by simp
  have hw0 : evalE Q (cycMaps s.sk ce r' (T' + 1)) (tAtS tb ce sl.k.whens.length) = T0 := by rw [tAtS_eval tb, hQt, hk]; simp only [T']; omega
  -- The node's hypotheses hold there.
  have hH : ∀ c ∈ n.hyps, evalC Q (cycMaps s.sk ce r' (T' + 1)) c = true := by
    intro c hc
    have h := hhy c hc
    simp only [Bool.or_eq_true] at h
    rcases h with (((h | h) | h) | h) | h
    · rw [beqC_eq h, congr2C (ρ := Q) (M := cycMaps s.sk ce r' (T' + 1)) (ρ' := r'.ρ0) (M' := r'.mp 0) s.f.m.pre
        (fun j hj => hEnv.2.2 j (avoids_occ hT.prz hj)) (fun m hm => cm_o (avoidsMaps_occ hT.prm hm))]
      exact hr'.pre
    · rw [beqC_eq h, evalC_iff]; simp only [holdsC, evalE, hQt, hk]; simp only [T']; omega
    · rw [beqC_eq h, evalC_iff]; simp only [holdsC, evalE, hQt, hQT]; omega
    · rw [beqC_eq h, evalC_iff]; simp only [holdsC, evalE, hQT, hQo]; omega
    · obtain ⟨c', hc', hb⟩ := List.any_eq_true.mp h
      rw [beqC_eq hb]
      obtain ⟨i, hi, rfl⟩ := kWhens_mem tb ce sl.k.whens.length 0 sl.k.whens hc'
      have hiq : i < (q₁ :: qs).length := by omega
      have hu : T0 + i ≤ T' := by simp only [T']; omega
      have hwi : evalE Q (cycMaps s.sk ce r' (T' + 1)) (tAtS tb ce (sl.k.whens.length - (0 + i))) = T0 + i := by rw [tAtS_eval tb, hQt, hk]; simp only [T']; omega
      have hall := sallowed_at (q₁ :: qs) sl.k.whens ρ M hK i hiq hi
      have hav := hwh _ (List.getElem_mem hi)
      rw [enc_trC hS hT hr' hEnv hwi hu]
      rw [congr2C (ρ' := withExt s (sEnd s ρ M ((q₁ :: qs).take i)).1 (sReq s (sEnd s ρ M ((q₁ :: qs).take i)).1 (sEnd s ρ M ((q₁ :: qs).take i)).2 (q₁ :: qs)[i].1 (q₁ :: qs)[i].2))
        (M' := withCarried s (sEnd s ρ M ((q₁ :: qs).take i)).2 (q₁ :: qs)[i].2) _ ?_ ?_]
      · exact hall
      · intro x hx
        obtain ⟨hz, hfl⟩ := hcz x (avoids_occ hav.1 hx)
        rw [enc_Y hS hT hr' hEnv hwi hu hz hfl, hXj i hiq]
      · intro m hm
        rw [cv_N (avoidsMaps_occ hav.2 hm), hNj i hiq]
  have hc0 := cyclic_sound facts nodes hc (cycMaps s.sk ce r' (T' + 1)) Q hF n hn hH
  rw [beqC_eq hcon] at hc0
  -- `then` over the run: the maps it reads, then its names.
  have hTle : T0 ≤ T' := by simp only [T']; omega
  obtain ⟨hagE, hmE⟩ : Agree s.wVars (r'.st T') (sEnd s ρ M (q₁ :: qs)).1 ∧ r'.mp T' = (sEnd s ρ M (q₁ :: qs)).2 := by
    have h := hagj (q₁ :: qs).length (Nat.le_refl _); simp only [List.take_length] at h; exact h
  let Mt : Nat → Nat → Nat := primedMaps sl.k.primeMaps (sEnd s ρ M (q₁ :: qs)).2 (renMaps sl.mren ((q₁ :: qs).map (·.2)) (withCarried s M q₁.2))
  have hrd : ∀ m key, evalE Q (cycMaps s.sk ce r' (T' + 1)) (kRd tb ce sl m key)
      = (fun m => if ce.tm.contains m then cycMaps s.sk ce r' (T' + 1) m else Mt m) m (evalE Q (cycMaps s.sk ce r' (T' + 1)) key) := by
    intro m key
    simp only [kRd]
    cases hq : lookup (fun q => q.2 == m) sl.k.primeMaps with
    | some q =>
      obtain ⟨hqm, hqe⟩ := lookup_some hq
      have hqe' : q.2 = m := by simpa using hqe
      obtain ⟨⟨hq1, hq2⟩, hq3⟩ := hpm q hqm
      have hnt : ¬ ce.tm.contains m = true := by rw [← hqe']; simpa using hq3
      simp only [evalE, tAtS_eval tb, hQt, hQo, Nat.sub_zero]
      rw [read_mm hS.dtm (List.contains_iff_mem.mp hq1) (Nat.le_refl _), N_not_carried (show q.1 ∉ s.sk.carried from fun h => by simp only [Bool.not_eq_true'] at hq2; rw [List.contains_iff_mem.mpr (show q.1 ∈ s.carried from h)] at hq2; cases hq2), hmE, if_neg hnt]
      simp only [Mt, primedMaps, hq]
    | none =>
      have hkm := kMren_eval sl.mren 0 ((q₁ :: qs).map (·.2)) (withCarried s M q₁.2) m (by simp; omega)
      cases hkr : kMren 0 sl.mren m with
      | some p =>
        obtain ⟨i', hi', hκ', hi0, ⟨p', hp', hp1, hp2⟩, hren⟩ := hkm.2 p.1 p.2 hkr
        obtain ⟨hcar, hnt0⟩ := hmr _ (List.getElem_mem hi') p' hp'
        have hnt : ¬ ce.tm.contains m = true := by rw [← hp2]; simpa using hnt0
        have hiq : i' < (q₁ :: qs).length := by simpa using hκ'
        simp only [evalE, tAtS_eval tb, hQt, hQo, hi0, Nat.zero_add]
        rw [show T' - (sl.k.whens.length - i') = T0 + i' by rw [hk]; simp only [T']; omega]
        rw [read_mm hS.dtm (hS.carm _ (by rw [← hp1]; exact List.contains_iff_mem.mp hcar)) (by simp only [T']; omega), hNj i' hiq, if_neg hnt]
        simp only [Mt, primedMaps, hq, hren, withCarried, ← hp1, hcar, if_true, List.getElem_map]
      | none =>
        rw [enc_rd hS hT hr' hEnv hw0 hTle]
        simp only [cycView]
        by_cases ht : ce.tm.contains m = true
        · rw [if_pos ht, if_pos ht]
        · rw [if_neg ht, if_neg ht]
          have h0 := hNj 0 hq0
          simp only [Nat.add_zero, List.take_zero, sEnd, List.getElem_cons_zero] at h0
          rw [h0]
          simp only [Mt, primedMaps, hq, hkm.1 hkr]
  rw [substR_evalC (kσ tb ce sl) (kRd tb ce sl) Q _ _ hrd] at hc0
  rw [congr2C (ρ' := primed sl.k.prime (sEnd s ρ M (q₁ :: qs)).1 (renEnv sl.k.ren (sExts s ρ M (q₁ :: qs)) (withExt s ρ (sReq s ρ M q₁.1 q₁.2))))
    (M' := Mt) _ ?_ ?_] at hc0
  · exact hc0
  · intro x hx
    obtain ⟨hz, hfl⟩ := hcz x (avoids_occ hthv hx)
    simp only [kσ, List.append_assoc]
    rw [applyS_app, assoc_ren]
    simp only [primed]
    cases hq : lookup (fun q => q.2 == x) sl.k.prime with
    | some q =>
      obtain ⟨hqm, _⟩ := lookup_some hq
      obtain ⟨hq1, hq2⟩ := hpr q hqm
      have hqw : q.1 ∉ s.wVars := fun h => by
        simp only [Bool.not_eq_true'] at hq2
        rw [List.contains_iff_mem.mpr (by rw [sk_inputs]; simp only [SMachine.extVars, List.mem_append]; exact Or.inr h)] at hq2; cases hq2
      simp only [Option.map_some, evalE, tAtS_eval tb, hQt, Nat.sub_zero]
      rw [read_vm hS.dtm (List.contains_iff_mem.mp hq1), CRun.X, withInputs_other (by simpa using hq2), hagE q.1 hqw]
    | none =>
      simp only [Option.map_none]
      by_cases hxr : x ∈ tgts sl.k.ren
      · have hel : ∀ ρ M (qs : List SRequest), (sExts s ρ M qs).length = qs.length := by
          intro ρ M qs; induction qs generalizing ρ M with
          | nil => rfl
          | cons q qs ih => simp [sExts, ih]
        rw [kRen_eval tb ce sl.k.whens.length Q _ _ _ sl.k.ren 0 (sExts s ρ M (q₁ :: qs)) (by rw [hel]; omega) ?_ x hxr]
        intro i hi hιl p hp
        have hpin := hrin _ (List.getElem_mem hi) p hp
        have hiq : i < (q₁ :: qs).length := by rw [hel] at hιl; exact hιl
        simp only [evalE, tAtS_eval tb, hQt, Nat.zero_add]
        rw [show T' - (sl.k.whens.length - i) = T0 + i by rw [hk]; simp only [T']; omega]
        rw [read_vm hS.dtm (hS.inv _ (List.contains_iff_mem.mp hpin)), hXj i hiq, sExts_get ρ M (q₁ :: qs) i hiq]
        simp only [withExt, show s.extVars.contains p.1 = true from by rw [← sk_inputs]; exact hpin, if_true]
      · rw [kRen_out tb ce sl.k.whens.length Q _ _ sl.k.ren 0 x hxr, renEnv_other _ _ _ x hxr]
        have hX0 := hXj 0 hq0
        simp only [Nat.add_zero, List.take_zero, sEnd, List.getElem_cons_zero] at hX0
        by_cases hv : x ∈ ce.vtr.map (·.1)
        · rw [enc_σ_in hS hT hr' hEnv hw0 hTle hv, hX0]
        · rw [enc_σ_out hS hT hr' hEnv hw0 hTle hv, hQr x (fun h => hz (List.mem_append_left _ h))]
          simp only [withExt, show s.extVars.contains x = false from by simpa [List.contains_iff_mem] using hwV x hv, Bool.false_eq_true, if_false]
          have h0 := hagj 0 (Nat.zero_le _)
          simp only [Nat.add_zero, List.take_zero, sEnd] at h0
          rw [← h0.1 x (hwW x hv)]
          exact (hframe T0 hTle x hv hfl).symm
  · intro m hm
    simp only [if_neg (fun h => avoidsMaps_occ hthm hm (List.contains_iff_mem.mp h))]


def cycQKOk (s : SMachine) (ce : CycEnc) (facts : List Fact) (sl : SKStep) (n : CNode) : Bool :=
  cycQKOkAt true s ce facts sl n || cycQKOkAt false s ce facts sl n

theorem cyc_qkstep_sound (s : SMachine) (ce : CycEnc) (facts : List Fact) (nodes : List CNode) (hc : checkCyclic facts nodes = true)
    (sl : SKStep) (n : CNode) (hn : n ∈ nodes) (hok : cycQKOk s ce facts sl n = true) : SKStepHolds s sl := by
  simp only [cycQKOk, Bool.or_eq_true] at hok
  rcases hok with h | h
  · exact cyc_qkstep_sound_at true s ce facts nodes hc sl n hn h
  · exact cyc_qkstep_sound_at false s ce facts nodes hc sl n hn h

/-- A request allowed, as a node for a machine with flags that hold at every key (`cycAOk` over its sk machine, those
flags' facts, the flags' keys apart). -/
def cycQAOk (s : SMachine) (ce : CycEnc) (facts : List Fact) (w : C) (n : CNode) : Bool :=
  sOk s && cycShapeOk s.sk ce s.bk && cycTermsOk s.sk ce s.bk && cycBodyOk s ce s.bk && cycQFactsIn s ce facts
    && avoids (ce.special ++ s.bk ++ flagVars s.f.flags) w && avoidsMaps ce.tm w
    && beqC n.concl (trC ce (.var ce.t) (inlineC s.f.flags s.f.m.assume))
    && n.hyps.all (fun h => beqC h s.f.m.pre || beqC h (.le (.var ce.t) (.var ce.T)) || beqC h (.lt (.var ce.T) (.var ce.om))
      || beqC h (trC ce (.var ce.t) w) || cycZeroOk s ce h)

theorem cyc_qallow_sound (s : SMachine) (ce : CycEnc) (facts : List Fact) (nodes : List CNode) (hc : checkCyclic facts nodes = true)
    (w : C) (n : CNode) (hn : n ∈ nodes) (hok : cycQAOk s ce facts w n = true) : AllowHolds s w := by
  simp only [cycQAOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hs, hsh⟩, hte⟩, hbo⟩, hfa⟩, hwv⟩, hwm⟩, hcon⟩, hhy⟩ := hok
  have hS := cycShape_of hsh
  have hT := cycTerms_of hte
  have hsp := special_parts hS.dsp
  intro ρ M hr ι hw
  obtain ⟨r, T, hr0, hd, hag, hmp⟩ := sk_run hs hr
  -- The run with the request at T (the last, which no step takes) the claim's, decided, carrying empty sets.
  let r2 := r.last T (sReq s ρ M ι noSets) noSets
  have hr2 : r2.Ok s.sk T := last_ok hr0 _ _
  have hd2 : ∀ u, u ≤ T → r2.Decided s u := by
    intro u hu
    by_cases huT : u = T
    · subst huT
      simp only [CRun.Decided, r2, CRun.last, ↓reduceIte, hmp]
      rw [sReq_agree hs hag, sReq_idem]
    · exact last_other huT _ _ (hd u hu)
  have hX : r2.X s.sk T = withExt s ρ (sReq s ρ M ι noSets) := by
    show withInputs s.sk.f.m.inputs (r.st T) (if T = T then sReq s ρ M ι noSets else r.ι T) = _
    rw [if_pos rfl]; exact sk_inputsView _ _ hag _ _ _
  have hN : r2.N s.sk T = withCarried s M noSets := by
    show withCarried s.sk (r.mp T) (if T = T then noSets else r.κ T) = _
    rw [if_pos rfl, hmp]; rfl
  obtain ⟨Q, hQt, hQT, hQo, hQr⟩ : ∃ Q : Nat → Nat, Q ce.t = T ∧ Q ce.T = T ∧ Q ce.om = T + 1 ∧ ∀ i, i ∉ ce.special → Q i = r.ρ0 i :=
    ⟨fun i => if i = ce.t then T else if i = ce.T then T else if i = ce.om then T + 1 else r.ρ0 i,
      by simp, by simp [Ne.symm hsp.2.2.2.2.2.1], by simp [Ne.symm hsp.2.2.2.2.2.2, Ne.symm hsp.2.2.2.2.1],
      fun i hi => by
        dsimp only
        rw [if_neg (fun e => hi (in_special (Or.inr (Or.inr (Or.inr (Or.inr e)))))), if_neg (fun e => hi (in_special (Or.inr (Or.inr (Or.inl e))))),
          if_neg (fun e => hi (in_special (Or.inr (Or.inr (Or.inr (Or.inl e))))))]⟩
  have hEnv : EnvOk s.sk ce s.bk r2 T Q := ⟨hQT, hQo, fun i hi => hQr i (notP hi).1⟩
  have hwt : evalE Q (cycMaps s.sk ce r2 (T + 1)) (.var ce.t) = T := by simp [evalE, hQt]
  have hF : FactsHold facts Q (cycMaps s.sk ce r2 (T + 1)) := qfacts_all hs hS hT hr2 hd2 hbo hEnv hfa
  have hH : ∀ c ∈ n.hyps, evalC Q (cycMaps s.sk ce r2 (T + 1)) c = true := by
    intro c hc
    have h := hhy c hc
    simp only [Bool.or_eq_true] at h
    rcases h with ((((h | h) | h) | h) | h)
    · rw [beqC_eq h, congr2C (ρ := Q) (M := cycMaps s.sk ce r2 (T + 1)) (ρ' := r2.ρ0) (M' := r2.mp 0) s.f.m.pre
        (fun j hj => hEnv.2.2 j (avoids_occ hT.prz hj)) (fun m hm => cm_o (avoidsMaps_occ hT.prm hm))]
      exact hr2.pre
    · rw [beqC_eq h, evalC_iff]; simp only [holdsC, evalE, hQt, hQT]; omega
    · rw [beqC_eq h, evalC_iff]; simp only [holdsC, evalE, hQT, hQo]; omega
    · rw [beqC_eq h, enc_trC hS hT hr2 hEnv hwt (Nat.le_refl T)]
      rw [congr2C (ρ' := withExt s ρ (sReq s ρ M ι noSets)) (M' := withCarried s M noSets) _ ?_ ?_]
      · exact hw
      · intro x hx
        have hxz := avoids_occ hwv hx
        rw [enc_Y hS hT hr2 hEnv hwt (Nat.le_refl T) (fun h => hxz (List.mem_append_left _ h)) (fun h => hxz (List.mem_append_right _ h)), hX]
      · intro m hm
        rw [cv_N (avoidsMaps_occ hwm hm), hN]
    · obtain ⟨cm, key, hcm, rfl⟩ := cycZeroOk_spec h
      rw [evalC_iff]
      simp only [holdsC, evalE, hQt, hQo]
      rw [read_mm hS.dtm (hS.carm cm hcm) (Nat.le_refl T), hN]
      simp only [withCarried, List.contains_iff_mem.mpr hcm, if_true, noSets]
  have hc0 := cyclic_sound facts nodes hc (cycMaps s.sk ce r2 (T + 1)) Q hF n hn hH
  rw [beqC_eq hcon] at hc0
  change evalC Q _ (trC ce (.var ce.t) (inlineC s.sk.f.flags s.f.m.assume)) = true at hc0
  rw [enc_nowC hS hT hr2 hEnv hwt (Nat.le_refl T) s.f.m.assume hT.asz hT.asm] at hc0
  obtain ⟨hV, hNv⟩ := sk_view hs hag M ι noSets
  have hV2 : r2.V s.sk T = (sView s.sk (r.st T) M (sReq s ρ M ι noSets) noSets).1 := by
    rw [sk_view_eq _ _ hag]; simp only [CRun.V, hX, hN]; rfl
  have hN2 : r2.N s.sk T = (sView s ρ M ι noSets).2 := by rw [hN]; rfl
  obtain ⟨_, _, _, has, _⟩ := sOk_terms hs
  rw [hV2, hN2, congrC _ (sView s ρ M ι noSets).1 _ s.f.m.assume (fun j hj => hV j (avoids_occ has hj))] at hc0
  exact hc0

end Kern

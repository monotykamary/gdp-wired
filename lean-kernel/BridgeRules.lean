import Bridge
import Refine
import History

/-!
BridgeRules: the rest of today's rules carried by cyclic proofs. Lean 4.34.0, core only, on top of `Bridge.lean`.

Bridge.lean carries a cyclic proof's node to a machine's law about every reachable state. The rules beside the laws
claim more: a step law (and a k-step law) is about every k allowed requests in a row from every reachable state. Here
a node over the same encoding, at time t with t + k ≤ T, reads the k requests at times t, …, t + k − 1 and the state
after them at t + k: its hypotheses among the precondition, t + k ≤ T, T < Ω and each step's `when` at its time, its
conclusion `then` with each later request's inputs at their time, the primed names at t + k and the maps a later request
carries at its time (`cycKOk`). `cyc_kstep_sound`: such a node of a checked cyclic proof makes the k-step law hold, as
Sets.lean's `SKStepHolds` states it (the claim `skstep_sound` proves of the usual certificate). The run is the one a
reachable state ends (`reach_run`), extended by the k requests (`run_ext`).
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

-- Time t + j.
def tAt (ce : CycEnc) : Nat → E
  | 0 => .var ce.t
  | j + 1 => .add (.var ce.t) (.const (j + 1))

theorem tAt_eval (ce : CycEnc) (Q : Nat → Nat) (M : Nat → Nat → Nat) : ∀ j, evalE Q M (tAt ce j) = Q ce.t + j
  | 0 => by simp [tAt, evalE]
  | j + 1 => by simp [tAt, evalE]

-- The map over time of a traced variable, and of a map.
def cycVM (ce : CycEnc) (x : Nat) : Nat := ((lookup (fun p => p.1 == x) ce.vtr).map (·.2)).getD 0
def cycMM (ce : CycEnc) (m : Nat) : Nat := ((lookup (fun p => p.1 == m) ce.mtr).map (·.2)).getD 0

-- Each later request's inputs at their fresh names, read at its time.
def kRenσ (ce : CycEnc) : Nat → List (List (Nat × Nat)) → List (Nat × E)
  | _, [] => []
  | j, r :: rs => r.map (fun p => (p.2, .get (cycVM ce p.1) (tAt ce j))) ++ kRenσ ce (j + 1) rs

-- The step and the carried map a fresh map name stands for.
def kMren : Nat → List (List (Nat × Nat)) → Nat → Option (Nat × Nat)
  | _, [], _ => none
  | j, r :: rs, m => match lookup (fun p => p.2 == m) r with
    | some p => some (j, p.1)
    | none => kMren (j + 1) rs m

-- `then` over the run: primed names at t + k, each later request's inputs at their time, the rest at t.
def kσ (ce : CycEnc) (sl : SKStep) : List (Nat × E) :=
  sl.k.prime.map (fun q => (q.2, .get (cycVM ce q.1) (tAt ce sl.k.whens.length))) ++ kRenσ ce 0 sl.k.ren ++ cycσ ce (tAt ce 0)
def kRd (ce : CycEnc) (sl : SKStep) : Nat → E → E := fun m key =>
  match lookup (fun q => q.2 == m) sl.k.primeMaps with
  | some q => .get (cycMM ce q.1) (.add (tAt ce sl.k.whens.length) (.prod key (.var ce.om)))
  | none => match kMren 0 sl.mren m with
    | some p => .get (cycMM ce p.2) (.add (tAt ce p.1) (.prod key (.var ce.om)))
    | none => cycRd ce (tAt ce 0) m key

-- Each step's `when` at its time.
def kWhens (ce : CycEnc) : Nat → List C → List C
  | _, [] => []
  | j, w :: ws => trC ce (tAt ce j) w :: kWhens ce (j + 1) ws

theorem kWhens_mem (ce : CycEnc) : ∀ (j : Nat) (ws : List C) {c : C}, c ∈ kWhens ce j ws → ∃ i, ∃ h : i < ws.length, c = trC ce (tAt ce (j + i)) ws[i]
  | _, [], _, h => by simp [kWhens] at h
  | j, w :: ws, c, h => by
    simp only [kWhens, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by simp, by simp⟩
    · obtain ⟨i, hi, rfl⟩ := kWhens_mem ce (j + 1) ws h
      exact ⟨i + 1, by simp; omega, by simp [Nat.add_assoc, Nat.add_comm 1 i]⟩

/-- A k-step law's node, checked against the machine's encoding: the encoding fits the machine as for its laws, the
law's fresh names stand for traced inputs and state variables and the maps for maps over time, `then` and each `when`
read no added variable, flag or map over time, the conclusion is `then` over the run (`kσ`, `kRd`) and the hypotheses
are among the precondition, t + k ≤ T, T < Ω and each step's `when` at its time. -/
def cycKOk (s : SMachine) (ce : CycEnc) (facts : List Fact) (sl : SKStep) (n : CNode) : Bool :=
  cycShapeOk s ce [] && cycTermsOk s ce [] && s.wits.isEmpty && cycFactsIn s ce facts
    && sl.k.ren.length == sl.k.whens.length && sl.mren.length == sl.k.whens.length
    && sl.k.ren.all (fun r => r.all fun p => s.f.m.inputs.contains p.1)
    && sl.k.prime.all (fun q => (ce.vtr.map (·.1)).contains q.1 && !s.f.m.inputs.contains q.1)
    && sl.mren.all (fun r => r.all fun p => s.carried.contains p.1 && !ce.tm.contains p.2)
    && sl.k.primeMaps.all (fun q => (ce.mtr.map (·.1)).contains q.1 && !s.carried.contains q.1 && !ce.tm.contains q.2)
    && avoids (ce.special ++ flagVars s.f.flags) sl.k.then_ && avoidsMaps ce.tm sl.k.then_
    && sl.k.whens.all (fun w => avoids (ce.special ++ flagVars s.f.flags) w && avoidsMaps ce.tm w)
    && beqC n.concl (substRC (kσ ce sl) (kRd ce sl) sl.k.then_)
    && n.hyps.all (fun h => beqC h s.f.m.pre || beqC h (.le (tAt ce sl.k.whens.length) (.var ce.T)) || beqC h (.lt (.var ce.T) (.var ce.om))
      || (kWhens ce 0 sl.k.whens).any (beqC h))

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
theorem kRen_eval (ce : CycEnc) (Q : Nat → Nat) (cm : Nat → Nat → Nat) (b : Nat → Nat) (rest : List (Nat × E)) :
    ∀ (rs : List (List (Nat × Nat))) (j : Nat) (ιs : List (Nat → Nat)), rs.length ≤ ιs.length →
      (∀ i (hi : i < rs.length) (hι : i < ιs.length), ∀ p ∈ rs[i], evalE Q cm (.get (cycVM ce p.1) (tAt ce (j + i))) = ιs[i] p.1) →
      ∀ v, v ∈ tgts rs → applyS (kRenσ ce j rs ++ rest) Q cm v = renEnv rs ιs b v
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
      exact kRen_eval ce Q cm b rest rs (j + 1) ιs (by simp at hl; omega)
        (fun i hi hι p hp => by
          have := hX (i + 1) (by simp; omega) (by simp; omega) p (by simpa using hp)
          simpa [Nat.add_assoc, Nat.add_comm 1 i] using this) v (not_tgt_cons hv hr)

theorem kRen_out (ce : CycEnc) (Q : Nat → Nat) (cm : Nat → Nat → Nat) (rest : List (Nat × E)) :
    ∀ (rs : List (List (Nat × Nat))) (j : Nat) (v : Nat), v ∉ tgts rs → applyS (kRenσ ce j rs ++ rest) Q cm v = applyS rest Q cm v
  | [], _, _, _ => by simp [kRenσ]
  | r :: rs, j, v, hv => by
    simp only [kRenσ, List.append_assoc]
    rw [applyS_app, assoc_ren]
    have hn : lookup (fun p => p.2 == v) r = none := lookup_none (fun p hp => by
      simp only [beq_eq_false_iff_ne]; intro he; exact hv (by simp only [tgts, List.mem_append]; exact Or.inl (List.mem_map.mpr ⟨p, hp, he⟩)))
    simp only [hn, Option.map_none]
    exact kRen_out ce Q cm rest rs (j + 1) v (fun h => hv (by simp only [tgts, List.mem_append]; exact Or.inr h))

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

/-- A cyclic proof of a k-step law (a step law, k = 1), checked against the machine's encoding (`cycKOk`): from every
reachable state, every k requests in a row the machine allows, each meeting its `when`, end where `then` holds. -/
theorem cyc_kstep_sound (s : SMachine) (ce : CycEnc) (facts : List Fact) (nodes : List CNode) (hc : checkCyclic facts nodes = true)
    (sl : SKStep) (n : CNode) (hn : n ∈ nodes) (hok : cycKOk s ce facts sl n = true) : SKStepHolds s sl := by
  simp only [cycKOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsh, hte⟩, hwit⟩, hfa⟩, hrl⟩, hml⟩, hrin⟩, hpr⟩, hmr⟩, hpm⟩, hthv⟩, hthm⟩, hwh⟩, hcon⟩, hhy⟩ := hok
  have hS := cycShape_of hsh
  have hT := cycTerms_of hte
  have hW : s.wits = [] := isEmpty_nil hwit
  have hsp := special_parts hS.dsp
  intro ρ M hr q₁ qs hlen hK
  obtain ⟨r, T0, hr0, hst, hmp⟩ := reach_run hS.q hr
  obtain ⟨r', hr', _, _, _, hj, hι⟩ := run_ext hS.q (q₁ :: qs) sl.k.whens r T0 ρ M hr0 hst hmp (by simp; omega) hK
  have hk : sl.k.whens.length = (q₁ :: qs).length := by simp; omega
  -- The node's environment: t the state's time, T the run's end, Ω one above it, the rest from before the start.
  obtain ⟨Q, hQt, hQT, hQo, hQr⟩ : ∃ Q : Nat → Nat, Q ce.t = T0 ∧ Q ce.T = T0 + (q₁ :: qs).length ∧ Q ce.om = T0 + (q₁ :: qs).length + 1
      ∧ ∀ i, i ∉ ce.special → Q i = r'.ρ0 i :=
    ⟨fun i => if i = ce.t then T0 else if i = ce.T then T0 + (q₁ :: qs).length else if i = ce.om then T0 + (q₁ :: qs).length + 1 else r'.ρ0 i,
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
  have hw0 : evalE Q (cycMaps s ce r' (T0 + (q₁ :: qs).length + 1)) (tAt ce 0) = T0 := by rw [tAt_eval, hQt]; rfl
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
    rcases h with ((h | h) | h) | h
    · rw [beqC_eq h, congr2C (ρ' := r'.ρ0) (M' := r'.mp 0) _ (fun j hj => hEnv.2.2 j (avoids_occ hT.prz hj))
        (fun m hm => cm_o (avoidsMaps_occ hT.prm hm))]
      exact hr'.pre
    · rw [beqC_eq h, evalC_iff]; simp only [holdsC, evalE, tAt_eval, hQt, hQT, hk]; omega
    · rw [beqC_eq h, evalC_iff]; simp only [holdsC, evalE, hQT, hQo]; omega
    · obtain ⟨c', hc', hb⟩ := List.any_eq_true.mp h
      rw [beqC_eq hb]
      obtain ⟨i, hi, rfl⟩ := kWhens_mem ce 0 sl.k.whens hc'
      have hiq : i < (q₁ :: qs).length := by omega
      have hu : T0 + i ≤ T0 + (q₁ :: qs).length := by omega
      have hwi : evalE Q (cycMaps s ce r' (T0 + (q₁ :: qs).length + 1)) (tAt ce (0 + i)) = T0 + i := by rw [tAt_eval, hQt]; omega
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
  have hrd : ∀ m key, evalE Q (cycMaps s ce r' (T0 + (q₁ :: qs).length + 1)) (kRd ce sl m key)
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
      simp only [evalE, tAt_eval, hQt, hQo, hk]
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
        simp only [evalE, tAt_eval, hQt, hQo, hi0, Nat.zero_add]
        rw [read_mm hS.dtm (hS.carm _ (by rw [← hp1]; exact List.contains_iff_mem.mp hcar)) (by omega), CRun.N, hκi, if_neg hnt]
        simp only [Mt, primedMaps, hq, hren, withCarried, ← hp1, hcar, if_true, List.getElem_map]
      | none =>
        rw [enc_rd hS hT hr' hEnv hw0 hTle]
        simp only [cycView]
        by_cases ht : ce.tm.contains m = true
        · rw [if_pos ht, if_pos ht]
        · rw [if_neg ht, if_neg ht, CRun.N, hst0.2, hι0.2]
          simp only [Mt, primedMaps, hq, hkm.1 hkr]
  rw [substR_evalC (kσ ce sl) (kRd ce sl) Q _ _ hrd] at hc0
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
      simp only [Option.map_some, evalE, tAt_eval, hQt, hk]
      rw [read_vm hS.dtm (List.contains_iff_mem.mp hq1), CRun.X, withInputs_other (by simpa using hq2), hend.1]
    | none =>
      simp only [Option.map_none]
      by_cases hxr : x ∈ tgts sl.k.ren
      · rw [kRen_eval ce Q _ _ _ sl.k.ren 0 (sExts s ρ M (q₁ :: qs)) (by rw [sExts_plain hS.q hW]; simp; omega) ?_ x hxr]
        intro i hi hιl p hp
        have hpin := hrin _ (List.getElem_mem hi) p hp
        have hiq : i < (q₁ :: qs).length := by rw [sExts_plain hS.q hW] at hιl; simpa using hιl
        obtain ⟨hιi, _⟩ := hι i hiq
        simp only [evalE, tAt_eval, hQt, Nat.zero_add]
        rw [read_vm hS.dtm (hS.inv _ (List.contains_iff_mem.mp hpin)), CRun.X]
        simp only [withInputs, hpin, if_true, hιi]
        have hx : ∀ (l : List (Nat → Nat)), l = (q₁ :: qs).map (fun q v => if s.f.m.inputs.contains v then q.1 v else 0) →
            ∀ h : i < l.length, (q₁ :: qs)[i].1 p.1 = l[i] p.1 := by
          intro l hl h; subst hl; simp only [List.getElem_map, hpin, if_true]
        exact hx _ (sExts_plain hS.q hW _ _ _) hιl
      · rw [kRen_out ce Q _ _ sl.k.ren 0 x hxr, renEnv_other _ _ _ x hxr, withExt_plain hS.q hW, sReq_plain hS.q hW]
        by_cases hv : x ∈ ce.vtr.map (·.1)
        · rw [enc_σ_in hS hT hr' hEnv hw0 hTle hv, CRun.X, hst0.1, hι0.1]; simp only [withInputs]; split <;> rfl
        · have hxi : x ∉ s.f.m.inputs := fun h => hv (hS.inv x h)
          rw [enc_σ_out hS hT hr' hEnv hw0 hTle hv, if_neg (fun h => hxi (List.contains_iff_mem.mp h)), ← hst0.1,
            hframe _ hTle x hv (fun h => hxz (List.mem_append_right _ h))]
          exact hQr x (fun h => hxz (List.mem_append_left _ h))
  · intro m hm
    simp only [if_neg (fun h => avoidsMaps_occ hthm hm (List.contains_iff_mem.mp h))]

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

end Kern

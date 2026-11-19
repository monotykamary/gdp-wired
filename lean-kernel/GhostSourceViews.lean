-- Generic structural transport reused from feat/grouped-sums@3a397980d.
-- No machine, field, law, or proof tree is encoded in this library.
import GhostMap

open Kern

namespace Kern.GhostSourceViews

private abbrev Env := Nat → Nat
private abbrev Maps := Nat → Nat → Nat
private abbrev Flag := Nat × C
private abbrev QFlag := Nat × List Nat × C

private def liftFlag (binder : Nat → Nat) (p : Flag) : QFlag :=
  (p.1, [binder p.1], p.2)

def promote (s : SMachine) (binder : Nat → Nat)
    (ws : List (Nat × List Nat)) : SMachine :=
  { s with
    f := { s.f with flags := [] }
    qflags := s.f.flags.map (liftFlag binder)
    wits := ws }

def bindersOK (s : SMachine) (binder : Nat → Nat) : Bool :=
  s.f.flags.all fun p => !occC (binder p.1) p.2

private theorem hit_mem {α : Type} (test : α → Bool) (xs : List α) (a : α)
    (h : lookup test xs = some a) : a ∈ xs := by
  induction xs with
  | nil => simp [lookup] at h
  | cons x xs ih =>
    cases hx : test x with
    | false =>
      exact List.mem_cons_of_mem _ (ih (by simpa [lookup, hx] using h))
    | true =>
      have he : x = a := by simpa [lookup, hx] using h
      simp [he]

private theorem hit_test {α : Type} (test : α → Bool) (xs : List α) (a : α)
    (h : lookup test xs = some a) : test a = true := by
  induction xs with
  | nil => simp [lookup] at h
  | cons x xs ih =>
    cases hx : test x with
    | false => exact ih (by simpa [lookup, hx] using h)
    | true =>
      have he : x = a := by simpa [lookup, hx] using h
      simpa [← he] using hx

private theorem lift_hit (b : Nat → Nat) (i : Nat) (fs : List Flag) :
    lookup (fun q : QFlag => q.1 == i) (fs.map (liftFlag b)) =
      (lookup (fun p : Flag => p.1 == i) fs).map (liftFlag b) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    cases hp : p.1 == i with
    | false => simpa [lookup, liftFlag, hp] using ih
    | true => simp [lookup, liftFlag, hp]

private theorem unused_key (X : Env) (N : Maps) (b : Nat) (c : C)
    (h : occC b c = false) :
    (∀ v, holdsC (atKeys X [b] v) N c) ↔ evalC X N c = true := by
  have he (v : Env) : evalC (atKeys X [b] v) N c = evalC X N c := by
    apply congrC
    intro i hi
    have hn : i ≠ b := by
      intro e
      subst i
      simp [h] at hi
    exact atKeys_out (by simpa using hn)
  constructor
  · intro hall
    rw [← he X]
    exact (evalC_iff _ _ _).mpr (hall X)
  · intro hc v
    apply (evalC_iff _ _ _).mp
    rwa [he v]

private theorem promoted_bits (s : SMachine) (b : Nat → Nat)
    (ws : List (Nat × List Nat)) (hb : bindersOK s b = true)
    (X : Env) (N : Maps) :
    decideQ (promote s b ws) X N = decideFlags s.f.flags X N := by
  classical
  have fresh : ∀ p ∈ s.f.flags, occC (b p.1) p.2 = false := by
    simpa [bindersOK] using hb
  funext i
  simp only [decideQ, promote, lift_hit, decideFlags, applyS, assoc_flagSub,
    flagOf]
  cases hh : lookup (fun p : Flag => p.1 == i) s.f.flags with
  | none => rfl
  | some p =>
    have hp := fresh p (hit_mem _ _ _ hh)
    have hk := unused_key X N (b p.1) p.2 hp
    cases hc : evalC X N p.2 <;>
      simp [liftFlag, hk, hc, evalE]

private theorem empty_bits (s : SMachine) (hq : s.qflags = [])
    (X : Env) (N : Maps) : decideQ s X N = X := by
  funext i
  simp [decideQ, hq, lookup]

theorem promote_view (s : SMachine) (b : Nat → Nat)
    (ws : List (Nat × List Nat)) (hq : s.qflags = [])
    (hb : bindersOK s b = true) : sView (promote s b ws) = sView s := by
  funext ρ M ι κ
  let X := withInputs s.f.m.inputs ρ ι
  let N := withCarried s M κ
  change (decideQ (promote s b ws) X N, N) =
    (decideFlags s.f.flags (decideQ s X N) N, N)
  rw [empty_bits s hq, promoted_bits s b ws hb]

theorem promote_next (s : SMachine) (b : Nat → Nat)
    (ws : List (Nat × List Nat)) (hq : s.qflags = [])
    (hb : bindersOK s b = true) : sNext (promote s b ws) = sNext s := by
  funext ρ M ι κ
  simp only [sNext, promote_view s b ws hq hb]
  rfl

private theorem transport {s t : SMachine}
    (hm : s.f.m = t.f.m) (hf : s.facts = t.facts)
    (hp : s.pfacts = t.pfacts) (hv : sView s = sView t)
    (hn : sNext s = sNext t) {ρ M} (hr : SReach s ρ M) :
    SReach t ρ M := by
  induction hr with
  | start X N hM hc hl hpl =>
    rw [hm]
    apply SReach.start
    · simpa only [hm] using hM
    · simpa only [hm] using hc
    · simpa only [hf] using hl
    · simpa only [SMachine.PFacts, hp] using hpl
  | step X N ι κ _ hc ih =>
    rw [hn]
    exact SReach.step X N ι κ ih (by simpa only [hm, hv] using hc)

theorem promote_reach (s : SMachine) (b : Nat → Nat)
    (ws : List (Nat × List Nat)) (hq : s.qflags = [])
    (hb : bindersOK s b = true) {ρ M} :
    SReach (promote s b ws) ρ M ↔ SReach s ρ M := by
  have hv := promote_view s b ws hq hb
  have hn := promote_next s b ws hq hb
  exact ⟨transport (s := promote s b ws) (t := s) rfl rfl rfl hv hn,
         transport (s := s) (t := promote s b ws) rfl rfl rfl hv.symm hn.symm⟩

-- Supply literal identity proofs, not observations of selected executions.
theorem candidate_reach {source candidate : SMachine} (b : Nat → Nat)
    (ws : List (Nat × List Nat)) (hid : candidate = promote source b ws)
    (hq : source.qflags = []) (hb : bindersOK source b = true) {ρ M} :
    SReach candidate ρ M ↔ SReach source ρ M := by
  subst candidate
  exact promote_reach source b ws hq hb

private theorem readE (X : Env) (N : Maps) (o g : Nat) (e : E)
    (h : occE o e = false) : evalE (upd X o g) N e = evalE X N e := by
  apply congrE
  intro i hi
  by_cases eq : i = o
  · subst i
    simp [h] at hi
  · simp [upd, eq]

private theorem readC (X : Env) (N : Maps) (o g : Nat) (c : C)
    (h : occC o c = false) : evalC (upd X o g) N c = evalC X N c := by
  apply congrC
  intro i hi
  by_cases eq : i = o
  · subst i
    simp [h] at hi
  · simp [upd, eq]

private def assignsOK (o : Nat) (xs : List (Nat × E)) : Bool :=
  xs.all fun p => !(p.1 == o) && !occE o p.2

def observerOK (s : SMachine) (o : Nat) : Bool :=
  !s.f.m.inputs.contains o &&
  !occC o s.f.m.pre &&
  !occC o s.f.m.assume &&
  assignsOK o s.f.m.init &&
  assignsOK o s.f.m.step &&
  (s.f.flags.all fun p => !(p.1 == o) && !occC o p.2) &&
  (s.f.m.writes.all fun w => !occE o w.2.1 && !occE o w.2.2) &&
  (s.every.all fun w => !occE o w.2.2)

private theorem assoc_member (xs : List (Nat × E)) (i : Nat) (e : E)
    (h : assoc xs i = some e) : (i, e) ∈ xs := by
  induction xs with
  | nil => simp [assoc, lookup] at h
  | cons p xs ih =>
    obtain ⟨j, a⟩ := p
    by_cases hj : j = i
    · subst j
      have ha : a = e := by simpa [assoc, lookup] using h
      simp [ha]
    · exact List.mem_cons_of_mem _ (ih (by
        simpa [assoc, lookup, hj, Ne.symm hj] using h))

private theorem assigns_upd (xs : List (Nat × E)) (X : Env) (N : Maps)
    (o g : Nat) (h : assignsOK o xs = true) :
    applyS xs (upd X o g) N = upd (applyS xs X N) o g := by
  have fresh : ∀ p ∈ xs, p.1 ≠ o ∧ occE o p.2 = false := by
    simpa [assignsOK] using h
  funext i
  cases ha : assoc xs i with
  | none => simp [applyS, upd, ha]
  | some e =>
    have hp := fresh (i, e) (assoc_member xs i e ha)
    simp [applyS, upd, ha, hp.1, readE X N o g e hp.2]

private theorem inputs_upd (ins : List Nat) (o g : Nat) (X I : Env)
    (h : o ∉ ins) :
    withInputs ins (upd X o g) I = upd (withInputs ins X I) o g := by
  funext i
  by_cases hi : i = o
  · subst i
    simp [withInputs, upd, List.contains_iff_mem, h]
  · simp [withInputs, upd, hi]

private theorem flags_upd (fs : List Flag) (X : Env) (N : Maps)
    (o g : Nat) (fresh : ∀ p ∈ fs, p.1 ≠ o ∧ occC o p.2 = false) :
    decideFlags fs (upd X o g) N = upd (decideFlags fs X N) o g := by
  funext i
  simp only [decideFlags, applyS, assoc_flagSub, flagOf, upd]
  cases hh : lookup (fun p : Flag => p.1 == i) fs with
  | none => rfl
  | some p =>
    have hp := fresh p (hit_mem _ _ _ hh)
    have he : p.1 = i := by simpa using hit_test _ _ _ hh
    have hi : i ≠ o := he ▸ hp.1
    have hc := readC X N o g p.2 hp.2
    change evalE (upd X o g) N (.ite p.2 (.const 1) (.const 0)) =
      (if i = o then g else evalE X N (.ite p.2 (.const 1) (.const 0)))
    simp only [if_neg hi, evalE, hc]

private theorem view_upd (s : SMachine) (o g : Nat) (X : Env) (N : Maps)
    (I : Env) (K : Maps) (hq : s.qflags = []) (hin : o ∉ s.f.m.inputs)
    (hf : ∀ p ∈ s.f.flags, p.1 ≠ o ∧ occC o p.2 = false) :
    sView s (upd X o g) N I K =
      (upd (sView s X N I K).1 o g, (sView s X N I K).2) := by
  simp only [sView, empty_bits s hq, inputs_upd _ o g X I hin,
    flags_upd _ _ _ o g hf]

private theorem writes_upd (ws : List (Nat × E × E)) (D : Env) (N : Maps)
    (o g : Nat)
    (hf : ∀ w ∈ ws, occE o w.2.1 = false ∧ occE o w.2.2 = false) :
    writeMaps ws (upd D o g) N = writeMaps ws D N := by
  funext mp k
  simp only [writeMaps]
  cases hh : lookup (fun w : Nat × E × E => w.1 == mp) ws with
  | none => rfl
  | some w =>
    have hw := hf w (hit_mem _ _ _ hh)
    change (if k = evalE (upd D o g) N w.2.1 then evalE (upd D o g) N w.2.2 else N mp k) =
      (if k = evalE D N w.2.1 then evalE D N w.2.2 else N mp k)
    rw [readE D N o g w.2.1 hw.1, readE D N o g w.2.2 hw.2]

private theorem every_upd (s : SMachine) (D : Env) (N : Maps) (o g : Nat)
    (hw : ∀ w ∈ s.f.m.writes, occE o w.2.1 = false ∧ occE o w.2.2 = false)
    (he : ∀ w ∈ s.every, occE o w.2.2 = false) :
    everyMaps s (upd D o g) N = everyMaps s D N := by
  funext mp k
  simp only [everyMaps]
  cases hh : lookup (fun w : Nat × Nat × E => w.1 == mp) s.every with
  | none => rw [writes_upd _ _ _ _ _ hw]
  | some w =>
    have h := he w (hit_mem _ _ _ hh)
    apply congrE
    intro i hi
    by_cases hio : i = o
    · subst i
      simp [h] at hi
    · simp [upd, hio]

theorem source_rebind (source : SMachine) (obs : Nat)
    (hq : source.qflags = []) (hfacts : source.facts = [])
    (hpfacts : source.pfacts = []) (hok : observerOK source obs = true) :
    ∀ {ρ M}, SReach source ρ M → ∀ g, SReach source (upd ρ obs g) M := by
  have parts :
      obs ∉ source.f.m.inputs ∧
      occC obs source.f.m.pre = false ∧
      occC obs source.f.m.assume = false ∧
      assignsOK obs source.f.m.init = true ∧
      assignsOK obs source.f.m.step = true ∧
      (∀ p ∈ source.f.flags, p.1 ≠ obs ∧ occC obs p.2 = false) ∧
      (∀ w ∈ source.f.m.writes,
        occE obs w.2.1 = false ∧ occE obs w.2.2 = false) ∧
      (∀ w ∈ source.every, occE obs w.2.2 = false) := by
    simpa [observerOK, List.contains_iff_mem, and_assoc] using hok
  obtain ⟨hin, hpre, hassume, hinit, hstep, hflags, hw, he⟩ := parts
  intro ρ M hr
  induction hr with
  | start X N hM hc _ _ =>
    intro g
    rw [← assigns_upd _ X N obs g hinit]
    apply SReach.start (upd X obs g) N hM
    · rwa [readC _ _ _ _ _ hpre]
    · simp [hfacts]
    · simp [SMachine.PFacts, hpfacts]
  | step X N I K _ hc ih =>
    intro g
    have hv := view_upd source obs g X N I K hq hin hflags
    have hc' : evalC (sView source (upd X obs g) N I K).1
        (sView source (upd X obs g) N I K).2 source.f.m.assume = true := by
      simpa only [hv, readC _ _ obs g _ hassume] using hc
    have hr' := SReach.step (s := source) (upd X obs g) N I K (ih g) hc'
    simpa only [sNext, hv, assigns_upd _ _ _ obs g hstep,
      every_upd source _ _ obs g hw he] using hr'

end Kern.GhostSourceViews

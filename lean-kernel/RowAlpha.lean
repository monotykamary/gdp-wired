import QAlpha

namespace Kern.RowAlpha
open Classical

structure Rename where
  mp : Nat
  old : Nat
  fresh : Nat
  deriving DecidableEq, Repr

def renameRow (w : Nat × Nat × E) (r : Rename) : Nat × Nat × E :=
  if w.1 = r.mp then (w.1, r.fresh, substE [(r.old, .var r.fresh)] w.2.2) else w

def validRow (w : Nat × Nat × E) (r : Rename) : Bool :=
  if w.1 = r.mp then (w.2.1 == r.old) && !occE r.fresh w.2.2 else true

def rename (s : SMachine) (r : Rename) : SMachine :=
  { s with every := s.every.map (fun w => renameRow w r) }

def valid (s : SMachine) (r : Rename) : Bool := s.every.all (fun w => validRow w r)

def renameAll : SMachine → List Rename → SMachine
  | s, [] => s
  | s, r :: rs => renameAll (rename s r) rs

def validAll : SMachine → List Rename → Bool
  | _, [] => true
  | s, r :: rs => valid s r && validAll (rename s r) rs

@[simp] theorem renameRow_mp (w : Nat × Nat × E) (r : Rename) : (renameRow w r).1 = w.1 := by
  unfold renameRow; split <;> rfl

theorem eval_row (e : E) (a b : Nat) (h : occE b e = false)
    (D : Nat → Nat) (N : Nat → Nat → Nat) (key : Nat) :
    evalE (upd D b key) N (substE [(a, .var b)] e) = evalE (upd D a key) N e := by
  rw [subst_evalE, applyS_single]
  apply congrE
  intro i hi
  have hib : i ≠ b := by intro he; subst i; simp [h] at hi
  by_cases hia : i = a
  · subst i; simp [upd, evalE]
  · simp [upd, evalE, hia, hib]

theorem row_value (w : Nat × Nat × E) (r : Rename) (h : validRow w r = true)
    (D : Nat → Nat) (N : Nat → Nat → Nat) (key : Nat) :
    evalE (upd D (renameRow w r).2.1 key) N (renameRow w r).2.2 =
      evalE (upd D w.2.1 key) N w.2.2 := by
  by_cases he : w.1 = r.mp
  · have hp : w.2.1 = r.old ∧ occE r.fresh w.2.2 = false := by
      simpa [validRow, he, Bool.and_eq_true] using h
    simpa [renameRow, he, hp.1] using eval_row w.2.2 r.old r.fresh hp.2 D N key
  · simp [renameRow, he]

theorem lookup_value (ws : List (Nat × Nat × E)) (r : Rename)
    (h : ws.all (fun w => validRow w r) = true) (D : Nat → Nat)
    (N : Nat → Nat → Nat) (mp key : Nat) (fallback : Nat) :
    (match lookup (fun w => w.1 == mp) (ws.map (fun w => renameRow w r)) with
     | some w => evalE (upd D w.2.1 key) N w.2.2
     | none => fallback) =
    (match lookup (fun w => w.1 == mp) ws with
     | some w => evalE (upd D w.2.1 key) N w.2.2
     | none => fallback) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hp : validRow w r = true ∧ ws.all (fun w => validRow w r) = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using h
    by_cases hi : (w.1 == mp) = true
    · simpa only [List.map_cons, lookup, renameRow_mp, hi, ite_true] using row_value w r hp.1 D N key
    · simpa [List.map_cons, lookup, hi] using ih hp.2

theorem everyMaps_rename (s : SMachine) (r : Rename) (h : valid s r = true) :
    everyMaps (rename s r) = everyMaps s := by
  funext D N mp key
  exact lookup_value s.every r h D N mp key (writeMaps s.f.m.writes D N mp key)

structure Equiv (s t : SMachine) : Prop where
  f : s.f = t.f
  carried : s.carried = t.carried
  every : everyMaps s = everyMaps t
  facts : s.facts = t.facts
  pfacts : s.pfacts = t.pfacts
  flags : ∀ X N, decideQ s X N = decideQ t X N

theorem Equiv.refl (s : SMachine) : Equiv s s := ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
theorem Equiv.trans {s t u : SMachine} (h : Equiv s t) (g : Equiv t u) : Equiv s u :=
  ⟨h.f.trans g.f, h.carried.trans g.carried, h.every.trans g.every,
   h.facts.trans g.facts, h.pfacts.trans g.pfacts, fun X N => (h.flags X N).trans (g.flags X N)⟩
theorem Equiv.symm {s t : SMachine} (h : Equiv s t) : Equiv t s :=
  ⟨h.f.symm, h.carried.symm, h.every.symm, h.facts.symm, h.pfacts.symm, fun X N => (h.flags X N).symm⟩

theorem rename_equiv (s : SMachine) (r : Rename) (h : valid s r = true) : Equiv (rename s r) s :=
  ⟨rfl, rfl, everyMaps_rename s r h, rfl, rfl, fun _ _ => rfl⟩

theorem renameAll_equiv (s : SMachine) (rs : List Rename) (h : validAll s rs = true) :
    Equiv (renameAll s rs) s := by
  induction rs generalizing s with
  | nil => exact Equiv.refl s
  | cons r rs ih =>
    have hp : valid s r = true ∧ validAll (rename s r) rs = true := by
      simpa only [validAll, Bool.and_eq_true] using h
    exact (ih (rename s r) hp.2).trans (rename_equiv s r hp.1)

theorem Equiv.withCarried {s t : SMachine} (h : Equiv s t) (M κ : Nat → Nat → Nat) :
    Kern.withCarried s M κ = Kern.withCarried t M κ := by
  funext mp key
  change (if s.carried.contains mp then κ mp else M mp) key =
    (if t.carried.contains mp then κ mp else M mp) key
  rw [h.carried]

theorem Equiv.view {s t : SMachine} (h : Equiv s t) (ρ ι : Nat → Nat) (M κ : Nat → Nat → Nat) :
    sView s ρ M ι κ = sView t ρ M ι κ := by
  simp only [sView, h.f, h.withCarried, h.flags]

theorem Equiv.next {s t : SMachine} (h : Equiv s t) (ρ ι : Nat → Nat) (M κ : Nat → Nat → Nat) :
    sNext s ρ M ι κ = sNext t ρ M ι κ := by
  simp only [sNext, h.view, h.f, h.every]

theorem Equiv.sreach_imp {s t : SMachine} (h : Equiv s t) {ρ M} (hr : SReach s ρ M) : SReach t ρ M := by
  induction hr with
  | start ρ M hm hp hf hpf =>
    have hh := SReach.start (s := t) ρ M (by simpa only [h.f] using hm)
      (by simpa only [h.f] using hp) (by simpa only [h.facts] using hf)
      (by simpa only [SMachine.PFacts, h.pfacts] using hpf)
    simpa only [h.f] using hh
  | step ρ M ι κ hr ha ih =>
    have hh := SReach.step ρ M ι κ ih (by simpa only [h.view, h.f] using ha)
    simpa only [h.next] using hh

theorem Equiv.creach_imp {s t : SMachine} (h : Equiv s t) (ds : List CDecl) {ρ M}
    (hr : CReach s ds ρ M) : CReach t ds ρ M := by
  induction hr with
  | start ρ M hm hp hf hpf =>
    have hh := CReach.start (s := t) (ds := ds) ρ M (by simpa only [h.f] using hm)
      (by simpa only [h.f] using hp) (by simpa only [h.facts] using hf)
      (by simpa only [SMachine.PFacts, h.pfacts] using hpf)
    simpa only [h.f] using hh
  | step ρ M ι κ hr hg ha ih =>
    have hh := CReach.step ρ M ι κ ih (by simpa only [h.f, h.withCarried] using hg)
      (by simpa only [h.view, h.f] using ha)
    simpa only [h.next] using hh

theorem Equiv.sreach {s t : SMachine} (h : Equiv s t) (ρ M) : SReach s ρ M ↔ SReach t ρ M :=
  ⟨h.sreach_imp, h.symm.sreach_imp⟩
theorem Equiv.creach {s t : SMachine} (h : Equiv s t) (ds : List CDecl) (ρ M) : CReach s ds ρ M ↔ CReach t ds ρ M :=
  ⟨h.creach_imp ds, h.symm.creach_imp ds⟩

end Kern.RowAlpha

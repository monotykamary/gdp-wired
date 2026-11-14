import CountMachine

/-! A semantic bridge for capture-avoiding alpha conversion of quantified flags.
Only qflags change; no checker or proof rule is modified. -/
namespace Kern.QAlpha
open Classical

structure Rename where
  flag : Nat
  old : Nat
  fresh : Nat
  deriving DecidableEq, Repr

def keys (ks : List Nat) (a b : Nat) : List Nat :=
  ks.map (fun i => if i = a then b else i)

def body (c : C) (a b : Nat) : C := substC [(a, .var b)] c

def validQ (q : Nat × List Nat × C) (r : Rename) : Bool :=
  if q.1 = r.flag then q.2.1.contains r.old && !q.2.1.contains r.fresh && !occC r.fresh q.2.2 else true

def renameQ (q : Nat × List Nat × C) (r : Rename) : Nat × List Nat × C :=
  if q.1 = r.flag then (q.1, keys q.2.1 r.old r.fresh, body q.2.2 r.old r.fresh) else q

def valid (s : SMachine) (r : Rename) : Bool := s.qflags.all (fun q => validQ q r)
def rename (s : SMachine) (r : Rename) : SMachine :=
  { s with qflags := s.qflags.map (fun q => renameQ q r) }

def renameAll : SMachine → List Rename → SMachine
  | s, [] => s
  | s, r :: rs => renameAll (rename s r) rs

def validAll : SMachine → List Rename → Bool
  | _, [] => true
  | s, r :: rs => valid s r && validAll (rename s r) rs

theorem mem_keys {ks : List Nat} {a b i : Nat} (hi : i ≠ b) :
    i ∈ keys ks a b ↔ i ∈ ks ∧ i ≠ a := by
  simp only [keys, List.mem_map]
  constructor
  · rintro ⟨j, hj, he⟩
    split at he <;> grind
  · rintro ⟨h, hia⟩
    exact ⟨i, h, by simp [hia]⟩

theorem eval_body (ks : List Nat) (c : C) (a b : Nat)
    (ha : a ∈ ks) (hb : b ∉ ks) (hc : occC b c = false)
    (X u v : Nat → Nat) (N : Nat → Nat → Nat)
    (hab : u a = v b) (huv : ∀ i ∈ ks, i ≠ a → u i = v i) :
    evalC (atKeys X (keys ks a b) v) N (body c a b) = evalC (atKeys X ks u) N c := by
  have hne : a ≠ b := by intro h; subst b; exact hb ha
  unfold body
  rw [subst_evalC]
  apply congrC
  intro i hi
  have hib : i ≠ b := by intro h; subst i; simp [hc] at hi
  by_cases hia : i = a
  · subst i
    have hbm : b ∈ keys ks a b := List.mem_map.mpr ⟨a, ha, by simp⟩
    simp [applyS, assoc, lookup, evalE, atKeys_in hbm, atKeys_in ha, hab]
  · have hm := mem_keys (ks := ks) (a := a) hib
    by_cases hik : i ∈ ks
    · have hmk : i ∈ keys ks a b := hm.mpr ⟨hik, hia⟩
      simp [applyS, assoc, lookup, hia, Ne.symm hia, atKeys_in hmk, atKeys_in hik, huv i hik hia]
    · have hmk : i ∉ keys ks a b := fun h => hik (hm.mp h).1
      simp [applyS, assoc, lookup, hia, Ne.symm hia, atKeys_out hmk, atKeys_out hik]

theorem quantified (ks : List Nat) (c : C) (a b : Nat)
    (ha : a ∈ ks) (hb : b ∉ ks) (hc : occC b c = false)
    (X : Nat → Nat) (N : Nat → Nat → Nat) :
    (∀ v, holdsC (atKeys X (keys ks a b) v) N (body c a b)) ↔
    (∀ u, holdsC (atKeys X ks u) N c) := by
  have hne : a ≠ b := by intro h; subst b; exact hb ha
  constructor
  · intro h u
    have hv := h (upd u b (u a))
    rw [← evalC_iff, eval_body ks c a b ha hb hc X u (upd u b (u a)) N
      (by simp [upd]) (by
        intro i hi hia
        have hib : i ≠ b := by
          intro e
          subst i
          exact hb hi
        simp [upd, hib])] at hv
    exact (evalC_iff _ _ _).mp hv
  · intro h v
    rw [← evalC_iff, eval_body ks c a b ha hb hc X (upd v a (v b)) v N
      (by simp [upd]) (by intro i hi hia; simp [upd, hia])]
    exact (evalC_iff _ _ _).mpr (h _)

@[simp] theorem renameQ_flag (q : Nat × List Nat × C) (r : Rename) : (renameQ q r).1 = q.1 := by
  unfold renameQ; split <;> rfl

theorem quantifiedQ (q : Nat × List Nat × C) (r : Rename) (h : validQ q r = true)
    (X : Nat → Nat) (N : Nat → Nat → Nat) :
    (∀ k, holdsC (atKeys X (renameQ q r).2.1 k) N (renameQ q r).2.2) ↔
    (∀ k, holdsC (atKeys X q.2.1 k) N q.2.2) := by
  by_cases he : q.1 = r.flag
  · have hp : r.old ∈ q.2.1 ∧ r.fresh ∉ q.2.1 ∧ occC r.fresh q.2.2 = false := by
      simpa [validQ, he, Bool.and_eq_true, List.contains_iff_mem, and_assoc] using h
    simpa [renameQ, he] using quantified q.2.1 q.2.2 r.old r.fresh hp.1 hp.2.1 hp.2.2 X N
  · simp [renameQ, he]

theorem lookup_value (qs : List (Nat × List Nat × C)) (r : Rename)
    (h : qs.all (fun q => validQ q r) = true) (X : Nat → Nat) (N : Nat → Nat → Nat) (i : Nat) :
    (match lookup (fun q => q.1 == i) (qs.map (fun q => renameQ q r)) with
     | some q => if ∀ k, holdsC (atKeys X q.2.1 k) N q.2.2 then 1 else 0
     | none => X i) =
    (match lookup (fun q => q.1 == i) qs with
     | some q => if ∀ k, holdsC (atKeys X q.2.1 k) N q.2.2 then 1 else 0
     | none => X i) := by
  classical
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    have hp : validQ q r = true ∧ qs.all (fun q => validQ q r) = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using h
    by_cases hi : (q.1 == i) = true
    · simp only [List.map_cons, lookup, renameQ_flag, hi, ite_true]
      rw [quantifiedQ q r hp.1 X N]
    · simpa [List.map_cons, lookup, hi] using ih hp.2

theorem decideQ_rename (s : SMachine) (r : Rename) (h : valid s r = true)
    (X : Nat → Nat) (N : Nat → Nat → Nat) : decideQ (rename s r) X N = decideQ s X N := by
  classical
  funext i
  exact lookup_value s.qflags r h X N i

/-- The complete semantic interface, independent of checker acceptance. -/
structure Equiv (s t : SMachine) : Prop where
  f : s.f = t.f
  carried : s.carried = t.carried
  every : s.every = t.every
  facts : s.facts = t.facts
  pfacts : s.pfacts = t.pfacts
  flags : ∀ X N, decideQ s X N = decideQ t X N

theorem Equiv.refl (s : SMachine) : Equiv s s := ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
theorem Equiv.trans {s t u : SMachine} (h : Equiv s t) (g : Equiv t u) : Equiv s u :=
  ⟨h.f.trans g.f, h.carried.trans g.carried, h.every.trans g.every,
   h.facts.trans g.facts, h.pfacts.trans g.pfacts, fun X N => (h.flags X N).trans (g.flags X N)⟩
theorem rename_equiv (s : SMachine) (r : Rename) (h : valid s r = true) : Equiv (rename s r) s :=
  ⟨rfl, rfl, rfl, rfl, rfl, decideQ_rename s r h⟩

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
  simp only [sNext, h.view]
  have he : Kern.everyMaps s = Kern.everyMaps t := by
    funext D N mp key
    unfold Kern.everyMaps
    rw [h.every, h.f]
  rw [h.f, he]

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

theorem Equiv.symm {s t : SMachine} (h : Equiv s t) : Equiv t s :=
  ⟨h.f.symm, h.carried.symm, h.every.symm, h.facts.symm, h.pfacts.symm, fun X N => (h.flags X N).symm⟩

theorem Equiv.sreach {s t : SMachine} (h : Equiv s t) (ρ M) : SReach s ρ M ↔ SReach t ρ M :=
  ⟨h.sreach_imp, h.symm.sreach_imp⟩

theorem Equiv.creach {s t : SMachine} (h : Equiv s t) (ds : List CDecl) (ρ M) : CReach s ds ρ M ↔ CReach t ds ρ M :=
  ⟨h.creach_imp ds, h.symm.creach_imp ds⟩

/-- Transport the existing count-machine checker soundness to the ORIGINAL machine. -/
theorem cmachine_sound (s : SMachine) (rs : List Rename) (ds : List CDecl) (ps : List CEntry)
    (hv : validAll s rs = true) (hc : checkCMachine (renameAll s rs) ds ps = true) :
    ∀ ρ M, CReach s ds ρ M → ∀ ce ∈ ps, ce.e.Holds ρ (withCnt ds ρ M) := by
  intro ρ M hr
  exact Kern.cmachine_sound (renameAll s rs) ds ps hc ρ M
    (((renameAll_equiv s rs hv).creach ds ρ M).mpr hr)

/-- Transport the existing set-machine checker soundness to the ORIGINAL machine. -/
theorem smachine_sound (s : SMachine) (rs : List Rename) (ps : List SEntry)
    (hv : validAll s rs = true) (hc : checkSMachine (renameAll s rs) ps = true) :
    ∀ ρ M, SReach s ρ M → ∀ e ∈ ps, e.Holds ρ M := by
  intro ρ M hr
  exact Kern.smachine_sound (renameAll s rs) ps hc ρ M
    (((renameAll_equiv s rs hv).sreach ρ M).mpr hr)

end Kern.QAlpha

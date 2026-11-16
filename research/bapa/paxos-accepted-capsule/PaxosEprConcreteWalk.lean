import PaxosEprTargetExecution
namespace Bapa.PaxosEprTarget
open Kern Bapa.FiniteSimulation

structure ScanStore where
  size : Nat
  none : Nat
  maps : Nat → Nat → Nat

structure During (s : ScanStore) (q : Nat → Nat) (r mr v i : Nat) (x : KState) : Prop where
  none : x.1 0 = s.none
  size : x.1 1 = s.size
  busy : x.1 8 = 1
  count : x.1 9 = i
  round : x.1 10 = r
  maxRound : x.1 11 = mr
  value : x.1 12 = v
  publicMaps : ∀ mp, mp < 6 → ∀ key, x.2 mp key = s.maps mp key
  quorum : ∀ key, x.2 6 key = q key

structure Finished (s : ScanStore) (r v : Nat) (x : KState) : Prop where
  none : x.1 0 = s.none
  size : x.1 1 = s.size
  busy : x.1 8 = 0
  count : x.1 9 = 0
  round : x.1 10 = 0
  maxRound : x.1 11 = 0
  value : x.1 12 = 0
  publicMaps : ∀ mp, mp < 6 → ∀ key, x.2 mp key =
    if mp = 3 ∧ key = cpair r v then 1 else s.maps mp key
  quorum : ∀ key, x.2 6 key = 0

def StoreBoolean (s : ScanStore) : Prop := ∀ mp, mp < 6 → ∀ key, s.maps mp key ≤ 1

def AllRows (s : ScanStore) (q : Nat → Nat) (r mr : Nat) : Prop :=
  ∀ i, i < s.size → q i = 1 → ∀ rr vv,
    s.maps 4 (cpair i (cpair rr vv)) = 1 → rr < r → mr ≠ s.none ∧ rr ≤ mr

theorem During.boolean {s q r mr v i x} (h : During s q r mr v i x)
    (hs : StoreBoolean s) (hq : ∀ k, q k ≤ 1) : BooleanSeven x.2 := by
  intro mp hm key
  by_cases he : mp = 6
  · subst mp
    rw [h.quorum]
    exact hq key
  · rw [h.publicMaps mp (by omega)]
    exact hs mp (by omega) key

theorem During.row {s q r mr v i x} (h : During s q r mr v i x)
    (rows : AllRows s q r mr) (hi : i < s.size) :
    x.2 6 (x.1 9) = 1 → ∀ rr vv, x.2 4 (cpair (x.1 9) (cpair rr vv)) = 1 →
      rr < x.1 10 → x.1 11 ≠ x.1 0 ∧ rr ≤ x.1 11 := by
  intro hq rr vv hv hl
  have hqi : q i = 1 := by simpa only [h.count, h.quorum] using hq
  have hvi : s.maps 4 (cpair i (cpair rr vv)) = 1 := by
    simpa only [h.count, h.publicMaps 4 (by decide)] using hv
  have hlt : rr < r := by simpa only [h.round] using hl
  simpa only [h.maxRound,h.none] using rows i hi hqi rr vv hvi hlt

theorem during_next {s q r mr v i x y} (hx : During s q r mr v i x)
    (hi : i+1 < s.size) (he : ScanEffect x.1 x.2 y.1 y.2) : During s q r mr v (i+1) y := by
  have hn : ¬ x.1 9 + 1 = x.1 1 := by rw [hx.count,hx.size]; omega
  obtain ⟨e0,e1,e8,e9,e10,e11,e12,em,eq⟩ := he
  refine ⟨e0.trans hx.none,e1.trans hx.size,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [if_neg hn] using e8
  · simp only [if_neg hn] at e9
    simpa only [hx.count] using e9
  · simpa only [if_neg hn,hx.round] using e10
  · simpa only [if_neg hn,hx.maxRound] using e11
  · simpa only [if_neg hn,hx.value] using e12
  · intro mp hm key
    simpa [hn,hx.publicMaps mp hm key] using em mp hm key
  · intro key
    simpa only [if_neg hn,hx.quorum key] using eq key

theorem during_finish {s q r mr v i x y} (hx : During s q r mr v i x)
    (hi : i+1 = s.size) (he : ScanEffect x.1 x.2 y.1 y.2) : Finished s r v y := by
  have hn : x.1 9 + 1 = x.1 1 := by rw [hx.count,hx.size]; exact hi
  obtain ⟨e0,e1,e8,e9,e10,e11,e12,em,eq⟩ := he
  refine ⟨e0.trans hx.none,e1.trans hx.size,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [if_pos hn] using e8
  · simpa only [if_pos hn] using e9
  · simpa only [if_pos hn] using e10
  · simpa only [if_pos hn] using e11
  · simpa only [if_pos hn] using e12
  · intro mp hm key
    simpa [hn,hx.round,hx.value,hx.publicMaps mp hm key] using em mp hm key
  · intro key
    simpa only [if_pos hn] using eq key

/-- Every node is visited by an actual counted edge. No reachability, GHolds,
or post-state correspondence is assumed at the end of the finite scan. -/
theorem finish_concrete_scan (s : ScanStore) (q : Nat → Nat) (r mr v : Nat)
    (hs : StoreBoolean s) (hq : ∀ k, q k ≤ 1) (rows : AllRows s q r mr)
    (hsize : 0 < s.size) {x : KState} (hx : During s q r mr v 0 x) :
    ∃ y, CSteps machine declarations x y ∧ Finished s r v y := by
  have walk : ∀ remaining i x, i+remaining+1 = s.size → During s q r mr v i x →
      ∃ y, CSteps machine declarations x y ∧ Finished s r v y := by
    intro remaining
    induction remaining with
    | zero =>
      intro i x hi hx
      have hpos : 0 < x.1 1 := by rw [hx.size]; exact hsize
      obtain ⟨y,edge,effect⟩ := encoded_scan_step x.1 x.2 hpos hx.busy (hx.boolean hs hq)
        (hx.row rows (by omega))
      exact ⟨y,.next (.refl _) edge,during_finish hx (by omega) effect⟩
    | succ remaining ih =>
      intro i x hi hx
      have hpos : 0 < x.1 1 := by rw [hx.size]; exact hsize
      obtain ⟨y,edge,effect⟩ := encoded_scan_step x.1 x.2 hpos hx.busy (hx.boolean hs hq)
        (hx.row rows (by omega))
      have hy := during_next hx (by omega) effect
      obtain ⟨z,path,done⟩ := ih (i+1) y (by omega) hy
      exact ⟨z,(Steps.next (.refl _) edge).trans path,done⟩
  exact walk (s.size-1) 0 x (by omega) hx

#print axioms finish_concrete_scan
end Bapa.PaxosEprTarget

import Count
import Sets

/-! Finite-prefix composition. All observations in the state-level interface
are functions of the actual store. No decidability of reachability, bound on
support size, or correctness of a proposed list of writes is assumed. -/
namespace Kern.FiniteSumComposition
set_option autoImplicit false

/-- Fold a finite list, counting each occurrence once. -/
def sumOn : List Nat → (Nat → Nat) → Nat
  | [], _ => 0
  | i :: is, f => f i + sumOn is f

theorem sumOn_congr (is : List Nat) (f g : Nat → Nat)
    (h : ∀ i ∈ is, f i = g i) : sumOn is f = sumOn is g := by
  induction is with
  | nil => rfl
  | cons a as ih =>
    change f a + sumOn as f = g a + sumOn as g
    rw [h a (by simp), ih (fun i hi => h i (by simp [hi]))]

/-- Fold any finite family of contributions before or after summing the sites. -/
theorem interchange (is : List Nat) (v : Nat → Nat → Nat) (n : Nat) :
    sumOn is (fun i => sumBelow (v i) n) =
      sumBelow (fun k => sumOn is (fun i => v i k)) n := by
  induction is with
  | nil => exact (sumBelow_zero_fn n).symm
  | cons a as ih =>
    change sumBelow (v a) n + sumOn as (fun i => sumBelow (v i) n) =
      sumBelow (fun k => v a k + sumOn as (fun i => v i k)) n
    rw [sumBelow_add, ih]

private theorem spike (n t v : Nat) (ht : t < n) :
    sumBelow (fun k => if k = t then v else 0) n = v := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : n = t
    · subst t
      have hz : sumBelow (fun k => if k = n then v else 0) n = 0 := by
        calc
          _ = sumBelow (fun _ => 0) n := sumBelow_congr n (fun k hk => by simp [Nat.ne_of_lt hk])
          _ = 0 := sumBelow_zero_fn n
      simp [sumBelow, hz]
    · have hlt : t < n := by omega
      simp [sumBelow, he, ih hlt]

private theorem pick (ts : List Nat) (f : Nat → Nat) (k : Nat) (hd : ts.Nodup) :
    sumOn ts (fun i => if k = i then f i else 0) = (if k ∈ ts then f k else 0) := by
  induction ts with
  | nil => simp [sumOn]
  | cons a as ih =>
    obtain ⟨hna, htail⟩ := List.nodup_cons.mp hd
    by_cases h : k = a
    · subst k; simp [sumOn, ih htail, hna]
    · simp [sumOn, ih htail, List.mem_cons, h]

/-- A masked prefix sum is the listed sum only with in-range, nonrepeated sites. -/
theorem masked_sum (f : Nat → Nat) (n : Nat) (ts : List Nat)
    (hd : ts.Nodup) (inside : ∀ t ∈ ts, t < n) :
    sumBelow (fun k => if k ∈ ts then f k else 0) n = sumOn ts f := by
  calc
    _ = sumBelow (fun k => sumOn ts (fun i => if k = i then f i else 0)) n :=
      sumBelow_congr n (fun k _ => (pick ts f k hd).symm)
    _ = sumOn ts (fun i => sumBelow (fun k => if k = i then f i else 0) n) :=
      (interchange ts (fun i k => if k = i then f i else 0) n).symm
    _ = sumOn ts f := sumOn_congr ts _ f (fun i hi => spike n i (f i) (inside i hi))

/-- With a frame on the complement, replacing the touched part exchanges the two totals. -/
theorem exchange (f g : Nat → Nat) (n : Nat) (ts : List Nat)
    (hd : ts.Nodup) (inside : ∀ t ∈ ts, t < n)
    (frame : ∀ k, k < n → k ∉ ts → g k = f k) :
    sumBelow g n + sumOn ts f = sumBelow f n + sumOn ts g := by
  rw [← masked_sum f n ts hd inside, ← masked_sum g n ts hd inside,
      ← sumBelow_add, ← sumBelow_add]
  apply sumBelow_congr n
  intro k hk
  by_cases h : k ∈ ts
  · simp [h, Nat.add_comm]
  · simp [h, frame k hk h]

theorem sparse_change (f g : Nat → Nat) (n before after : Nat) (ts : List Nat)
    (hd : ts.Nodup) (inside : ∀ t ∈ ts, t < n)
    (frame : ∀ k, k < n → k ∉ ts → g k = f k)
    (old : before = sumBelow f n)
    (balance : after + sumOn ts f = before + sumOn ts g) : after = sumBelow g n := by
  have e := exchange f g n ts hd inside frame
  omega

/-- A broadcast need not frame any old cell. Its checked scalar is the fold of
its specified new row, not an unchecked assertion that the old sum was zero. -/
theorem rebuild (g row : Nat → Nat) (n after : Nat)
    (scalar : after = sumBelow row n) (cells : ∀ k, k < n → g k = row k) :
    after = sumBelow g n := scalar.trans (sumBelow_congr n cells).symm

abbrev FoldState := (Nat → Nat) × (Nat → Nat → Nat)

structure Layout where
  fields : List Nat
  size : FoldState → Nat
  cell : Nat → FoldState → Nat → Nat

def Coupled (d : Layout) (x : FoldState) : Prop :=
  ∀ i ∈ d.fields, x.1 i = sumBelow (d.cell i x) (d.size x)

/-- All-support reconstruction, usable both at start and on the broadcast path. -/
def Rebuilt (d : Layout) (y : FoldState) (n : Nat) : Prop :=
  ∃ row : Nat → Nat → Nat, ∀ i ∈ d.fields,
    y.1 i = sumBelow (row i) n ∧ ∀ k, k < n → d.cell i y k = row i k

/-- Shared touched sites; separate frame and balance for every tracked scalar. -/
def Sparse (d : Layout) (x y : FoldState) : Prop :=
  ∃ ts : List Nat, ts.Nodup ∧ (∀ t ∈ ts, t < d.size x) ∧ ∀ i ∈ d.fields,
    (∀ k, k < d.size x → k ∉ ts → d.cell i y k = d.cell i x k) ∧
    y.1 i + sumOn ts (d.cell i x) = x.1 i + sumOn ts (d.cell i y)

def StepOK (d : Layout) (x y : FoldState) : Prop :=
  d.size y = d.size x ∧ (Sparse d x y ∨ Rebuilt d y (d.size x))

theorem rebuilt_coupled (d : Layout) (x : FoldState) (h : Rebuilt d x (d.size x)) :
    Coupled d x := by
  obtain ⟨row, hr⟩ := h
  intro i hi
  exact rebuild _ (row i) _ _ (hr i hi).1 (hr i hi).2

theorem step_coupled (d : Layout) (x y : FoldState) (h : Coupled d x) (ok : StepOK d x y) :
    Coupled d y := by
  obtain ⟨hn, hs | hr⟩ := ok
  · obtain ⟨ts, hd, inside, hall⟩ := hs
    intro i hi
    rw [hn]
    exact sparse_change _ _ _ _ _ ts hd inside (hall i hi).1 (h i hi) (hall i hi).2
  · exact rebuilt_coupled d y (hn.symm ▸ hr)

/-- Capacity is a checked inequality at an arbitrary site, not an assertion
about the sum in a reachable state. Unit capacity specializes the RHS to size. -/
theorem combined_capacity (d : Layout) (x : FoldState) (cap : Nat → Nat)
    (h : Coupled d x)
    (pointwise : ∀ k, k < d.size x → sumOn d.fields (fun i => d.cell i x k) ≤ cap k) :
    sumOn d.fields x.1 ≤ sumBelow cap (d.size x) := by
  calc
    sumOn d.fields x.1 = sumOn d.fields (fun i => sumBelow (d.cell i x) (d.size x)) :=
      sumOn_congr _ _ _ h
    _ = sumBelow (fun k => sumOn d.fields (fun i => d.cell i x k)) (d.size x) :=
      interchange d.fields (fun i => d.cell i x) (d.size x)
    _ ≤ _ := sumBelow_mono _ pointwise

/-- Machine binding. The base needs only the actual map initialization. The
step producer sees admission but cannot assume reachability or the invariant. -/
theorem reach_coupled (s : SMachine) (d : Layout)
    (base : ∀ ρ M, StartMaps s.f.m M → Coupled d (applyS s.f.m.init ρ M, M))
    (step : ∀ ρ M ι κ, evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume = true →
      StepOK d (ρ, M) (sNext s ρ M ι κ))
    {ρ : Nat → Nat} {M : Nat → Nat → Nat} (h : SReach s ρ M) : Coupled d (ρ, M) := by
  induction h with
  | start ρ M hm _ _ _ => exact base ρ M hm
  | step ρ M ι κ _ adm ih => exact step_coupled d _ _ ih (step ρ M ι κ adm)

/-- The final sequent has the caller's original C as conclusion. In particular
this does not silently replace that law by the intermediate capacity bound. -/
theorem state_law (s : SMachine) (d : Layout) (original : C) (cap : FoldState → Nat → Nat)
    (base : ∀ ρ M, StartMaps s.f.m M → Coupled d (applyS s.f.m.init ρ M, M))
    (step : ∀ ρ M ι κ, evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume = true →
      StepOK d (ρ, M) (sNext s ρ M ι κ))
    (pointwise : ∀ x k, k < d.size x → sumOn d.fields (fun i => d.cell i x k) ≤ cap x k)
    (claim : ∀ x : FoldState, sumOn d.fields x.1 ≤ sumBelow (cap x) (d.size x) →
      holdsC x.1 x.2 original)
    {ρ : Nat → Nat} {M : Nat → Nat → Nat} (h : SReach s ρ M) : holdsC ρ M original := by
  exact claim (ρ, M) (combined_capacity d (ρ, M) _ (reach_coupled s d base step h) (pointwise (ρ, M)))

#print axioms interchange
#print axioms exchange
#print axioms sparse_change
#print axioms rebuild
#print axioms combined_capacity
#print axioms reach_coupled
#print axioms state_law
end Kern.FiniteSumComposition

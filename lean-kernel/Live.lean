import Sets

/-!
Liveness under fairness: "from leads to to", proven sound for machines with sets (`sleads_sound`, and under weak
fairness `sleads_wf_sound`); a machine with maps and flags is one with no sets. kernel.ts proves it by a rank (naturals over the state and params, compared in
order: the first that differs decides) and helpful requests, each with the region where it helps. While `from` holds and
`to` doesn't: every request allowed keeps `from` or reaches `to`, and reaches `to`, lowers the rank, or keeps the rank
with every region it was in kept (a step law); some region holds (a step law that reads no step); and each helpful
request, taken in its region, reaches `to` or lowers the rank (a step law whose `when` names the inputs the request
sets; the others, and the maps it carries, stay free: a history's queries among them). Lean builds all of them from the
liveness and checks them with the step-law rules (StepLaw.lean's, Sets.lean's). Then along every run that takes each
helpful request infinitely often, each state where `from` holds is followed by one where `to` holds: the rank can't drop
forever, once it stops dropping the region it is in stays, and that region's request comes and lowers it.
-/

namespace Kern

/-! Ranks compared in order -/

def lexB : List Nat → List Nat → Bool
  | a' :: as', a :: as => decide (a' < a) || (decide (a' = a) && lexB as' as)
  | _, _ => false

theorem lexB_irrefl : ∀ x : List Nat, lexB x x = false
  | [] => rfl
  | a :: as => by simp [lexB, lexB_irrefl as]

theorem nat_down {g : Nat → Nat} {n0 : Nat} (h : ∀ n, n0 ≤ n → g (n + 1) ≤ g n) : ∀ d, g (n0 + d) ≤ g n0
  | 0 => Nat.le_refl _
  | d + 1 => Nat.le_trans (h (n0 + d) (Nat.le_add_right _ _)) (nat_down h d)

-- A natural that never rises from n0 on stops changing.
theorem nat_stable (g : Nat → Nat) : ∀ v n0, g n0 ≤ v → (∀ n, n0 ≤ n → g (n + 1) ≤ g n) →
    ∃ T, n0 ≤ T ∧ ∀ m, T ≤ m → g m = g T := by
  intro v
  induction v with
  | zero =>
    intro n0 hv h
    refine ⟨n0, Nat.le_refl _, fun m hm => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    have := nat_down h d; omega
  | succ v ih =>
    intro n0 hv h
    by_cases hall : ∀ m, n0 ≤ m → g m = g n0
    · exact ⟨n0, Nat.le_refl _, hall⟩
    · have hex : ∃ m, n0 ≤ m ∧ g m ≠ g n0 := Classical.byContradiction fun hno =>
        hall fun m hm => Classical.byContradiction fun hne => hno ⟨m, hm, hne⟩
      obtain ⟨m, hm, hne⟩ := hex
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
      have := nat_down h d
      obtain ⟨T, hT, hTm⟩ := ih (n0 + d) (by omega) (fun n hn => h n (by omega))
      exact ⟨T, by omega, hTm⟩

-- A rank of k naturals that never rises (in order) from n0 on stops changing.
theorem lex_stable : ∀ (k : Nat) (r : Nat → List Nat) (n0 : Nat), (∀ n, (r n).length = k) →
    (∀ n, n0 ≤ n → lexB (r (n + 1)) (r n) = true ∨ r (n + 1) = r n) → ∃ T, n0 ≤ T ∧ ∀ m, T ≤ m → r m = r T
  | 0, r, n0, hk, _ => ⟨n0, Nat.le_refl _, fun m _ => by
      rw [List.eq_nil_of_length_eq_zero (hk m), List.eq_nil_of_length_eq_zero (hk n0)]⟩
  | k + 1, r, n0, hk, hmono => by
    have hcons : ∀ n, r n = (r n).headD 0 :: (r n).tail := by
      intro n
      have := hk n
      cases h : r n with
      | nil => rw [h] at this; simp at this
      | cons a as => rfl
    have hstep : ∀ n, n0 ≤ n → (r (n + 1)).headD 0 < (r n).headD 0 ∨
        ((r (n + 1)).headD 0 = (r n).headD 0 ∧ (lexB (r (n + 1)).tail (r n).tail = true ∨ (r (n + 1)).tail = (r n).tail)) := by
      intro n hn
      have h := hmono n hn
      rw [hcons (n + 1), hcons n] at h
      simp only [lexB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.cons.injEq] at h
      rcases h with (h | ⟨h1, h2⟩) | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, Or.inl h2⟩
      · exact Or.inr ⟨h1, Or.inr h2⟩
    obtain ⟨T1, hT1, hT1m⟩ := nat_stable (fun n => (r n).headD 0) _ n0 (Nat.le_refl _) (fun n hn => by
      rcases hstep n hn with h | ⟨h, _⟩
      · exact Nat.le_of_lt h
      · exact Nat.le_of_eq h)
    obtain ⟨T2, hT2, hT2m⟩ := lex_stable k (fun n => (r n).tail) T1 (fun n => by simp [hk n]) (fun n hn => by
      rcases hstep n (by omega) with h | ⟨_, h⟩
      · have e1 := hT1m (n + 1) (by omega); have e2 := hT1m n hn; omega
      · exact h)
    refine ⟨T2, by omega, fun m hm => ?_⟩
    have e1 := hT1m m (by omega); have e2 := hT1m T2 hT2; have e3 := hT2m m hm
    rw [hcons m, hcons T2, e3, e1, e2]

/-- Along a run: if `P ∧ ¬Q` is kept (or Q reached) with the rank never rising, and kept only with every region kept;
some region holds while `P ∧ ¬Q` does; and each region's helpful step reaches Q or lowers the rank there; then Q
follows every P, provided each helpful step is taken from any point on where it stays enabled (E), and it is enabled in
its region while `P ∧ ¬Q` holds. With E always true, that is: each helpful step taken infinitely often. -/
theorem leads_of_lex {α : Type} (P Q : Nat → Prop) (r : Nat → List Nat) (k : Nat) (hk : ∀ n, (r n).length = k)
    (helps : List α) (W H E : α → Nat → Prop)
    (hstay : ∀ n, P n → ¬ Q n → (P (n + 1) ∨ Q (n + 1)) ∧
      (Q (n + 1) ∨ lexB (r (n + 1)) (r n) = true ∨ (r (n + 1) = r n ∧ ∀ h ∈ helps, W h n → W h (n + 1))))
    (hcover : ∀ n, P n → ¬ Q n → ∃ h ∈ helps, W h n)
    (hhelp : ∀ h ∈ helps, ∀ n, P n → ¬ Q n → W h n → H h n → Q (n + 1) ∨ lexB (r (n + 1)) (r n) = true)
    (henabled : ∀ h ∈ helps, ∀ n, P n → ¬ Q n → W h n → E h n)
    (fair : ∀ h ∈ helps, ∀ n, (∀ m, n ≤ m → E h m) → ∃ m, n ≤ m ∧ H h m) : ∀ n, P n → ∃ m, n ≤ m ∧ Q m := by
  intro n0 hP
  apply Classical.byContradiction
  intro hno
  have hnq : ∀ m, n0 ≤ m → ¬ Q m := fun m hm hq => hno ⟨m, hm, hq⟩
  have hPd : ∀ d, P (n0 + d) := by
    intro d
    induction d with
    | zero => exact hP
    | succ d ih =>
      rcases (hstay (n0 + d) ih (hnq _ (Nat.le_add_right _ _))).1 with h | h
      · exact h
      · exact absurd h (hnq _ (by omega))
  have hPm : ∀ m, n0 ≤ m → P m := fun m hm => by obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm; exact hPd d
  have hmono : ∀ n, n0 ≤ n → lexB (r (n + 1)) (r n) = true ∨ r (n + 1) = r n := by
    intro n hn
    rcases (hstay n (hPm n hn) (hnq n hn)).2 with h | h | ⟨h, _⟩
    · exact absurd h (hnq _ (by omega))
    · exact Or.inl h
    · exact Or.inr h
  -- The rank stops changing at T; the region T is in stays, and its helpful step would lower the rank.
  obtain ⟨T, hT, hTm⟩ := lex_stable k r n0 hk hmono
  have hlow : ∀ m, T ≤ m → lexB (r (m + 1)) (r m) ≠ true := fun m hm hl => by
    rw [hTm (m + 1) (by omega), hTm m hm, lexB_irrefl] at hl; exact absurd hl (by simp)
  obtain ⟨h, hh, hW⟩ := hcover T (hPm T hT) (hnq T hT)
  have hWd : ∀ d, W h (T + d) := by
    intro d
    induction d with
    | zero => exact hW
    | succ d ih =>
      rcases (hstay (T + d) (hPm _ (by omega)) (hnq _ (by omega))).2 with hq | hl | ⟨_, hkeep⟩
      · exact absurd hq (hnq _ (by omega))
      · exact absurd hl (hlow _ (by omega))
      · exact hkeep h hh ih
  obtain ⟨m, hm, hH⟩ := fair h hh T (fun m hm => by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact henabled h hh (T + d) (hPm _ (by omega)) (hnq _ (by omega)) (hWd d))
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rcases hhelp h hh (T + d) (hPm _ (by omega)) (hnq _ (by omega)) (hWd d) hH with hq | hl
  · exact hnq _ (by omega) hq
  · exact hlow _ (by omega) hl

/-! Primed names: a condition read after a step -/

-- A term with its state variables renamed to their primed names (`pr`: variable, name) and its maps to theirs (`pm`).
mutual
def primeE (pr pm : List (Nat × Nat)) : E → E
  | .var i => match lookup (fun q => q.1 == i) pr with
    | some q => .var q.2
    | none => .var i
  | .const n => .const n
  | .add a b => .add (primeE pr pm a) (primeE pr pm b)
  | .sub a b => .sub (primeE pr pm a) (primeE pr pm b)
  | .mul k a => .mul k (primeE pr pm a)
  | .min a b => .min (primeE pr pm a) (primeE pr pm b)
  | .max a b => .max (primeE pr pm a) (primeE pr pm b)
  | .prod a b => .prod (primeE pr pm a) (primeE pr pm b)
  | .ite c t f => .ite (primeC pr pm c) (primeE pr pm t) (primeE pr pm f)
  | .get m k => .get (match lookup (fun q => q.1 == m) pm with
      | some q => q.2
      | none => m) (primeE pr pm k)
def primeC (pr pm : List (Nat × Nat)) : C → C
  | .le a b => .le (primeE pr pm a) (primeE pr pm b)
  | .lt a b => .lt (primeE pr pm a) (primeE pr pm b)
  | .eq a b => .eq (primeE pr pm a) (primeE pr pm b)
  | .and a b => .and (primeC pr pm a) (primeC pr pm b)
  | .or a b => .or (primeC pr pm a) (primeC pr pm b)
  | .not a => .not (primeC pr pm a)
end

-- Read where `then` reads (primed names after, the rest before), a renamed term is the term after, wherever a variable
-- or map it reads is renamed or the same before and after, and reads no primed name.
section prime
variable (pr pm : List (Nat × Nat)) (hpr : distinct (pr.map (·.2)) = true) (hpm : distinct (pm.map (·.2)) = true)
  (ρ ρ' : Nat → Nat) (M M' : Nat → Nat → Nat)
include hpr hpm
mutual
theorem primeE_eval : (e : E) → (∀ i, occE i e = true → i ∉ pr.map (·.2) ∧ (i ∈ pr.map (·.1) ∨ ρ' i = ρ i)) →
    (∀ mp, occME mp e = true → mp ∉ pm.map (·.2) ∧ (mp ∈ pm.map (·.1) ∨ M' mp = M mp)) →
    evalE (primed pr ρ' ρ) (primedMaps pm M' M) (primeE pr pm e) = evalE ρ' M' e
  | .var i, hv, _ => by
    simp only [primeE]
    cases hl : lookup (fun q => q.1 == i) pr with
    | some q =>
      have ⟨hq, hqi⟩ := lookup_some hl
      simp only [beq_iff_eq] at hqi
      simp only [evalE, primed, lookup_ren hpr q hq, hqi]
    | none =>
      have hi := hv i (by simp [occE])
      have hnot : i ∉ pr.map (·.1) := fun hm => by
        obtain ⟨q, hq, hqi⟩ := List.mem_map.mp hm
        have := lookup_none_all hl q hq; simp [hqi] at this
      have hn2 : lookup (fun q => q.2 == i) pr = none := lookup_none (fun q hq => by
        simp only [beq_eq_false_iff_ne]; intro he; exact hi.1 (by rw [← he]; exact List.mem_map_of_mem hq))
      simp only [evalE, primed, hn2]
      rcases hi.2 with h | h
      · exact absurd h hnot
      · exact h.symm
  | .const n, _, _ => rfl
  | .add a b, hv, hm => by
    simp only [primeE, evalE, primeE_eval a (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h])),
      primeE_eval b (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h]))]
  | .sub a b, hv, hm => by
    simp only [primeE, evalE, primeE_eval a (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h])),
      primeE_eval b (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h]))]
  | .mul k a, hv, hm => by
    simp only [primeE, evalE, primeE_eval a (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h]))]
  | .min a b, hv, hm => by
    simp only [primeE, evalE, primeE_eval a (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h])),
      primeE_eval b (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h]))]
  | .max a b, hv, hm => by
    simp only [primeE, evalE, primeE_eval a (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h])),
      primeE_eval b (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h]))]
  | .prod a b, hv, hm => by
    simp only [primeE, evalE, primeE_eval a (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h])),
      primeE_eval b (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h]))]
  | .ite c t f, hv, hm => by
    simp only [primeE, evalE, primeC_eval c (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h])),
      primeE_eval t (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h])),
      primeE_eval f (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h]))]
  | .get m k, hv, hm => by
    have hk := primeE_eval k (fun i hi => hv i (by simp [occE, hi])) (fun mp h => hm mp (by simp [occME, h]))
    simp only [primeE, evalE, hk]
    cases hl : lookup (fun q => q.1 == m) pm with
    | some q =>
      have ⟨hq, hqm⟩ := lookup_some hl
      simp only [beq_iff_eq] at hqm
      simp only [primedMaps, lookup_ren hpm q hq, hqm]
    | none =>
      have hmm := hm m (by simp [occME])
      have hnot : m ∉ pm.map (·.1) := fun hmem => by
        obtain ⟨q, hq, hqm⟩ := List.mem_map.mp hmem
        have := lookup_none_all hl q hq; simp [hqm] at this
      have hn2 : lookup (fun q => q.2 == m) pm = none := lookup_none (fun q hq => by
        simp only [beq_eq_false_iff_ne]; intro he; exact hmm.1 (by rw [← he]; exact List.mem_map_of_mem hq))
      simp only [primedMaps, hn2]
      rcases hmm.2 with h | h
      · exact absurd h hnot
      · rw [h]
theorem primeC_eval : (c : C) → (∀ i, occC i c = true → i ∉ pr.map (·.2) ∧ (i ∈ pr.map (·.1) ∨ ρ' i = ρ i)) →
    (∀ mp, occMC mp c = true → mp ∉ pm.map (·.2) ∧ (mp ∈ pm.map (·.1) ∨ M' mp = M mp)) →
    evalC (primed pr ρ' ρ) (primedMaps pm M' M) (primeC pr pm c) = evalC ρ' M' c
  | .le a b, hv, hm => by
    simp only [primeC, evalC, primeE_eval a (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h])),
      primeE_eval b (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h]))]
  | .lt a b, hv, hm => by
    simp only [primeC, evalC, primeE_eval a (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h])),
      primeE_eval b (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h]))]
  | .eq a b, hv, hm => by
    simp only [primeC, evalC, primeE_eval a (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h])),
      primeE_eval b (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h]))]
  | .and a b, hv, hm => by
    simp only [primeC, evalC, primeC_eval a (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h])),
      primeC_eval b (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h]))]
  | .or a b, hv, hm => by
    simp only [primeC, evalC, primeC_eval a (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h])),
      primeC_eval b (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h]))]
  | .not a, hv, hm => by
    simp only [primeC, evalC, primeC_eval a (fun i hi => hv i (by simp [occC, hi])) (fun mp h => hm mp (by simp [occMC, h]))]
end
end prime

-- Read where `then` reads, a condition that reads no primed name is the condition before the step.
theorem unprimedC_eval {pr pm : List (Nat × Nat)} {c : C} (hv : ∀ i, occC i c = true → i ∉ pr.map (·.2)) (hm : ∀ mp, occMC mp c = true → mp ∉ pm.map (·.2))
    (ρ ρ' : Nat → Nat) (M M' : Nat → Nat → Nat) : evalC (primed pr ρ' ρ) (primedMaps pm M' M) c = evalC ρ M c := by
  rw [congrC _ ρ _ c (fun i hi => by
    simp only [primed]
    rw [lookup_none (fun q hq => by simp only [beq_eq_false_iff_ne]; intro he; exact hv i hi (by rw [← he]; exact List.mem_map_of_mem hq))])]
  exact congrMC ρ _ M c (fun mp hmp => by
    funext k; simp only [primedMaps]
    rw [lookup_none (fun q hq => by simp only [beq_eq_false_iff_ne]; intro he; exact hm mp hmp (by rw [← he]; exact List.mem_map_of_mem hq))])

theorem unprimed_eval {pr pm : List (Nat × Nat)} {e : E} (hv : ∀ i, occE i e = true → i ∉ pr.map (·.2)) (hm : ∀ mp, occME mp e = true → mp ∉ pm.map (·.2))
    (ρ ρ' : Nat → Nat) (M M' : Nat → Nat → Nat) : evalE (primed pr ρ' ρ) (primedMaps pm M' M) e = evalE ρ M e := by
  rw [congrE _ ρ _ e (fun i hi => by
    simp only [primed]
    rw [lookup_none (fun q hq => by simp only [beq_eq_false_iff_ne]; intro he; exact hv i hi (by rw [← he]; exact List.mem_map_of_mem hq))])]
  exact congrME ρ _ M e (fun mp hmp => by
    funext k; simp only [primedMaps]
    rw [lookup_none (fun q hq => by simp only [beq_eq_false_iff_ne]; intro he; exact hm mp hmp (by rw [← he]; exact List.mem_map_of_mem hq))])

-- A condition (a term) read across a step: primed, it is read after the step; plain, before it, whether in `then`'s
-- reading or in `when`'s; given that what it reads is renamed or unchanged by the step, and unchanged by the request.
theorem view_C {pr pm : List (Nat × Nat)} (hpr : distinct (pr.map (·.2)) = true) (hpm : distinct (pm.map (·.2)) = true)
    {c : C} {ρ X ρ' : Nat → Nat} {M N M' : Nat → Nat → Nat}
    (hv : ∀ i, occC i c = true → i ∉ pr.map (·.2) ∧ (i ∈ pr.map (·.1) ∨ ρ' i = X i))
    (hm : ∀ mp, occMC mp c = true → mp ∉ pm.map (·.2) ∧ (mp ∈ pm.map (·.1) ∨ M' mp = N mp))
    (hx : ∀ i, occC i c = true → X i = ρ i) (hn : ∀ mp, occMC mp c = true → N mp = M mp) :
    evalC (primed pr ρ' X) (primedMaps pm M' N) (primeC pr pm c) = evalC ρ' M' c
      ∧ evalC (primed pr ρ' X) (primedMaps pm M' N) c = evalC ρ M c ∧ evalC X N c = evalC ρ M c := by
  have h3 : evalC X N c = evalC ρ M c := by rw [congrMC X N M c hn]; exact congrC X ρ M c hx
  refine ⟨primeC_eval pr pm hpr hpm X ρ' N M' c hv hm, ?_, h3⟩
  rw [unprimedC_eval (fun i hi => (hv i hi).1) (fun mp h => (hm mp h).1), h3]

theorem view_E {pr pm : List (Nat × Nat)} (hpr : distinct (pr.map (·.2)) = true) (hpm : distinct (pm.map (·.2)) = true)
    {e : E} {ρ X ρ' : Nat → Nat} {M N M' : Nat → Nat → Nat}
    (hv : ∀ i, occC i (.eq e e) = true → i ∉ pr.map (·.2) ∧ (i ∈ pr.map (·.1) ∨ ρ' i = X i))
    (hm : ∀ mp, occMC mp (.eq e e) = true → mp ∉ pm.map (·.2) ∧ (mp ∈ pm.map (·.1) ∨ M' mp = N mp))
    (hx : ∀ i, occC i (.eq e e) = true → X i = ρ i) (hn : ∀ mp, occMC mp (.eq e e) = true → N mp = M mp) :
    evalE (primed pr ρ' X) (primedMaps pm M' N) (primeE pr pm e) = evalE ρ' M' e
      ∧ evalE (primed pr ρ' X) (primedMaps pm M' N) e = evalE ρ M e := by
  have h3 : evalE X N e = evalE ρ M e := by
    rw [congrME X N M e (fun mp h => hn mp (by simp [occMC, h]))]; exact congrE X ρ M e (fun i h => hx i (by simp [occC, h]))
  refine ⟨primeE_eval pr pm hpr hpm X ρ' N M' e (fun i h => hv i (by simp [occC, h])) (fun mp h => hm mp (by simp [occMC, h])), ?_⟩
  rw [unprimed_eval (fun i h => (hv i (by simp [occC, h])).1) (fun mp h => (hm mp (by simp [occMC, h])).1), h3]

/-! The conditions Lean builds -/

def falseC : C := .lt (.const 0) (.const 0)
-- The rank after (as') below the rank before (as), in order; the two equal; each region, if it held, held after; some
-- region; the request's inputs as its terms.
def lexLtC : List E → List E → C
  | a' :: as', a :: as => .or (.lt a' a) (.and (.eq a' a) (lexLtC as' as))
  | _, _ => falseC
def eqsC : List E → List E → C
  | a' :: as', a :: as => .and (.eq a' a) (eqsC as' as)
  | _, _ => trueC
def keepC (pr pm : List (Nat × Nat)) : List C → C
  | [] => trueC
  | w :: ws => .and (.or (.not w) (primeC pr pm w)) (keepC pr pm ws)
def anyC : List C → C
  | [] => falseC
  | w :: ws => .or w (anyC ws)
def reqC : List (Nat × E) → C
  | [] => trueC
  | p :: ps => .and (.eq (.var p.1) p.2) (reqC ps)

theorem lexLtC_eval (ρ : Nat → Nat) (M : Nat → Nat → Nat) : ∀ as' as : List E,
    evalC ρ M (lexLtC as' as) = lexB (as'.map (evalE ρ M)) (as.map (evalE ρ M))
  | a' :: as', a :: as => by simp only [lexLtC, lexB, evalC, List.map_cons, lexLtC_eval ρ M as' as]
  | [], _ => by simp [lexLtC, lexB, evalC, falseC]
  | _ :: _, [] => by simp [lexLtC, lexB, evalC, falseC]

theorem eqsC_eval (ρ : Nat → Nat) (M : Nat → Nat → Nat) : ∀ as' as : List E, as'.length = as.length →
    (evalC ρ M (eqsC as' as) = true ↔ as'.map (evalE ρ M) = as.map (evalE ρ M))
  | a' :: as', a :: as, h => by
    simp only [eqsC, evalC, Bool.and_eq_true, decide_eq_true_eq, List.map_cons, List.cons.injEq, eqsC_eval ρ M as' as (by simpa using h)]
  | [], [], _ => by simp [eqsC, evalC, trueC]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem keepC_eval (ρ : Nat → Nat) (M : Nat → Nat → Nat) (pr pm : List (Nat × Nat)) : ∀ ws : List C,
    evalC ρ M (keepC pr pm ws) = true ↔ ∀ w ∈ ws, evalC ρ M w = true → evalC ρ M (primeC pr pm w) = true
  | [] => by simp [keepC, evalC, trueC]
  | w :: ws => by
    rw [List.forall_mem_cons, ← keepC_eval ρ M pr pm ws]
    simp only [keepC, evalC, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    cases evalC ρ M w <;> simp

theorem anyC_eval (ρ : Nat → Nat) (M : Nat → Nat → Nat) : ∀ ws : List C, evalC ρ M (anyC ws) = true ↔ ∃ w ∈ ws, evalC ρ M w = true
  | [] => by simp [anyC, evalC, falseC]
  | w :: ws => by simp only [anyC, evalC, Bool.or_eq_true, anyC_eval ρ M ws, List.mem_cons, exists_eq_or_imp]

theorem reqC_eval (ρ : Nat → Nat) (M : Nat → Nat → Nat) : ∀ ps : List (Nat × E), evalC ρ M (reqC ps) = true ↔ ∀ p ∈ ps, ρ p.1 = evalE ρ M p.2
  | [] => by simp [reqC, evalC, trueC]
  | p :: ps => by
    rw [List.forall_mem_cons, ← reqC_eval ρ M ps]
    simp only [reqC, evalC, evalE, Bool.and_eq_true]
    exact ⟨fun h => ⟨of_decide_eq_true h.1, h.2⟩, fun h => ⟨decide_eq_true h.1, h.2⟩⟩

theorem zip_cover {α β : Type} : ∀ (as : List α) (bs : List β), as.length = bs.length → ∀ a ∈ as, ∃ b, (a, b) ∈ as.zip bs
  | [], [], _, a, ha => by simp at ha
  | a :: as, b :: bs, h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, by simp⟩
    · obtain ⟨b', hb'⟩ := zip_cover as bs (by simpa using h) x hx
      exact ⟨b', by simp [hb']⟩
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h

/-! Liveness -/

structure Live where
  from_ : C
  to : C
  rank : List E                         -- compared in order
  helps : List (C × List (Nat × E))     -- (the region where it helps, the request: an input and its term over the state and params)
  prime : List (Nat × Nat)              -- a state variable, and its primed name
  primeMaps : List (Nat × Nat)          -- a map, and its primed name

def Live.pend (l : Live) : C := .and l.from_ (.not l.to)
def liveStayC (l : Live) : C :=
  .and (.or (primeC l.prime l.primeMaps l.from_) (primeC l.prime l.primeMaps l.to))
    (.or (primeC l.prime l.primeMaps l.to) (.or (lexLtC (l.rank.map (primeE l.prime l.primeMaps)) l.rank)
      (.and (eqsC (l.rank.map (primeE l.prime l.primeMaps)) l.rank) (keepC l.prime l.primeMaps (l.helps.map (·.1))))))
def liveCoverC (l : Live) : C := anyC (l.helps.map (·.1))
def liveHelpWhen (l : Live) (h : C × List (Nat × E)) : C := .and l.pend (.and h.1 (reqC h.2))
def liveHelpThen (l : Live) : C := .or (primeC l.prime l.primeMaps l.to) (lexLtC (l.rank.map (primeE l.prime l.primeMaps)) l.rank)
-- What reads the state alone: `from`, `to`, each part of the rank and each region.
def liveConds (l : Live) : List C := [l.from_, l.to] ++ l.rank.map (fun e => .eq e e) ++ l.helps.map (·.1)

theorem mem_conds_rank {l : Live} {e : E} (he : e ∈ l.rank) : C.eq e e ∈ liveConds l := by
  simp only [liveConds, List.mem_append, List.mem_map]; exact Or.inl (Or.inr ⟨e, he, rfl⟩)

/-- The argument, given how each step reads: `B`, `BM` the state and maps `when` reads (with the request), `A`, `AM`
those `then` reads (primed names after the step). -/
theorem leads_view (l : Live) (st : Nat → (Nat → Nat) × (Nat → Nat → Nat)) (B A : Nat → Nat → Nat) (BM AM : Nat → Nat → Nat → Nat)
    (H En : C × List (Nat × E) → Nat → Prop)
    (hC : ∀ n, ∀ c ∈ liveConds l, evalC (A n) (AM n) (primeC l.prime l.primeMaps c) = evalC (st (n + 1)).1 (st (n + 1)).2 c
      ∧ evalC (A n) (AM n) c = evalC (st n).1 (st n).2 c ∧ evalC (B n) (BM n) c = evalC (st n).1 (st n).2 c)
    (hE : ∀ n, ∀ e ∈ l.rank, evalE (A n) (AM n) (primeE l.prime l.primeMaps e) = evalE (st (n + 1)).1 (st (n + 1)).2 e
      ∧ evalE (A n) (AM n) e = evalE (st n).1 (st n).2 e)
    (hstay : ∀ n, evalC (B n) (BM n) l.pend = true → evalC (A n) (AM n) (liveStayC l) = true)
    (hcover : ∀ n, evalC (B n) (BM n) l.pend = true → evalC (A n) (AM n) (liveCoverC l) = true)
    (hhelp : ∀ h ∈ l.helps, ∀ n, evalC (B n) (BM n) (liveHelpWhen l h) = true → evalC (A n) (AM n) (liveHelpThen l) = true)
    (hreq : ∀ h ∈ l.helps, ∀ n, H h n → evalC (B n) (BM n) (reqC h.2) = true)
    (henabled : ∀ h ∈ l.helps, ∀ n, evalC (st n).1 (st n).2 l.from_ = true → evalC (st n).1 (st n).2 l.to = false →
      evalC (st n).1 (st n).2 h.1 = true → En h n)
    (fair : ∀ h ∈ l.helps, ∀ n, (∀ m, n ≤ m → En h m) → ∃ m, n ≤ m ∧ H h m) :
    ∀ n, evalC (st n).1 (st n).2 l.from_ = true → ∃ m, n ≤ m ∧ evalC (st m).1 (st m).2 l.to = true := by
  have memF : l.from_ ∈ liveConds l := by simp [liveConds]
  have memT : l.to ∈ liveConds l := by simp [liveConds]
  have memH : ∀ h ∈ l.helps, h.1 ∈ liveConds l := fun h hh => by
    simp only [liveConds, List.mem_append, List.mem_map]; exact Or.inr ⟨h, hh, rfl⟩
  have h1 : ∀ n, (l.rank.map (primeE l.prime l.primeMaps)).map (evalE (A n) (AM n)) = l.rank.map (evalE (st (n + 1)).1 (st (n + 1)).2) := by
    intro n; rw [List.map_map]; exact List.map_congr_left (fun e he => (hE n e he).1)
  have h2 : ∀ n, l.rank.map (evalE (A n) (AM n)) = l.rank.map (evalE (st n).1 (st n).2) := fun n =>
    List.map_congr_left (fun e he => (hE n e he).2)
  have hlex : ∀ n, evalC (A n) (AM n) (lexLtC (l.rank.map (primeE l.prime l.primeMaps)) l.rank)
      = lexB (l.rank.map (evalE (st (n + 1)).1 (st (n + 1)).2)) (l.rank.map (evalE (st n).1 (st n).2)) := by
    intro n; rw [lexLtC_eval, h1, h2]
  have heqs : ∀ n, evalC (A n) (AM n) (eqsC (l.rank.map (primeE l.prime l.primeMaps)) l.rank) = true
      ↔ l.rank.map (evalE (st (n + 1)).1 (st (n + 1)).2) = l.rank.map (evalE (st n).1 (st n).2) := by
    intro n; rw [eqsC_eval _ _ _ _ (by simp), h1, h2]
  have hpend : ∀ n, evalC (st n).1 (st n).2 l.from_ = true → ¬ evalC (st n).1 (st n).2 l.to = true → evalC (B n) (BM n) l.pend = true := by
    intro n hP hnQ
    simp only [Live.pend, evalC, Bool.and_eq_true, Bool.not_eq_true']
    rw [(hC n _ memF).2.2, (hC n _ memT).2.2]; exact ⟨hP, by simpa using hnQ⟩
  refine leads_of_lex (fun n => evalC (st n).1 (st n).2 l.from_ = true) (fun n => evalC (st n).1 (st n).2 l.to = true)
    (fun n => l.rank.map (evalE (st n).1 (st n).2)) l.rank.length (fun n => by simp) l.helps
    (fun h n => evalC (st n).1 (st n).2 h.1 = true) H En ?_ ?_ ?_ (fun h hh n hP hnQ hW => henabled h hh n hP (by simpa using hnQ) hW) fair
  · intro n hP hnQ
    have h := hstay n (hpend n hP hnQ)
    simp only [liveStayC, evalC, Bool.and_eq_true, Bool.or_eq_true] at h
    rw [(hC n _ memF).1, (hC n _ memT).1, hlex n, heqs n, keepC_eval] at h
    refine ⟨h.1, ?_⟩
    rcases h.2 with h2 | h2 | ⟨h2, h3⟩
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
    · refine Or.inr (Or.inr ⟨h2, fun hp hhp hW => ?_⟩)
      have := h3 hp.1 (List.mem_map_of_mem hhp) (by rw [(hC n _ (memH hp hhp)).2.1]; exact hW)
      rwa [(hC n _ (memH hp hhp)).1] at this
  · intro n hP hnQ
    have h := hcover n (hpend n hP hnQ)
    rw [liveCoverC, anyC_eval] at h
    obtain ⟨w, hw, hW⟩ := h
    obtain ⟨hp, hhp, rfl⟩ := List.mem_map.mp hw
    exact ⟨hp, hhp, by rw [← (hC n _ (memH hp hhp)).2.1]; exact hW⟩
  · intro hp hhp n hP hnQ hW hH
    have hB : evalC (B n) (BM n) (liveHelpWhen l hp) = true := by
      have := hpend n hP hnQ
      simp only [liveHelpWhen, evalC, Bool.and_eq_true]
      rw [(hC n _ (memH hp hhp)).2.2]
      exact ⟨this, hW, hreq hp hhp n hH⟩
    have h := hhelp hp hhp n hB
    simp only [liveHelpThen, evalC, Bool.or_eq_true] at h
    rwa [(hC n _ memT).1, hlex n] at h

theorem assoc_distinct : ∀ {σ : List (Nat × E)}, distinct (σ.map (·.1)) = true → ∀ {p}, p ∈ σ → assoc σ p.1 = some p.2
  | [], _, _, hp => by simp at hp
  | a :: as, hd, p, hp => by
    simp only [List.map_cons, distinct, Bool.and_eq_true, Bool.not_eq_true'] at hd
    simp only [assoc, lookup]
    rcases List.mem_cons.mp hp with rfl | hp
    · simp
    · have hne : (a.1 == p.1) = false := by
        simp only [beq_eq_false_iff_ne]; intro he
        have h1 : (as.map (·.1)).contains a.1 = true := List.contains_iff_mem.mpr (by rw [he]; exact List.mem_map_of_mem hp)
        rw [hd.1] at h1; cases h1
      simp only [hne, Bool.false_eq_true, if_false]
      have := assoc_distinct hd.2 hp
      simpa [assoc] using this

/-! Machines with sets -/

-- As for maps and flags, with the request's extended variables (inputs, quantified flags, witnesses) and the maps it
-- carries read by no part of the liveness, and maps written at every key unprimed counted as written.
def sliveVars (s : SMachine) (l : Live) : List Nat :=
  l.prime.map (·.2) ++ s.extVars ++ (flagVars s.f.flags ++ s.f.m.step.map (·.1)).filter (fun i => !(l.prime.map (·.1)).contains i)
def sliveMaps (s : SMachine) (l : Live) : List Nat :=
  l.primeMaps.map (·.2) ++ s.carried ++ (s.f.m.writes.map (·.1) ++ s.every.map (·.1)).filter (fun mp => !(l.primeMaps.map (·.1)).contains mp)
def sliveOk (s : SMachine) (l : Live) : Bool :=
  distinct (l.prime.map (·.2)) && distinct (l.primeMaps.map (·.2))
    && (liveConds l).all (fun c => avoids (sliveVars s l) c && avoidsMaps (sliveMaps s l) c)
    && l.helps.all (fun h => h.2.all (fun p => s.f.m.inputs.contains p.1 && avoids s.extVars (.eq p.2 p.2) && avoidsMaps s.carried (.eq p.2 p.2)))

-- A step law over sets's proof: (law instances, quantified flag instances, fact instances, several-key instances, tree).
-- A proof's instances (laws, quantified flags, facts, laws about several keys, facts about several keys) and its certificate.
abbrev SProof := List (Nat × E) × List (Nat × List E) × List (Nat × E) × List (Nat × E × List E) × List (Nat × E × List E) × Cert
def sliveStep (l : Live) (w t : C) (p : SProof) : SKStep :=
  ⟨⟨[w], t, [[]], l.prime, l.primeMaps, p.1, (p.2.2.2.2.2.1, p.2.2.2.2.2.2.2)⟩, [[]], p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.2.1, []⟩
def sliveHelpsOk (s : SMachine) (ps : List SEntry) (l : Live) (hp : List SProof) : Bool :=
  l.helps.length == hp.length && (l.helps.zip hp).all (fun x => checkSKStep s ps (sliveStep l (liveHelpWhen l x.1) (liveHelpThen l) x.2))

-- A run of a machine with sets: each step a request (inputs, the maps it carries) the machine allows.
structure SRun (s : SMachine) where
  st : Nat → (Nat → Nat) × (Nat → Nat → Nat)
  req : Nat → SRequest
  start : SReach s (st 0).1 (st 0).2
  allowed : ∀ n, evalC (sView s (st n).1 (st n).2 (req n).1 (req n).2).1 (sView s (st n).1 (st n).2 (req n).1 (req n).2).2 s.f.m.assume = true
  next : ∀ n, st (n + 1) = sNext s (st n).1 (st n).2 (req n).1 (req n).2

theorem srun_reach {s : SMachine} (run : SRun s) : ∀ n, SReach s (run.st n).1 (run.st n).2
  | 0 => run.start
  | n + 1 => by rw [run.next n]; exact SReach.step _ _ _ _ (srun_reach run n) (run.allowed n)

-- A step law over sets of one step: every request allowed that `when` admits takes a step where `then` holds.
theorem skstep_one {s : SMachine} {ps : List SEntry} {l : Live} {w t : C} {p : SProof} (hl : checkSMachine s ps = true)
    (hc : checkSKStep s ps (sliveStep l w t p) = true) : ∀ ρ M, SReach s ρ M → ∀ ι κ,
      evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume = true →
      evalC (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ) w = true →
      evalC (primed l.prime (sNext s ρ M ι κ).1 (withExt s ρ (sReq s ρ M ι κ)))
        (primedMaps l.primeMaps (sNext s ρ M ι κ).2 (withCarried s M κ)) t = true := by
  intro ρ M hr ι κ hA hW
  have h := skstep_sound s ps _ hl hc ρ M hr (ι, κ) [] rfl ⟨hA, hW, trivial⟩
  simpa [sliveStep, sEnd, sExts, renEnv, renMaps, lookup] using h

-- A step law over sets of one step, read as one step: every request allowed that `when` admits takes a step where `then`
-- holds, its fresh names read as the step reads them.
theorem skstep_holds_one {s : SMachine} {sl : SKStep} {w : C} (h : SKStepHolds s sl) (hw : sl.k.whens = [w]) (hren : sl.k.ren = [[]])
    (hmren : sl.mren = [[]]) : ∀ ρ M, SReach s ρ M → ∀ ι κ,
      evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume = true →
      evalC (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ) w = true →
      evalC (primed sl.k.prime (sNext s ρ M ι κ).1 (withExt s ρ (sReq s ρ M ι κ)))
        (primedMaps sl.k.primeMaps (sNext s ρ M ι κ).2 (withCarried s M κ)) sl.k.then_ = true := by
  intro ρ M hr ι κ hA hW
  have := h ρ M hr (ι, κ) [] (by simp [hw]) (by rw [hw]; exact ⟨hA, hW, trivial⟩)
  rw [hren, hmren] at this
  simpa [sEnd, sExts, renEnv, renMaps, lookup] using this

theorem decideQ_other {s : SMachine} {i : Nat} (h : i ∉ s.qVars) (X : Nat → Nat) (N : Nat → Nat → Nat) : decideQ s X N i = X i := by
  simp only [decideQ]
  rw [lookup_none (fun q hq => by
    simp only [beq_eq_false_iff_ne]; intro he; exact h (by rw [← he]; exact List.mem_map_of_mem hq))]

theorem slive_reads {s : SMachine} {l : Live} (hok : sliveOk s l = true) {c : C} (hc : c ∈ liveConds l)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    (∀ i, occC i c = true → i ∉ l.prime.map (·.2) ∧ (i ∈ l.prime.map (·.1) ∨ (sNext s ρ M ι κ).1 i = withExt s ρ (sReq s ρ M ι κ) i))
      ∧ (∀ mp, occMC mp c = true → mp ∉ l.primeMaps.map (·.2) ∧ (mp ∈ l.primeMaps.map (·.1) ∨ (sNext s ρ M ι κ).2 mp = withCarried s M κ mp))
      ∧ (∀ i, occC i c = true → withExt s ρ (sReq s ρ M ι κ) i = ρ i)
      ∧ (∀ mp, occMC mp c = true → withCarried s M κ mp = M mp) := by
  simp only [sliveOk, Bool.and_eq_true, List.all_eq_true] at hok
  have hv := hok.1.2 c hc
  have noExt : ∀ i, occC i c = true → i ∉ s.extVars := fun i hi hm => avoids_occ hv.1 hi (List.mem_append_left _ (List.mem_append_right _ hm))
  have hext : ∀ i, occC i c = true → withExt s ρ (sReq s ρ M ι κ) i = ρ i := fun i hi => by
    simp only [withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using noExt i hi)]
  have noCar : ∀ mp, occMC mp c = true → mp ∉ s.carried := fun mp hmp hm => avoidsMaps_occ hv.2 hmp (List.mem_append_left _ (List.mem_append_right _ hm))
  have hcar : ∀ mp, occMC mp c = true → withCarried s M κ mp = M mp := fun mp hmp => by
    simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using noCar mp hmp)]
  refine ⟨fun i hi => ⟨fun h => avoids_occ hv.1 hi (List.mem_append_left _ (List.mem_append_left _ h)), ?_⟩,
    fun mp hmp => ⟨fun h => avoidsMaps_occ hv.2 hmp (List.mem_append_left _ (List.mem_append_left _ h)), ?_⟩, hext, hcar⟩
  · by_cases hp : i ∈ l.prime.map (·.1)
    · exact Or.inl hp
    · right
      have hn : i ∉ flagVars s.f.flags ++ s.f.m.step.map (·.1) := fun hm =>
        avoids_occ hv.1 hi (List.mem_append_right _ (List.mem_filter.mpr ⟨hm, by simpa [List.contains_iff_mem] using hp⟩))
      have hx := noExt i hi
      simp only [SMachine.extVars, SMachine.qVars, List.mem_append, not_or] at hx
      rw [hext i hi]
      simp only [sNext, sView]
      rw [applyS_other (fun h => hn (List.mem_append_right _ h)), decide_other (fun h => hn (List.mem_append_left _ h)),
        decideQ_other (by simpa [SMachine.qVars] using hx.1.2), withInputs_other hx.1.1]
  · by_cases hp : mp ∈ l.primeMaps.map (·.1)
    · exact Or.inl hp
    · right
      have hw : mp ∉ s.f.m.writes.map (·.1) ++ s.every.map (·.1) := fun hm =>
        avoidsMaps_occ hv.2 hmp (List.mem_append_right _ (List.mem_filter.mpr ⟨hm, by simpa [List.contains_iff_mem] using hp⟩))
      funext k
      simp only [sNext, everyMaps]
      rw [lookup_none (fun w hw' => by simp only [beq_eq_false_iff_ne]; intro he; exact hw (List.mem_append_right _ (by rw [← he]; exact List.mem_map_of_mem hw')))]
      simp only [writeMaps]
      rw [lookup_none (fun w hw' => by simp only [beq_eq_false_iff_ne]; intro he; exact hw (List.mem_append_left _ (by rw [← he]; exact List.mem_map_of_mem hw')))]
      rfl

/-- Liveness under fairness: if the laws' proof checks, the liveness reads what it may (`sliveOk`), and the step laws Lean
builds from it check, then along every run that takes each helpful request (its named inputs as its terms; the rest,
and the maps it carries, free) infinitely often, each state where `from` holds is followed by one where `to` holds. -/
theorem sleads_sound (s : SMachine) (ps : List SEntry) (l : Live) (sp cp : SProof) (hp : List SProof)
    (hl : checkSMachine s ps = true) (hok : sliveOk s l = true)
    (hs : checkSKStep s ps (sliveStep l l.pend (liveStayC l) sp) = true) (hc : checkSKStep s ps (sliveStep l l.pend (liveCoverC l) cp) = true)
    (hh : sliveHelpsOk s ps l hp = true) (run : SRun s)
    (fair : ∀ h ∈ l.helps, ∀ n, ∃ m, n ≤ m ∧ ∀ p ∈ h.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 l.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 l.to = true := by
  have hok0 := hok
  simp only [sliveOk, Bool.and_eq_true, List.all_eq_true] at hok0
  obtain ⟨⟨⟨hd1, hd2⟩, _⟩, hreqs⟩ := hok0
  simp only [sliveHelpsOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hh
  obtain ⟨hlen, hall⟩ := hh
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
    have := skstep_one hl hs _ _ (srun_reach run n) _ _ (run.allowed n) hB
    rw [run.next n]; exact this
  · intro n hB
    have := skstep_one hl hc _ _ (srun_reach run n) _ _ (run.allowed n) hB
    rw [run.next n]; exact this
  · intro h hmem n hB
    obtain ⟨pp, hpp⟩ := zip_cover l.helps hp hlen h hmem
    have := skstep_one hl (hall _ hpp) _ _ (srun_reach run n) _ _ (run.allowed n) hB
    rw [run.next n]; exact this
  · intro h hmem n hH
    show evalC (withExt s (run.st n).1 (sReq s (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2)) (withCarried s (run.st n).2 (run.req n).2) (reqC h.2) = true
    rw [reqC_eval]
    intro p hp'
    have hq := hreqs h hmem p hp'
    obtain ⟨⟨hin, hav⟩, havm⟩ := hq
    have hext : s.extVars.contains p.1 = true := by
      simp only [SMachine.extVars, List.contains_iff_mem, List.mem_append]; exact Or.inl (Or.inl (List.contains_iff_mem.mp hin))
    have hl1 : withExt s (run.st n).1 (sReq s (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2) p.1 = (run.req n).1 p.1 := by
      simp only [withExt, hext, if_true, sReq, hin]
    have hr1 : evalE (withExt s (run.st n).1 (sReq s (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2)) (withCarried s (run.st n).2 (run.req n).2) p.2
        = evalE (run.st n).1 (run.st n).2 p.2 := by
      rw [congrME _ _ (run.st n).2 p.2 (fun mp hmp => by
        simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using avoidsMaps_occ havm (by simp [occMC, hmp]))])]
      exact congrE _ _ _ p.2 (fun i hi => by
        simp only [withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using avoids_occ hav (by simp [occC, hi]))])
    rw [hl1, hr1]; exact hH p hp'

/-! Weak fairness over sets -/

-- A request whose inputs named in a list are the list's terms meets the list's condition, in the goal's view.
theorem sreq_list {s : SMachine} {ps' : List (Nat × E)}
    (hc : ∀ p ∈ ps', (s.f.m.inputs.contains p.1 = true ∧ avoids s.extVars (.eq p.2 p.2) = true) ∧ avoidsMaps s.carried (.eq p.2 p.2) = true)
    {ρ : Nat → Nat} {M : Nat → Nat → Nat} {ι : Nat → Nat} {κ : Nat → Nat → Nat} (hH : ∀ p ∈ ps', ι p.1 = evalE ρ M p.2) :
    evalC (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ) (reqC ps') = true := by
  rw [reqC_eval]
  intro p hp'
  obtain ⟨⟨hin, hav⟩, havm⟩ := hc p hp'
  have hext : s.extVars.contains p.1 = true := by
    simp only [SMachine.extVars, List.contains_iff_mem, List.mem_append]; exact Or.inl (Or.inl (List.contains_iff_mem.mp hin))
  have hl1 : withExt s ρ (sReq s ρ M ι κ) p.1 = ι p.1 := by simp only [withExt, hext, if_true, sReq, hin]
  have hr1 : evalE (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ) p.2 = evalE ρ M p.2 := by
    rw [congrME _ _ M p.2 (fun mp hmp => by
      simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using avoidsMaps_occ havm (by simp [occMC, hmp]))])]
    exact congrE _ _ _ p.2 (fun i hi => by
      simp only [withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using avoids_occ hav (by simp [occC, hi]))])
  rw [hl1, hr1]; exact hH p hp'

theorem sreq_holds {s : SMachine} {l : Live} (hok : sliveOk s l = true) {h : C × List (Nat × E)} (hmem : h ∈ l.helps)
    {ρ : Nat → Nat} {M : Nat → Nat → Nat} {ι : Nat → Nat} {κ : Nat → Nat → Nat} (hH : ∀ p ∈ h.2, ι p.1 = evalE ρ M p.2) :
    evalC (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ) (reqC h.2) = true := by
  simp only [sliveOk, Bool.and_eq_true, List.all_eq_true] at hok
  exact sreq_list (fun p hp' => hok.2 h hmem p hp') hH

-- A helpful request allowed in its region, carrying empty sets: the precondition, the facts, the laws, `when`, each
-- quantified flag closed, and the carried maps empty at the keys the proof names refute the assumption's failing. The
-- facts read no request's variable or map.
def zeroHyps (s : SMachine) (zkeys : List E) : List C := s.carried.flatMap fun mp => zkeys.map fun t => .eq (.get mp t) (.const 0)
def sAllowGoal (s : SMachine) (ps : List SEntry) (w : C) (p : SProof) (zkeys : List E) : List C :=
  [s.f.m.pre] ++ factHyps s p.2.2.1 p.2.2.2.2.1 ++ (scalarHyps (sLaws ps p.2.2.2.1) ++ instHyps (sLaws ps p.2.2.2.1) (sInsts ps p.1 p.2.2.2.1))
    ++ [w] ++ closingHyps s p.2.1 ++ zeroHyps s zkeys ++ [.not (inlineC s.f.flags s.f.m.assume)]
def checkSAllow (s : SMachine) (ps : List SEntry) (w : C) (p : SProof) (zkeys : List E) : Bool :=
  s.facts.all (fun l => avoids s.extVars l.holds && avoidsMaps s.carried l.holds)
    && checkIn (sAllowGoal s ps w p zkeys) p.2.2.2.2.2

-- The request carrying empty sets.
def noSets : Nat → Nat → Nat := fun _ _ => 0

theorem sallow_sound (s : SMachine) (ps : List SEntry) (w : C) (p : SProof) (zkeys : List E)
    (hl : checkSMachine s ps = true) (hc : checkSAllow s ps w p zkeys = true) :
    ∀ ρ M, SReach s ρ M → ∀ ι, evalC (withExt s ρ (sReq s ρ M ι noSets)) (withCarried s M noSets) w = true →
      evalC (sView s ρ M ι noSets).1 (sView s ρ M ι noSets).2 s.f.m.assume = true := by
  intro ρ M hr ι hw
  simp only [checkSAllow, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨hfa, hgoal⟩ := hc
  have hs := sOk_of hl
  obtain ⟨hpreS, hrp⟩ := spre_parts hl
  let W := withExt s ρ (sReq s ρ M ι noSets)
  let M0 := withCarried s M noSets
  have hWo : ∀ v, v ∉ s.extVars → W v = ρ v := fun v hv => by
    simp only [W, withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hv)]
  have hMo : ∀ mp, mp ∉ s.carried → M0 mp = M mp := fun mp hmp => by
    simp only [M0, withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmp)]
  -- Every entry, and each pair's, holds in the goal's view of the state.
  have hall : ∀ e ∈ ps, e.Holds W M0 := fun e he =>
    sentry_transfer (slaws_avoid hl e.law (List.mem_map_of_mem he)).1 (slaws_avoid hl e.law (List.mem_map_of_mem he)).2
      (fun i hi => by simp only [W, withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hi)])
      (fun mp hmp => by simp only [M0, withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmp)])
      (smachine_sound s ps hl ρ M hr e he)
  have hlY : ∀ l ∈ sLaws ps p.2.2.2.1, l.Holds W M0 := fun l hl' => by
    rcases List.mem_append.mp hl' with hl' | hl'
    · obtain ⟨e', he', rfl⟩ := List.mem_map.mp hl'; exact SEntry.holds_law (hall e' he')
    · exact pairLaws_hold ps p.2.2.2.1 (skeys_apart hl) hall l hl'
  have hfacts : ∀ l ∈ s.facts, l.Holds W M0 := fun l hl' => by
    have h := hfa l hl'
    exact holds_transfer l h.1 h.2 (fun i hi => hWo i hi) (fun mp hmp => hMo mp hmp) (facts_sreach s (sfacts_ok hl) hr l hl')
  apply Decidable.byContradiction; intro hn
  apply sound_in _ _ hgoal W M0
  intro c hc
  simp only [sAllowGoal, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (((((rfl | hc) | hc) | rfl) | hc) | hc) | rfl
  · rw [noReadsC W M0 M s.f.m.pre hrp, congrC W ρ M s.f.m.pre (fun j hj => hWo j (fun h' =>
      avoids_occ hpreS hj (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h')))))]
    exact pre_sreach s hpreS hrp hr
  · -- The facts about several keys, as the reachable state has them: they read no request and no carried map.
    have hpf : s.PFacts W M0 := fun f hf' =>
      holdsOver_transfer f.1 (pfactsOk_parts (sfacts_ok hl) f hf').1 (pfactsOk_parts (sfacts_ok hl) f hf').2.1 f.2
        (fun i hi => hWo i (fun h' => hi (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h')))))
        (fun mp hmp => hMo mp (fun h' => hmp (List.mem_append_left _ (List.mem_append_left _ h'))))
        (pfacts_sreach s (sfacts_ok hl) hr f hf')
    exact facthyps_true s p.2.2.1 p.2.2.2.2.1 W M0 (fun f hf' => (pfactsOk_parts (sfacts_ok hl) f hf').2.2) hfacts hpf c hc
  · exact laws_hyps_true _ _ W M0 hlY c (List.mem_append.mpr hc)
  · exact hw
  · exact closing_true s ρ M ι noSets hs p.2.1 c hc
  · simp only [zeroHyps, List.mem_flatMap, List.mem_map] at hc
    obtain ⟨mp, hmp, t, _, rfl⟩ := hc
    simp only [evalC, evalE, M0, withCarried, List.contains_iff_mem.mpr hmp, if_true, noSets, decide_eq_true_eq]
  · -- The assumption, inlined: the view decides the plain flags as the step does, away from the witnesses.
    simp only [evalC, Bool.not_eq_true']
    rw [inline_evalC]
    have hagD := decide_agree_on (sOk_parts s hs).2.2.2.2.2.2 (withCarried s M noSets) (view_agree s ρ M ι noSets hs)
    rw [congrC _ (decideFlags s.f.flags (decideQ s (withInputs s.f.m.inputs ρ ι) (withCarried s M noSets)) (withCarried s M noSets)) _ s.f.m.assume
      (fun i hi => (hagD i (fun h => by
        have hpa : avoids s.wVars s.f.m.assume = true := by simp only [sOk, Bool.and_eq_true] at hs; exact hs.2
        exact avoids_occ hpa hi h)).symm)]
    have hf : evalC (sView s ρ M ι noSets).1 (sView s ρ M ι noSets).2 s.f.m.assume = false := by simpa using hn
    exact hf

def sliveAllowsOk (s : SMachine) (ps : List SEntry) (l : Live) (ap : List (List (Nat × E) × SProof × List E)) : Bool :=
  l.helps.length == ap.length
    && (l.helps.zip ap).all (fun x => distinct ((x.1.2 ++ x.2.1).map (·.1))
      && x.2.1.all (fun p => s.f.m.inputs.contains p.1 && avoids s.extVars (.eq p.2 p.2) && avoidsMaps s.carried (.eq p.2 p.2))
      && checkSAllow s ps (.and (liveHelpWhen l x.1) (reqC x.2.1)) x.2.2.1 x.2.2.2)

/-- Liveness under weak fairness, for machines with sets: as `sleads_sound`, with each helpful request also proven
allowed in its region carrying empty sets (`sliveAllowsOk`); then along every run that takes each helpful request
whenever, from some point on, it stays allowed (some request with its named inputs as its terms, carrying some sets, is a
step the machine allows), each state where `from` holds is followed by one where `to` holds. -/
theorem sleads_wf_sound (s : SMachine) (ps : List SEntry) (l : Live) (sp cp : SProof) (hp : List SProof) (ap : List (List (Nat × E) × SProof × List E))
    (hl : checkSMachine s ps = true) (hok : sliveOk s l = true)
    (hs : checkSKStep s ps (sliveStep l l.pend (liveStayC l) sp) = true) (hc : checkSKStep s ps (sliveStep l l.pend (liveCoverC l) cp) = true)
    (hh : sliveHelpsOk s ps l hp = true) (ha : sliveAllowsOk s ps l ap = true) (run : SRun s)
    (fair : ∀ h ∈ l.helps, ∀ n, (∀ m, n ≤ m → ∃ ι κ, (∀ p ∈ h.2, ι p.1 = evalE (run.st m).1 (run.st m).2 p.2)
        ∧ evalC (sView s (run.st m).1 (run.st m).2 ι κ).1 (sView s (run.st m).1 (run.st m).2 ι κ).2 s.f.m.assume = true) →
      ∃ m, n ≤ m ∧ ∀ p ∈ h.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 l.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 l.to = true := by
  have hok0 := hok
  simp only [sliveOk, Bool.and_eq_true, List.all_eq_true] at hok0
  obtain ⟨⟨⟨hd1, hd2⟩, _⟩, hreqs⟩ := hok0
  simp only [sliveHelpsOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hh
  obtain ⟨hlen, hall⟩ := hh
  simp only [sliveAllowsOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ha
  obtain ⟨halen, haall⟩ := ha
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
    have := skstep_one hl hs _ _ (srun_reach run n) _ _ (run.allowed n) hB
    rw [run.next n]; exact this
  · intro n hB
    have := skstep_one hl hc _ _ (srun_reach run n) _ _ (run.allowed n) hB
    rw [run.next n]; exact this
  · intro h hmem n hB
    obtain ⟨pp, hpp⟩ := zip_cover l.helps hp hlen h hmem
    have := skstep_one hl (hall _ hpp) _ _ (srun_reach run n) _ _ (run.allowed n) hB
    rw [run.next n]; exact this
  · intro h hmem n hH
    show evalC (withExt s (run.st n).1 (sReq s (run.st n).1 (run.st n).2 (run.req n).1 (run.req n).2)) (withCarried s (run.st n).2 (run.req n).2) (reqC h.2) = true
    exact sreq_holds hok hmem (fun p hp' => hH p hp')
  · -- Enabled in its region: the request with its named inputs as its terms, the rest as the state has them, carrying
    -- empty sets.
    intro h hmem n hP hnQ hW
    obtain ⟨x, hx⟩ := zip_cover l.helps ap halen h hmem
    obtain ⟨⟨hdist, hwit⟩, hpc⟩ := haall _ hx
    let ρ := (run.st n).1
    let M := (run.st n).2
    let ι := applyS (h.2 ++ x.1) ρ M
    have hιp : ∀ p ∈ h.2, ι p.1 = evalE ρ M p.2 := fun p hp' => by
      simp only [ι, applyS, assoc_distinct hdist (List.mem_append_left _ hp')]
    have hιw : ∀ p ∈ x.1, ι p.1 = evalE ρ M p.2 := fun p hp' => by
      simp only [ι, applyS, assoc_distinct hdist (List.mem_append_right _ hp')]
    have hX : ∀ c ∈ liveConds l, evalC (withExt s ρ (sReq s ρ M ι noSets)) (withCarried s M noSets) c = evalC ρ M c := fun c hc' => by
      obtain ⟨_, _, hx', hn'⟩ := slive_reads hok hc' ρ M ι noSets
      rw [congrMC _ _ M c hn']; exact congrC _ _ M c hx'
    have memF : l.from_ ∈ liveConds l := by simp [liveConds]
    have memT : l.to ∈ liveConds l := by simp [liveConds]
    have memH : h.1 ∈ liveConds l := by simp only [liveConds, List.mem_append, List.mem_map]; exact Or.inr ⟨h, hmem, rfl⟩
    refine ⟨ι, noSets, hιp, sallow_sound s ps _ x.2.1 x.2.2 hl hpc ρ M (srun_reach run n) ι ?_⟩
    simp only [liveHelpWhen, Live.pend, evalC, Bool.and_eq_true, Bool.not_eq_true']
    rw [hX _ memF, hX _ memT, hX _ memH]
    exact ⟨⟨⟨hP, hnQ⟩, hW, sreq_holds hok hmem hιp⟩, sreq_list (fun p hp' => hwit p hp') hιw⟩

/-! Loops, as machines -/

-- A loop as a machine with sets (none of them): the loop's state, inputs, precondition and assumption, its body taken
-- where the guard holds and the state kept where it doesn't. That it halts is a liveness claim: every request helps,
-- `to` is the guard failing, and the loop's ranks drop.
def Loop.machine (l : Loop) : SMachine :=
  ⟨⟨⟨l.inputs, l.init, [], l.body.map (fun p => (p.1, E.ite l.guard p.2 (.var p.1))), [], l.pre, l.assume⟩, []⟩, [], [], [], [], [], []⟩

theorem assoc_guarded (g : C) (i : Nat) : ∀ body : List (Nat × E),
    assoc (body.map fun p => (p.1, E.ite g p.2 (.var p.1))) i = (assoc body i).map fun e => E.ite g e (.var i)
  | [] => rfl
  | p :: ps => by
    simp only [List.map_cons, assoc, lookup] at ⊢
    by_cases h : (p.1 == i) = true
    · have hp : p.1 = i := beq_iff_eq.mp h
      simp only [h, ite_true, Option.map_some]; rw [hp]
    · simp only [h, Bool.false_eq_true, ite_false]
      have := assoc_guarded g i ps
      simp only [assoc] at this; exact this

-- The loop's machine reads a request as the loop does: its inputs set, nothing decided, no map carried.
theorem sView_loop (l : Loop) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    sView l.machine ρ M ι κ = (withInputs l.inputs ρ ι, M) := by
  have hc : withCarried l.machine M κ = M := by funext mp; simp [withCarried, Loop.machine]
  have hq : decideQ l.machine (withInputs l.inputs ρ ι) M = withInputs l.inputs ρ ι := by funext v; simp [decideQ, Loop.machine, lookup]
  simp only [sView, hc]
  show (decideFlags [] (decideQ l.machine (withInputs l.inputs ρ ι) M) M, M) = _
  rw [hq]; simp [decideFlags, flagSub, applyS_nil']

-- Where the guard holds, a step of the loop's machine is a turn of the loop, and leaves the maps.
theorem sNext_loop (l : Loop) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (hg : evalC (withInputs l.inputs ρ ι) M l.guard = true) :
    sNext l.machine ρ M ι κ = (applyS l.body (withInputs l.inputs ρ ι) M, M) := by
  simp only [sNext, sView_loop]
  refine Prod.ext ?_ ?_
  · funext i
    show applyS (l.body.map fun p => (p.1, E.ite l.guard p.2 (.var p.1))) (withInputs l.inputs ρ ι) M i = _
    simp only [applyS, assoc_guarded]
    cases assoc l.body i with
    | none => rfl
    | some e => simp [evalE, hg]
  · funext mp key; simp [everyMaps, Loop.machine, lookup, writeMaps]

/-- A loop halts: if the loop's machine reaches the guard failing from anywhere, along every run whose helpful requests
(here naming no input, so every run's) recur, then for params meeting the precondition no run of turns is infinite. -/
theorem loop_halts_of (l : Loop) (lv : Live) (hfrom : lv.from_ = trueC) (hto : lv.to = .not l.guard) (hhelps : ∀ h ∈ lv.helps, h.2 = [])
    (hguard : avoids l.inputs l.guard = true)
    (hlive : ∀ run : SRun l.machine, (∀ h ∈ lv.helps, ∀ n, ∃ m, n ≤ m ∧ ∀ p ∈ h.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) →
      ∀ n, evalC (run.st n).1 (run.st n).2 lv.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 lv.to = true)
    (maps : Nat → Nat → Nat) (ρ0 : Nat → Nat) (h0 : evalC ρ0 maps l.pre = true) :
    ¬ ∃ f : Nat → Nat → Nat, f 0 = applyS l.init ρ0 maps ∧ ∀ n, Turn l maps (f n) (f (n + 1)) := by
  rintro ⟨f, hf0, hf⟩
  let ι := fun n => Classical.choose (hf n)
  have hg : ∀ n, evalC (withInputs l.inputs (f n) (ι n)) maps l.guard = true := fun n => (Classical.choose_spec (hf n)).1
  have ha : ∀ n, evalC (withInputs l.inputs (f n) (ι n)) maps l.assume = true := fun n => (Classical.choose_spec (hf n)).2.1
  have hnext : ∀ n, f (n + 1) = applyS l.body (withInputs l.inputs (f n) (ι n)) maps := fun n => (Classical.choose_spec (hf n)).2.2
  let run : SRun l.machine := {
    st := fun n => (f n, maps)
    req := fun n => (ι n, fun _ _ => 0)
    start := by
      show SReach l.machine (f 0) maps
      rw [hf0]
      exact SReach.start (s := l.machine) ρ0 maps (fun p hp => by simp [Loop.machine] at hp) h0 (fun l' hl' => by simp [Loop.machine] at hl') (fun p hp => by simp [Loop.machine] at hp)
    allowed := fun n => by
      show evalC (sView l.machine (f n) maps (ι n) _).1 (sView l.machine (f n) maps (ι n) _).2 l.assume = true
      rw [sView_loop]; exact ha n
    next := fun n => by
      show (f (n + 1), maps) = sNext l.machine (f n) maps (ι n) _
      rw [sNext_loop l _ _ _ _ (hg n), hnext n] }
  obtain ⟨m, _, hm⟩ := hlive run (fun h hh n => ⟨n, Nat.le_refl n, by simp [hhelps h hh]⟩) 0 (by rw [hfrom]; simp [trueC, evalC, evalE])
  rw [hto] at hm
  have hgm := hg m
  rw [congrC (withInputs l.inputs (f m) (ι m)) (f m) maps l.guard (fun i hi => withInputs_other (avoids_occ hguard hi) _ _)] at hgm
  simp only [evalC, Bool.not_eq_true'] at hm
  show False
  have : evalC (run.st m).1 (run.st m).2 l.guard = true := hgm
  rw [this] at hm; exact Bool.noConfusion hm

end Kern

#print axioms Kern.sleads_sound
#print axioms Kern.sleads_wf_sound
#print axioms Kern.loop_halts_of

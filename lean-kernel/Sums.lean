import Ghost
/-!
Sums over a map's keys: kernel.ts's `sumMachine`, a machine whose state variables may each be the sum, over every key,
of a term read at that key (`M.sum()`: the cell itself; a count of the keys where a condition holds; a field's total
where another field says so). The sum is exact: a map starts at the same value everywhere, so the term must be 0 at the
start at every key, and each step changes it at finitely many keys (the cover), so it is 0 past some key in every
reachable state and its sum is the sum below there (`IsSum`).

A machine with sums (`SumMachine`) is a machine with sets (`SMachine`) plus its sums (`SumDecl`): the variable, the key
the term reads its maps at, the term, the cover keys (terms over the step's view: every key a step may change the term
at), a quantified flag and its witness. Lean builds the machine kernel.ts proves things about (`SumMachine.plain`):
- each sum a state variable from 0, after each step `(S + new) ∸ old`, where old and new are the term's values at the
  cover keys, each key counted once (`dTermE`), before and after the step;
- the assumption conjoined with two facts at every step: old ≤ S (`sumFact`), and a quantified flag that holds at every
  key k: the term at k and at the cover keys, each key once, is at most S (`sumBody`), so a goal reads `M[t] <= S`, and
  `M[t] + M[c] <= S` where t is not c, at the keys its proof names.
It checks kernel.ts's side conditions (`sumOk`: the term reads its maps only at its key and no variable, is 0 at the
start, reads no carried map; each map it reads written at one key has that key among the cover keys) and, for each map
the term reads that a step writes at every key, the cover goal (`sumCoverGoal`): at a key none of the cover keys is, the
write keeps the cell.

`sum_holds`: in every state the plain machine reaches, each sum variable is the sum of its term over the keys (IsSum),
and `sum_allowed`: there the plain machine allows exactly the requests the rule's own assumption allows, the facts being
true. So every claim proven of the plain machine (laws, step laws, k-induction, liveness) is a claim about the rule with
its sums exact; under weak fairness the helpful requests are proven allowed by the rule's own assumption
(`sumleads_wf_sound`, through Live.lean's `sleads_wf_soundA`).
-/
namespace Kern
open Classical

/-! Finite sums of naturals over the keys -/

def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo f n + f n

-- f is 0 from some key N on, and n is its sum below N.
def IsSum (f : Nat → Nat) (n : Nat) : Prop := ∃ N, (∀ k, N ≤ k → f k = 0) ∧ n = sumTo f N

-- The sum, where there is one.
noncomputable def sumOf (f : Nat → Nat) : Nat := if h : ∃ n, IsSum f n then Classical.choose h else 0

theorem sumTo_tail {f : Nat → Nat} {N : Nat} (h : ∀ k, N ≤ k → f k = 0) : ∀ d, sumTo f (N + d) = sumTo f N
  | 0 => rfl
  | d + 1 => by
    show sumTo f (N + d) + f (N + d) = sumTo f N
    rw [sumTo_tail h d, h (N + d) (Nat.le_add_right _ _)]; rfl

theorem sumTo_past {f : Nat → Nat} {N N' : Nat} (h : ∀ k, N ≤ k → f k = 0) (hle : N ≤ N') : sumTo f N' = sumTo f N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle; exact sumTo_tail h d

theorem isSum_unique {f : Nat → Nat} {a b : Nat} (ha : IsSum f a) (hb : IsSum f b) : a = b := by
  obtain ⟨N, hN, rfl⟩ := ha
  obtain ⟨N', hN', rfl⟩ := hb
  rw [← sumTo_past hN (Nat.le_max_left N N'), ← sumTo_past hN' (Nat.le_max_right N N')]

theorem sumOf_eq {f : Nat → Nat} {n : Nat} (h : IsSum f n) : sumOf f = n := by
  have hex : ∃ n, IsSum f n := ⟨n, h⟩
  simp only [sumOf, dif_pos hex]
  exact isSum_unique (Classical.choose_spec hex) h

theorem sumTo_const0 : ∀ N, sumTo (fun _ => 0) N = 0
  | 0 => rfl
  | N + 1 => by show sumTo (fun _ => 0) N + 0 = 0; rw [sumTo_const0 N]

theorem isSum_zero {f : Nat → Nat} (h : ∀ k, f k = 0) : IsSum f 0 :=
  ⟨0, fun k _ => h k, rfl⟩

-- f with key c set to 0.
def zap (f : Nat → Nat) (c : Nat) : Nat → Nat := fun k => if k = c then 0 else f k

theorem sumTo_zap (f : Nat → Nat) (c : Nat) : ∀ N, c < N → sumTo f N = f c + sumTo (zap f c) N
  | 0, h => absurd h (Nat.not_lt_zero _)
  | N + 1, h => by
    show sumTo f N + f N = f c + (sumTo (zap f c) N + zap f c N)
    by_cases hc : c = N
    · subst hc
      have hz : ∀ M, M ≤ c → sumTo (zap f c) M = sumTo f M := by
        intro M
        induction M with
        | zero => intro _; rfl
        | succ M ih =>
          intro hM
          show sumTo (zap f c) M + zap f c M = sumTo f M + f M
          rw [ih (by omega)]; simp only [zap, if_neg (show M ≠ c by omega)]
      rw [hz c (Nat.le_refl _)]; simp only [zap, ite_true]; omega
    · have hne : N ≠ c := fun h' => hc h'.symm
      rw [sumTo_zap f c N (by omega)]; simp only [zap, hne, ite_false]; omega

theorem zap_tail {f : Nat → Nat} {N : Nat} (h : ∀ k, N ≤ k → f k = 0) (c : Nat) : ∀ k, N ≤ k → zap f c k = 0 := by
  intro k hk; simp only [zap]; split
  · rfl
  · exact h k hk

-- A sum less one cell, and back.
theorem isSum_zap {f : Nat → Nat} {s : Nat} (h : IsSum f s) (c : Nat) : f c ≤ s ∧ IsSum (zap f c) (s - f c) := by
  obtain ⟨N, hN, rfl⟩ := h
  have hN' : ∀ k, max N (c + 1) ≤ k → f k = 0 := fun k hk => hN k (by omega)
  have e1 := sumTo_past hN (Nat.le_max_left N (c + 1))
  have e2 := sumTo_zap f c (max N (c + 1)) (by omega)
  refine ⟨by omega, max N (c + 1), zap_tail hN' c, by omega⟩

theorem isSum_unzap {f : Nat → Nat} {r : Nat} (c : Nat) (h : IsSum (zap f c) r) (hf : ∃ N, ∀ k, N ≤ k → f k = 0) : IsSum f (f c + r) := by
  obtain ⟨N, hN, rfl⟩ := h
  obtain ⟨N0, hN0⟩ := hf
  have hM : ∀ k, max (max N N0) (c + 1) ≤ k → f k = 0 := fun k hk => hN0 k (by omega)
  have e1 := sumTo_past hN (show N ≤ max (max N N0) (c + 1) by omega)
  have e2 := sumTo_zap f c (max (max N N0) (c + 1)) (by omega)
  exact ⟨max (max N N0) (c + 1), hM, by omega⟩

-- The sum of f at a list of keys, each key once (later copies read 0).
def dsum (f : Nat → Nat) : List Nat → Nat
  | [] => 0
  | c :: cs => f c + dsum (zap f c) cs

-- f with every listed key set to 0.
def zapAll (f : Nat → Nat) : List Nat → Nat → Nat
  | [] => f
  | c :: cs => zapAll (zap f c) cs

theorem zapAll_eq (f : Nat → Nat) : ∀ (cs : List Nat) (k : Nat), zapAll f cs k = if k ∈ cs then 0 else f k
  | [], k => by simp [zapAll]
  | c :: cs, k => by
    simp only [zapAll, zapAll_eq (zap f c) cs k, zap, List.mem_cons]
    by_cases h1 : k ∈ cs
    · simp [h1]
    · by_cases h2 : k = c <;> simp [h1, h2]

-- A sum is the listed keys' (each once) plus the rest's.
theorem isSum_split : ∀ (cs : List Nat) {f : Nat → Nat} {s : Nat}, IsSum f s → ∃ r, IsSum (zapAll f cs) r ∧ s = dsum f cs + r
  | [], _, s, h => ⟨s, h, by simp [dsum]⟩
  | c :: cs, f, s, h => by
    obtain ⟨hc, hz⟩ := isSum_zap h c
    obtain ⟨r, hr, hs⟩ := isSum_split cs hz
    exact ⟨r, hr, by simp only [dsum]; omega⟩

theorem isSum_tail {f : Nat → Nat} {s : Nat} (h : IsSum f s) : ∃ N, ∀ k, N ≤ k → f k = 0 := by
  obtain ⟨N, hN, _⟩ := h; exact ⟨N, hN⟩

theorem isSum_join : ∀ (cs : List Nat) {f : Nat → Nat} {r : Nat}, IsSum (zapAll f cs) r → (∃ N, ∀ k, N ≤ k → f k = 0) →
    IsSum f (dsum f cs + r)
  | [], _, r, h, _ => by simpa [dsum, zapAll] using h
  | c :: cs, f, r, h, hf => by
    have hzf : ∃ N, ∀ k, N ≤ k → zap f c k = 0 := by obtain ⟨N, hN⟩ := hf; exact ⟨N, zap_tail hN c⟩
    have h1 := isSum_join cs (f := zap f c) h hzf
    have h2 := isSum_unzap c h1 hf
    simp only [dsum]; rwa [Nat.add_assoc]

/-- The listed keys, each once, sum to at most the whole. -/
theorem dsum_le {f : Nat → Nat} {s : Nat} (h : IsSum f s) (cs : List Nat) : dsum f cs ≤ s := by
  obtain ⟨r, _, hs⟩ := isSum_split cs h; omega

/-- A function that agrees with f but at the listed keys sums to f's sum less the keys' old values plus their new. -/
theorem isSum_change {f f' : Nat → Nat} {s : Nat} (cs : List Nat) (h : IsSum f s) (hag : ∀ k, k ∉ cs → f' k = f k) :
    IsSum f' (s + dsum f' cs - dsum f cs) := by
  obtain ⟨r, hr, hs⟩ := isSum_split cs h
  have hz : zapAll f' cs = zapAll f cs := by
    funext k; rw [zapAll_eq, zapAll_eq]; split
    · rfl
    · rename_i hk; exact hag k hk
  obtain ⟨N, hN⟩ := isSum_tail h
  have hf' : ∃ N, ∀ k, N ≤ k → f' k = 0 := by
    refine ⟨max N (cs.foldr max 0 + 1), fun k hk => ?_⟩
    have hk' : k ∉ cs := by
      intro hm
      have : ∀ l : List Nat, ∀ x ∈ l, x ≤ l.foldr max 0 := by
        intro l; induction l with
        | nil => intro x hx; simp at hx
        | cons a as ih => intro x hx; rcases List.mem_cons.mp hx with rfl | hx
                          · simp only [List.foldr_cons]; omega
                          · have := ih x hx; simp only [List.foldr_cons]; omega
      have := this cs k hm; omega
    rw [hag k hk']; exact hN k (by omega)
  have := isSum_join cs (f := f') (by rw [hz]; exact hr) hf'
  have e : s + dsum f' cs - dsum f cs = dsum f' cs + r := by omega
  rw [e]; exact this

/-! The term read at a key -/

-- A term that reads its maps at the key variable k alone, and no variable but there.
mutual
def gOkE (k : Nat) : E → Bool
  | .var _ => false
  | .const _ => true
  | .add a b => gOkE k a && gOkE k b
  | .sub a b => gOkE k a && gOkE k b
  | .mul _ a => gOkE k a
  | .min a b => gOkE k a && gOkE k b
  | .max a b => gOkE k a && gOkE k b
  | .prod a b => gOkE k a && gOkE k b
  | .ite c t f => gOkC k c && gOkE k t && gOkE k f
  | .get _ key => match key with
    | .var i => i == k
    | _ => false
def gOkC (k : Nat) : C → Bool
  | .le a b => gOkE k a && gOkE k b
  | .lt a b => gOkE k a && gOkE k b
  | .eq a b => gOkE k a && gOkE k b
  | .and a b => gOkC k a && gOkC k b
  | .or a b => gOkC k a && gOkC k b
  | .not a => gOkC k a
end

-- The term's value at a key: each map read there.
def gAt (g : E) (M : Nat → Nat → Nat) (key : Nat) : Nat := evalE (fun _ => 0) (fun mp _ => M mp key) g

mutual
theorem g_sliceE (k : Nat) (ρ : Nat → Nat) (M : Nat → Nat → Nat) : (e : E) → gOkE k e = true →
    evalE ρ M e = evalE (fun _ => 0) (fun mp _ => M mp (ρ k)) e
  | .var _, h => by simp [gOkE] at h
  | .const _, _ => rfl
  | .add a b, h => by simp only [gOkE, Bool.and_eq_true] at h; simp only [evalE, g_sliceE k ρ M a h.1, g_sliceE k ρ M b h.2]
  | .sub a b, h => by simp only [gOkE, Bool.and_eq_true] at h; simp only [evalE, g_sliceE k ρ M a h.1, g_sliceE k ρ M b h.2]
  | .mul _ a, h => by simp only [gOkE] at h; simp only [evalE, g_sliceE k ρ M a h]
  | .min a b, h => by simp only [gOkE, Bool.and_eq_true] at h; simp only [evalE, g_sliceE k ρ M a h.1, g_sliceE k ρ M b h.2]
  | .max a b, h => by simp only [gOkE, Bool.and_eq_true] at h; simp only [evalE, g_sliceE k ρ M a h.1, g_sliceE k ρ M b h.2]
  | .prod a b, h => by simp only [gOkE, Bool.and_eq_true] at h; simp only [evalE, g_sliceE k ρ M a h.1, g_sliceE k ρ M b h.2]
  | .ite c t f, h => by
    simp only [gOkE, Bool.and_eq_true] at h
    simp only [evalE, g_sliceC k ρ M c h.1.1, g_sliceE k ρ M t h.1.2, g_sliceE k ρ M f h.2]
  | .get m key, h => by
    cases key <;> simp_all [gOkE, evalE]
theorem g_sliceC (k : Nat) (ρ : Nat → Nat) (M : Nat → Nat → Nat) : (c : C) → gOkC k c = true →
    evalC ρ M c = evalC (fun _ => 0) (fun mp _ => M mp (ρ k)) c
  | .le a b, h => by simp only [gOkC, Bool.and_eq_true] at h; simp only [evalC, g_sliceE k ρ M a h.1, g_sliceE k ρ M b h.2]
  | .lt a b, h => by simp only [gOkC, Bool.and_eq_true] at h; simp only [evalC, g_sliceE k ρ M a h.1, g_sliceE k ρ M b h.2]
  | .eq a b, h => by simp only [gOkC, Bool.and_eq_true] at h; simp only [evalC, g_sliceE k ρ M a h.1, g_sliceE k ρ M b h.2]
  | .and a b, h => by simp only [gOkC, Bool.and_eq_true] at h; simp only [evalC, g_sliceC k ρ M a h.1, g_sliceC k ρ M b h.2]
  | .or a b, h => by simp only [gOkC, Bool.and_eq_true] at h; simp only [evalC, g_sliceC k ρ M a h.1, g_sliceC k ρ M b h.2]
  | .not a, h => by simp only [gOkC] at h; simp only [evalC, g_sliceC k ρ M a h]
end

theorem gAt_eval {k : Nat} {g : E} (hg : gOkE k g = true) (ρ : Nat → Nat) (M : Nat → Nat → Nat) : evalE ρ M g = gAt g M (ρ k) :=
  g_sliceE k ρ M g hg

theorem gAt_congr {g : E} {M M' : Nat → Nat → Nat} {key : Nat} (h : ∀ mp, occME mp g = true → M mp key = M' mp key) :
    gAt g M key = gAt g M' key :=
  congrME _ _ _ g (fun mp hmp => funext fun _ => h mp hmp)

/-! Each key once, as a term -/

-- The sum of G at each listed key, a key equal to an earlier one read as 0.
def dTermE (G : E → E) : List E → E
  | [] => .const 0
  | c :: cs => .add (G c) (dTermE (fun t => .ite (.eq t c) (.const 0) (G t)) cs)

theorem dTermE_eval (W : Nat → Nat) (N : Nat → Nat → Nat) : ∀ (cs : List E) (G : E → E) (f : Nat → Nat),
    (∀ t, evalE W N (G t) = f (evalE W N t)) → evalE W N (dTermE G cs) = dsum f (cs.map (evalE W N))
  | [], _, _, _ => rfl
  | c :: cs, G, f, hG => by
    simp only [dTermE, evalE, List.map_cons, dsum, hG c]
    congr 1
    apply dTermE_eval W N cs _ (zap f (evalE W N c))
    intro t
    simp only [evalE, evalC, zap, hG t]
    by_cases h : evalE W N t = evalE W N c <;> simp [h]

/-! Machines with sums -/

structure SumDecl where
  v : Nat          -- the sum's state variable
  k : Nat          -- the key the term reads its maps at
  g : E            -- the term at each key
  cs : List E      -- the cover keys: every key a step may change the term at, over the step's view
  q : Nat          -- the quantified flag: at every key, the term there and at the cover keys is at most the sum
  w : Nat          -- its witness
  x : Nat          -- the key a cover goal reads

structure SumMachine where
  s : SMachine     -- the rule: its sums' variables are state it reads and no step sets
  sums : List SumDecl

-- The term at the key t, before the step.
def gHere (d : SumDecl) (t : E) : E := substE [(d.k, t)] d.g

-- A map read after a step, over the step's view: written at every key, its value at the key; written at one key, the
-- value there and the old cell elsewhere.
def postRd (s : SMachine) : Nat → E → E := fun mp key =>
  match lookup (fun w => w.1 == mp) s.every with
  | some w => substE [(w.2.1, key)] w.2.2
  | none => match lookup (fun w => w.1 == mp) s.f.m.writes with
    | some w => .ite (.eq key w.2.1) w.2.2 (.get mp key)
    | none => .get mp key

-- The term at the key t, after the step.
def gAfter (s : SMachine) (d : SumDecl) (t : E) : E := substRE [(d.k, t)] (postRd s) d.g

-- The sum after a step: the new values at the cover keys in, the old ones out.
def sumNext (s : SMachine) (d : SumDecl) : E := .sub (.add (.var d.v) (dTermE (gAfter s d) d.cs)) (dTermE (gHere d) d.cs)
-- The old values at the cover keys are at most the sum.
def sumFact (d : SumDecl) : C := .le (dTermE (gHere d) d.cs) (.var d.v)
-- At every key k: the term at k and at the cover keys, each key once, is at most the sum (a quantified flag's body, its
-- flags inlined: a quantified flag is decided before the plain flags).
def sumBody (s : SMachine) (d : SumDecl) : C := .le (dTermE (gHere d) (.var d.k :: d.cs.map (inlineE s.f.flags))) (.var d.v)
def sumsC : List SumDecl → C
  | [] => trueC
  | d :: ds => .and (.and (sumFact d) (.eq (.var d.q) (.const 1))) (sumsC ds)

/-- The machine kernel.ts proves things about: each sum a state variable from 0, moved by `sumNext`; the facts conjoined
to the assumption; each sum's quantified flag. -/
def SumMachine.plain (h : SumMachine) : SMachine :=
  { h.s with
    f := ⟨{ h.s.f.m with
      init := h.s.f.m.init ++ h.sums.map (fun d => (d.v, .const 0)),
      step := h.s.f.m.step ++ h.sums.map (fun d => (d.v, sumNext h.s d)),
      assume := .and h.s.f.m.assume (sumsC h.sums) }, h.s.f.flags⟩,
    qflags := h.s.qflags ++ h.sums.map (fun d => (d.q, [d.k], sumBody h.s d)),
    wits := h.s.wits ++ h.sums.map (fun d => (d.q, [d.w])) }

-- The writes at every key to a map the term reads.
def coverWs (s : SMachine) (d : SumDecl) : List (Nat × Nat × E) := s.every.filter (fun w => occME w.1 d.g)

-- At a key x none of the cover keys is, a step the rule allows keeps the map's cell.
def sumCoverGoal (s : SMachine) (d : SumDecl) (w : Nat × Nat × E) : List C :=
  [inlineC s.f.flags s.f.m.assume] ++ d.cs.map (fun c => .not (.eq (.var d.x) (inlineE s.f.flags c)))
    ++ [.not (.eq (substE [(w.2.1, .var d.x)] (inlineE s.f.flags w.2.2)) (.get w.1 (.var d.x)))]

-- The maps a term reads.
mutual
def mapsE : E → List Nat
  | .var _ => []
  | .const _ => []
  | .add a b => mapsE a ++ mapsE b
  | .sub a b => mapsE a ++ mapsE b
  | .mul _ a => mapsE a
  | .min a b => mapsE a ++ mapsE b
  | .max a b => mapsE a ++ mapsE b
  | .prod a b => mapsE a ++ mapsE b
  | .ite c t f => mapsC c ++ mapsE t ++ mapsE f
  | .get m key => m :: mapsE key
def mapsC : C → List Nat
  | .le a b => mapsE a ++ mapsE b
  | .lt a b => mapsE a ++ mapsE b
  | .eq a b => mapsE a ++ mapsE b
  | .and a b => mapsC a ++ mapsC b
  | .or a b => mapsC a ++ mapsC b
  | .not a => mapsC a
end

mutual
theorem mapsE_occ (mp : Nat) : (e : E) → occME mp e = true → mp ∈ mapsE e
  | .var _, h => by simp [occME] at h
  | .const _, h => by simp [occME] at h
  | .add a b, h => by simp only [occME, Bool.or_eq_true] at h; simp only [mapsE, List.mem_append]; exact h.imp (mapsE_occ mp a) (mapsE_occ mp b)
  | .sub a b, h => by simp only [occME, Bool.or_eq_true] at h; simp only [mapsE, List.mem_append]; exact h.imp (mapsE_occ mp a) (mapsE_occ mp b)
  | .mul _ a, h => by simp only [occME] at h; simp only [mapsE]; exact mapsE_occ mp a h
  | .min a b, h => by simp only [occME, Bool.or_eq_true] at h; simp only [mapsE, List.mem_append]; exact h.imp (mapsE_occ mp a) (mapsE_occ mp b)
  | .max a b, h => by simp only [occME, Bool.or_eq_true] at h; simp only [mapsE, List.mem_append]; exact h.imp (mapsE_occ mp a) (mapsE_occ mp b)
  | .prod a b, h => by simp only [occME, Bool.or_eq_true] at h; simp only [mapsE, List.mem_append]; exact h.imp (mapsE_occ mp a) (mapsE_occ mp b)
  | .ite c t f, h => by
    simp only [occME, Bool.or_eq_true] at h; simp only [mapsE, List.mem_append]
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (mapsC_occ mp c h))
    · exact Or.inl (Or.inr (mapsE_occ mp t h))
    · exact Or.inr (mapsE_occ mp f h)
  | .get m key, h => by
    simp only [occME, Bool.or_eq_true, beq_iff_eq] at h; simp only [mapsE, List.mem_cons]
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr (mapsE_occ mp key h)
theorem mapsC_occ (mp : Nat) : (c : C) → occMC mp c = true → mp ∈ mapsC c
  | .le a b, h => by simp only [occMC, Bool.or_eq_true] at h; simp only [mapsC, List.mem_append]; exact h.imp (mapsE_occ mp a) (mapsE_occ mp b)
  | .lt a b, h => by simp only [occMC, Bool.or_eq_true] at h; simp only [mapsC, List.mem_append]; exact h.imp (mapsE_occ mp a) (mapsE_occ mp b)
  | .eq a b, h => by simp only [occMC, Bool.or_eq_true] at h; simp only [mapsC, List.mem_append]; exact h.imp (mapsE_occ mp a) (mapsE_occ mp b)
  | .and a b, h => by simp only [occMC, Bool.or_eq_true] at h; simp only [mapsC, List.mem_append]; exact h.imp (mapsC_occ mp a) (mapsC_occ mp b)
  | .or a b, h => by simp only [occMC, Bool.or_eq_true] at h; simp only [mapsC, List.mem_append]; exact h.imp (mapsC_occ mp a) (mapsC_occ mp b)
  | .not a, h => by simp only [occMC] at h; simp only [mapsC]; exact mapsC_occ mp a h
end

def startVal (s : SMachine) (mp : Nat) : Nat := ((lookup (fun p => p.1 == mp) s.f.m.maps0).map (·.2)).getD 0

-- kernel.ts's conditions on each sum.
def sumOk1 (h : SumMachine) (d : SumDecl) : Bool :=
  let s := h.s
  gOkE d.k d.g
    -- 0 at the start at every key: each map it reads starts at a constant, and the term there is 0
    && (mapsE d.g).all (fun mp => (s.f.m.maps0.map (·.1)).contains mp)
    && evalE (fun _ => 0) (fun mp _ => startVal s mp) d.g == 0
    && avoidsMapsE s.carried d.g
    -- a map it reads written at one key: the key is a cover key
    && s.f.m.writes.all (fun w => !occME w.1 d.g || d.cs.any (fun c => beqE c w.2.1))
    -- written at every key: the key bound there is read by no flag, nor is the cover goal's key by anything it reads
    && (coverWs s d).all (fun w => s.f.flags.all (fun p => !occC w.2.1 p.2) && !(flagVars s.f.flags).contains w.2.1
        && avoidsE [d.x] (inlineE s.f.flags w.2.2) && d.x != w.2.1)
    && d.cs.all (fun c => avoidsE [d.k] c && avoidsE [d.x] (inlineE s.f.flags c))
    && avoids [d.x] (inlineC s.f.flags s.f.m.assume)
    -- the sum's variable: no input, flag, quantified flag or witness, set by no start or step of the rule, not the key
    && !(s.f.m.inputs ++ flagVars s.f.flags ++ h.plain.qVars ++ h.plain.wVars ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains d.v
    && d.v != d.k

def sumOk (h : SumMachine) : Bool := distinct (h.sums.map (·.v)) && h.sums.all (sumOk1 h)

-- Per sum, per write at every key to a map it reads: (table, tree) for its cover goal.
def checkSums (h : SumMachine) (covers : List (List (List VDef × Tree))) : Bool :=
  sumOk h && covers.length == h.sums.length
    && (h.sums.zip covers).all (fun p => (coverWs h.s p.1).length == p.2.length
      && ((coverWs h.s p.1).zip p.2).all (fun x => checkGoal ⟨x.2.1, sumCoverGoal h.s p.1 x.1⟩ x.2.2))

/-! What the checks give -/

theorem sumOk1_parts {h : SumMachine} {d : SumDecl} (hd : sumOk1 h d = true) :
    gOkE d.k d.g = true
    ∧ (∀ mp ∈ mapsE d.g, mp ∈ h.s.f.m.maps0.map (·.1))
    ∧ evalE (fun _ => 0) (fun mp _ => startVal h.s mp) d.g = 0
    ∧ avoidsMapsE h.s.carried d.g = true
    ∧ (∀ w ∈ h.s.f.m.writes, occME w.1 d.g = true → ∃ c ∈ d.cs, beqE c w.2.1 = true)
    ∧ (∀ w ∈ coverWs h.s d, (∀ p ∈ h.s.f.flags, occC w.2.1 p.2 = false) ∧ w.2.1 ∉ flagVars h.s.f.flags
        ∧ avoidsE [d.x] (inlineE h.s.f.flags w.2.2) = true ∧ d.x ≠ w.2.1)
    ∧ (∀ c ∈ d.cs, avoidsE [d.k] c = true ∧ avoidsE [d.x] (inlineE h.s.f.flags c) = true)
    ∧ avoids [d.x] (inlineC h.s.f.flags h.s.f.m.assume) = true
    ∧ d.v ∉ h.s.f.m.inputs ++ flagVars h.s.f.flags ++ h.plain.qVars ++ h.plain.wVars ++ h.s.f.m.init.map (·.1) ++ h.s.f.m.step.map (·.1)
    ∧ d.v ≠ d.k := by
  simp only [sumOk1, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne, ne_eq,
    Bool.or_eq_true, List.contains_iff_mem] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hg, hm⟩, h0⟩, hc⟩, hw⟩, hev⟩, hcs⟩, ha⟩, hv⟩, hvk⟩ := hd
  refine ⟨hg, hm, h0, hc, fun w hw' ho => ?_, fun w hw' => ?_, hcs, ha, ?_, hvk⟩
  · rcases hw w hw' with h1 | h1
    · simp [h1] at ho
    · exact h1
  · obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hev w hw'
    exact ⟨fun p hp => by simpa using h1 p hp, by simpa using h2, h3, h4⟩
  · intro hm'; simp_all

theorem sumOk_parts {h : SumMachine} (hok : sumOk h = true) : distinct (h.sums.map (·.v)) = true ∧ ∀ d ∈ h.sums, sumOk1 h d = true := by
  simp only [sumOk, Bool.and_eq_true, List.all_eq_true] at hok; exact hok

theorem checkSums_parts {h : SumMachine} {covers : List (List (List VDef × Tree))} (hc : checkSums h covers = true) :
    sumOk h = true ∧ ∀ d ∈ h.sums, ∀ w ∈ coverWs h.s d, ∃ t : List VDef × Tree, checkGoal ⟨t.1, sumCoverGoal h.s d w⟩ t.2 = true := by
  simp only [checkSums, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨hok, hlen⟩, hall⟩ := hc
  refine ⟨hok, fun d hd w hw => ?_⟩
  obtain ⟨cl, hcl⟩ := zip_cover h.sums covers hlen.symm d hd
  obtain ⟨hl2, hall2⟩ := hall _ hcl
  obtain ⟨t, ht⟩ := zip_cover (coverWs h.s d) cl hl2 w hw
  exact ⟨t, hall2 _ ht⟩

/-! Lookups -/

theorem assoc_after {σ τ : List (Nat × E)} {i : Nat} (h : i ∉ σ.map (·.1)) : assoc (σ ++ τ) i = assoc τ i := by
  have hσ : lookup (fun p => p.1 == i) σ = none :=
    lookup_none (fun p hp => by simp only [beq_eq_false_iff_ne]; intro he; exact h (by rw [← he]; exact List.mem_map_of_mem hp))
  simp only [assoc, lookup_append, hσ]

theorem assoc_sums (F : SumDecl → E) {ds : List SumDecl} (hd : distinct (ds.map (·.v)) = true) {d : SumDecl} (hm : d ∈ ds) :
    assoc (ds.map (fun d => (d.v, F d))) d.v = some (F d) := by
  have hd' : distinct ((ds.map (fun d => (d.v, F d))).map (·.1)) = true := by rw [List.map_map]; exact hd
  have := lookup_unique_fst hd' (List.mem_map_of_mem (f := fun d => (d.v, F d)) hm)
  simp only [assoc, this, Option.map_some]

theorem upd_at (ρ : Nat → Nat) (i v : Nat) : upd ρ i v i = v := by simp [upd]

/-! The terms' values -/

section terms
variable (h : SumMachine) (d : SumDecl)

theorem gHere_eval (hg : gOkE d.k d.g = true) (W : Nat → Nat) (N : Nat → Nat → Nat) (t : E) :
    evalE W N (gHere d t) = gAt d.g N (evalE W N t) := by
  rw [gHere, subst_evalE, applyS_single, gAt_eval hg, upd_at]

theorem postRd_eval (D : Nat → Nat) (N : Nat → Nat → Nat) (mp : Nat) (key : E) :
    evalE D N (postRd h.s mp key) = everyMaps h.s D N mp (evalE D N key) := by
  simp only [postRd, everyMaps]
  cases hl : lookup (fun w => w.1 == mp) h.s.every with
  | some w => simp only [subst_evalE, applyS_single]
  | none =>
    simp only [writeMaps]
    cases hl2 : lookup (fun w => w.1 == mp) h.s.f.m.writes with
    | some w => simp only [evalE, evalC]; by_cases hk : evalE D N key = evalE D N w.2.1 <;> simp [hk]
    | none => rfl

theorem gAfter_eval (hg : gOkE d.k d.g = true) (W : Nat → Nat) (N : Nat → Nat → Nat) (t : E) :
    evalE W N (gAfter h.s d t) = gAt d.g (everyMaps h.s W N) (evalE W N t) := by
  rw [gAfter, substR_evalE_on [(d.k, t)] (postRd h.s) W N (everyMaps h.s W N) [] (fun m key _ => postRd_eval h W N m key) d.g (by simp [avoidsMapsE]),
    applyS_single, gAt_eval hg, upd_at]

-- The term reads no carried map: read through the maps a request carries, it is the term over the state's maps.
theorem gAt_carried (hc : avoidsMapsE h.s.carried d.g = true) (M κ : Nat → Nat → Nat) :
    gAt d.g (withCarried h.s M κ) = gAt d.g M := by
  funext key
  apply gAt_congr; intro mp hmp
  simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using avoidsMapsE_occ hc hmp)]

end terms

/-! The sums are exact -/

section exact
variable (h : SumMachine)

-- The view reads a sum's variable as the state does.
theorem view_v {d : SumDecl} (hv : d.v ∉ h.s.f.m.inputs ++ flagVars h.s.f.flags ++ h.plain.qVars ++ h.plain.wVars ++ h.s.f.m.init.map (·.1) ++ h.s.f.m.step.map (·.1))
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) : (sView h.plain ρ M ι κ).1 d.v = ρ d.v := by
  simp only [List.mem_append, not_or] at hv
  show decideFlags h.s.f.flags (decideQ h.plain (withInputs h.s.f.m.inputs ρ ι) (withCarried h.s M κ)) (withCarried h.s M κ) d.v = ρ d.v
  rw [decide_other hv.1.1.1.1.2, decideQ_other hv.1.1.1.2, withInputs_other hv.1.1.1.1.1]

/-- One step the rule's assumption allows keeps every sum exact. -/
theorem sum_step (hc : checkSums h covers = true) {ρ : Nat → Nat} {M : Nat → Nat → Nat}
    (hsum : ∀ d ∈ h.sums, IsSum (gAt d.g M) (ρ d.v)) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (ha : evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.s.f.m.assume = true) :
    ∀ d ∈ h.sums, IsSum (gAt d.g (sNext h.plain ρ M ι κ).2) ((sNext h.plain ρ M ι κ).1 d.v) := by
  obtain ⟨hok, hcov⟩ := checkSums_parts hc
  obtain ⟨hdist, hall⟩ := sumOk_parts hok
  intro d hd
  obtain ⟨hg, _, _, hcar, hwr, hev, hcs, hax, hv, _⟩ := sumOk1_parts (hall d hd)
  let X := decideQ h.plain (withInputs h.s.f.m.inputs ρ ι) (withCarried h.s M κ)
  let N := withCarried h.s M κ
  let V := decideFlags h.s.f.flags X N
  have hV : (sView h.plain ρ M ι κ).1 = V := rfl
  have hN : (sView h.plain ρ M ι κ).2 = N := rfl
  let M' := everyMaps h.s V N
  have hM' : (sNext h.plain ρ M ι κ).2 = M' := rfl
  let cs' := d.cs.map (evalE V N)
  -- The term moves only at the cover keys.
  have hag : ∀ key, key ∉ cs' → gAt d.g M' key = gAt d.g M key := by
    intro key hkey
    apply gAt_congr; intro mp hmp
    have hNM : N mp key = M mp key := by
      simp only [N, withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using avoidsMapsE_occ hcar hmp)]
    simp only [M', everyMaps]
    cases hl : lookup (fun w => w.1 == mp) h.s.every with
    | some w =>
      obtain ⟨hwm, hw1⟩ := lookup_some hl
      simp only [beq_iff_eq] at hw1
      have hwc : w ∈ coverWs h.s d := List.mem_filter.mpr ⟨hwm, by rw [hw1]; exact hmp⟩
      obtain ⟨t, ht⟩ := hcov d hd w hwc
      obtain ⟨hfl, hbf, hxv, hxb⟩ := hev w hwc
      show evalE (upd V w.2.1 key) N w.2.2 = M mp key
      apply Decidable.byContradiction; intro hne
      apply sound ⟨t.1, sumCoverGoal h.s d w⟩ t.2 ht (upd X d.x key) N
      intro c hcm
      simp only [sumCoverGoal, List.mem_append, List.mem_singleton, List.mem_map] at hcm
      rcases hcm with (rfl | ⟨c0, hc0, rfl⟩) | rfl
      · rw [congrC _ X N _ (fun i hi => by simp only [upd]; rw [if_neg (fun he => avoids_occ hax hi (by simp [he]))]), inline_evalC]
        exact ha
      · have hc0' := (hcs c0 hc0).2
        simp only [evalC, evalE, upd_at, Bool.not_eq_true', decide_eq_false_iff_not]
        rw [congrE _ X N _ (fun i hi => by simp only [upd]; rw [if_neg (fun he => avoidsE_occ hc0' hi (by simp [he]))]), inline_evalE]
        intro he; exact hkey (List.mem_map.mpr ⟨c0, hc0, he.symm⟩)
      · simp only [evalC, evalE, Bool.not_eq_true', decide_eq_false_iff_not, upd_at]
        rw [subst_evalE, applyS_single]
        simp only [evalE, upd_at]
        rw [congrE _ (upd X w.2.1 key) N _ (fun i hi => by
          simp only [upd]; by_cases hib : i = w.2.1
          · simp [hib]
          · rw [if_neg hib, if_neg hib, if_neg (fun he => avoidsE_occ hxv hi (by simp [he]))]), inline_evalE,
          decide_upd hbf (fun p hp => hfl p hp)]
        intro he; rw [he] at hne; exact hne (by rw [hw1]; exact hNM)
    | none =>
      simp only [writeMaps]
      cases hl2 : lookup (fun w => w.1 == mp) h.s.f.m.writes with
      | some w =>
        obtain ⟨hwm, hw1⟩ := lookup_some hl2
        simp only [beq_iff_eq] at hw1
        obtain ⟨c, hcm, hce⟩ := hwr w hwm (by rw [hw1]; exact hmp)
        have hin : evalE V N w.2.1 ∈ cs' := List.mem_map.mpr ⟨c, hcm, by rw [beqE_eq hce]⟩
        have hne : key ≠ evalE V N w.2.1 := fun he => hkey (by rw [he]; exact hin)
        simp only [if_neg hne]; exact hNM
      | none => exact hNM
  have hold : evalE V N (dTermE (gHere d) d.cs) = dsum (gAt d.g M) cs' := by
    rw [dTermE_eval V N d.cs (gHere d) (gAt d.g N) (fun t => gHere_eval d hg V N t), gAt_carried h d hcar]
  have hnew : evalE V N (dTermE (gAfter h.s d) d.cs) = dsum (gAt d.g M') cs' :=
    dTermE_eval V N d.cs (gAfter h.s d) (gAt d.g M') (fun t => gAfter_eval h d hg V N t)
  have hval : (sNext h.plain ρ M ι κ).1 d.v = ρ d.v + dsum (gAt d.g M') cs' - dsum (gAt d.g M) cs' := by
    show applyS (h.s.f.m.step ++ h.sums.map (fun d => (d.v, sumNext h.s d))) V N d.v = _
    simp only [applyS]
    rw [assoc_after (fun hm => hv (by simp [hm])), assoc_sums (sumNext h.s) hdist hd]
    simp only [sumNext, evalE, hold, hnew]
    rw [← hV, view_v h hv ρ M ι κ]
  rw [hval, hM']
  exact isSum_change cs' (hsum d hd) hag

-- At the start every term is 0 at every key, and every sum 0.
theorem sum_start (hc : checkSums h covers = true) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hM : StartMaps h.plain.f.m M) :
    ∀ d ∈ h.sums, IsSum (gAt d.g M) (applyS h.plain.f.m.init ρ M d.v) := by
  obtain ⟨hok, _⟩ := checkSums_parts hc
  obtain ⟨hdist, hall⟩ := sumOk_parts hok
  intro d hd
  obtain ⟨_, hm, h0, _, _, _, _, _, hv, _⟩ := sumOk1_parts (hall d hd)
  have hval : applyS h.plain.f.m.init ρ M d.v = 0 := by
    show applyS (h.s.f.m.init ++ h.sums.map (fun d => (d.v, E.const 0))) ρ M d.v = 0
    simp only [applyS]
    rw [assoc_after (fun hm' => hv (by simp [hm'])), assoc_sums (fun _ => E.const 0) hdist hd]
    rfl
  rw [hval]
  refine isSum_zero (fun key => ?_)
  rw [gAt]
  refine Eq.trans (congrME _ _ _ d.g (fun mp hmp => ?_)) h0
  funext _
  obtain ⟨p, hp, hpe⟩ := List.mem_map.mp (hm mp (mapsE_occ mp d.g hmp))
  cases hl : lookup (fun p => p.1 == mp) h.s.f.m.maps0 with
  | none => exact absurd (lookup_none_all hl p hp) (by simp [hpe])
  | some p0 =>
    obtain ⟨hp0, hp0e⟩ := lookup_some hl
    simp only [beq_iff_eq] at hp0e
    simp only [startVal, hl, Option.map_some, Option.getD_some]
    rw [← hp0e]; exact hM p0 hp0 key

-- Each sum's quantified flag, in the plain machine.
theorem q_mem {d : SumDecl} (hd : d ∈ h.sums) : (d.q, [d.k], sumBody h.s d) ∈ h.plain.qflags :=
  List.mem_append_right _ (List.mem_map.mpr ⟨d, hd, rfl⟩)

/-- Where every sum is exact, the facts the plain machine assumes hold of every request, in its view. -/
theorem sum_facts (hc : checkSums h covers = true) (hs : sOk h.plain = true) {ρ : Nat → Nat} {M : Nat → Nat → Nat}
    (hsum : ∀ d ∈ h.sums, IsSum (gAt d.g M) (ρ d.v)) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 (sumsC h.sums) = true := by
  obtain ⟨hok, _⟩ := checkSums_parts hc
  obtain ⟨_, hall⟩ := sumOk_parts hok
  obtain ⟨_, hqd, _, _, hdx, _, _⟩ := sOk_parts h.plain hs
  let N := withCarried h.s M κ
  let Wi := withInputs h.s.f.m.inputs ρ ι
  have one : ∀ d ∈ h.sums, evalC (sView h.plain ρ M ι κ).1 N (.and (sumFact d) (.eq (.var d.q) (.const 1))) = true := by
    intro d hd
    obtain ⟨hg, _, _, hcar, _, _, _, _, hv, hvk⟩ := sumOk1_parts (hall d hd)
    have hvi : d.v ∉ h.s.f.m.inputs := fun hm => hv (by simp [hm])
    simp only [evalC, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · show decide (evalE _ N (dTermE (gHere d) d.cs) ≤ (sView h.plain ρ M ι κ).1 d.v) = true
      apply decide_eq_true
      rw [dTermE_eval _ N d.cs (gHere d) (gAt d.g N) (fun t => gHere_eval d hg _ N t), gAt_carried h d hcar, view_v h hv ρ M ι κ]
      exact dsum_le (hsum d hd) _
    · have hqv : d.q ∈ h.plain.qVars := List.mem_map_of_mem (q_mem h hd)
      have hqf : d.q ∉ flagVars h.s.f.flags := fun hm =>
        (distinct_append hdx).2.2 d.q (by simp only [SMachine.extVars, List.mem_append]; exact Or.inl (Or.inr hqv)) hm
      show decideFlags h.s.f.flags (decideQ h.plain Wi N) N d.q = 1
      rw [decide_other hqf, decideQ_of, lookup_unique hqd (q_mem h hd)]
      simp only
      rw [if_pos]
      intro key
      rw [← evalC_iff]
      show decide (evalE _ N (dTermE (gHere d) (.var d.k :: d.cs.map (inlineE h.s.f.flags))) ≤ atKeys Wi [d.k] key d.v) = true
      apply decide_eq_true
      rw [dTermE_eval _ N _ (gHere d) (gAt d.g N) (fun t => gHere_eval d hg _ N t), gAt_carried h d hcar,
        atKeys_out (show d.v ∉ [d.k] by simpa using hvk)]
      show _ ≤ withInputs h.s.f.m.inputs ρ ι d.v
      rw [withInputs_other hvi]
      exact dsum_le (hsum d hd) _
  have all : ∀ ds : List SumDecl, (∀ d ∈ ds, d ∈ h.sums) → evalC (sView h.plain ρ M ι κ).1 N (sumsC ds) = true := by
    intro ds
    induction ds with
    | nil => intro _; rfl
    | cons d ds ih =>
      intro hm
      have h1 := one d (hm d List.mem_cons_self)
      have h2 := ih (fun d' hd' => hm d' (List.mem_cons_of_mem _ hd'))
      show (evalC _ N (.and (sumFact d) (.eq (.var d.q) (.const 1))) && evalC _ N (sumsC ds)) = true
      rw [h1, h2]; rfl
  exact all h.sums (fun _ hd => hd)

/-- The plain machine allows exactly the requests the rule's own assumption allows, wherever the sums are exact. -/
theorem sum_assume (hc : checkSums h covers = true) (hs : sOk h.plain = true) {ρ : Nat → Nat} {M : Nat → Nat → Nat}
    (hsum : ∀ d ∈ h.sums, IsSum (gAt d.g M) (ρ d.v)) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.plain.f.m.assume
      = evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.s.f.m.assume := by
  show (evalC _ _ h.s.f.m.assume && evalC _ _ (sumsC h.sums)) = _
  rw [sum_facts h hc hs hsum ι κ, Bool.and_true]

/-- **The sums are exact**: in every state the plain machine reaches, each sum's variable is the sum, over every key,
of its term there. -/
theorem sum_holds (hc : checkSums h covers = true) :
    ∀ ρ M, SReach h.plain ρ M → ∀ d ∈ h.sums, IsSum (gAt d.g M) (ρ d.v) := by
  intro ρ M hr
  induction hr with
  | start ρ M hM _ _ _ => exact sum_start h hc ρ M hM
  | step ρ M ι κ _ ha ih =>
    have ha0 : evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.s.f.m.assume = true := by
      have : evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 (.and h.s.f.m.assume (sumsC h.sums)) = true := ha
      simp only [evalC, Bool.and_eq_true] at this; exact this.1
    exact sum_step h hc ih ι κ ha0

/-- **The plain machine is the rule**: in every state it reaches, it allows a request exactly when the rule's own
assumption does. -/
theorem sum_allowed (hc : checkSums h covers = true) (hs : sOk h.plain = true) :
    ∀ ρ M, SReach h.plain ρ M → ∀ ι κ, evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.plain.f.m.assume
      = evalC (sView h.plain ρ M ι κ).1 (sView h.plain ρ M ι κ).2 h.s.f.m.assume :=
  fun ρ M hr ι κ => sum_assume h hc hs (sum_holds h hc ρ M hr) ι κ

end exact

/-! A rule that reads none of its sums -/

-- The sums' variables and quantified flags, as ghosts of the rule (Ghost.lean's check: new names nothing of it reads).
def SumMachine.ghosts (h : SumMachine) : SGhosted := ⟨h.s, h.sums.flatMap (fun d => [(d.v, .const 0, .var d.v), (d.q, .const 0, .var d.q)])⟩

theorem ghosts_vars (h : SumMachine) {d : SumDecl} (hd : d ∈ h.sums) : d.v ∈ h.ghosts.vars ∧ d.q ∈ h.ghosts.vars := by
  simp only [SGhosted.vars, SumMachine.ghosts, List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨⟨_, ⟨d, hd, Or.inl rfl⟩, rfl⟩, ⟨_, ⟨d, hd, Or.inr rfl⟩, rfl⟩⟩

section project
variable (h : SumMachine) (hg : sghostOk h.ghosts = true)
include hg

-- One step from states that agree outside the sums' names: the plain machine reads the rule's assumption as the rule
-- does, and moves to a state that agrees outside them, with the same maps.
theorem sum_ghost_step {ρ ρg : Nat → Nat} (hag : Agree h.ghosts.vars ρg ρ) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    evalC (sView h.plain ρg M ι κ).1 (sView h.plain ρg M ι κ).2 h.s.f.m.assume = evalC (sView h.s ρ M ι κ).1 (sView h.s ρ M ι κ).2 h.s.f.m.assume
      ∧ Agree h.ghosts.vars (sNext h.plain ρg M ι κ).1 (sNext h.s ρ M ι κ).1
      ∧ (sNext h.plain ρg M ι κ).2 = (sNext h.s ρ M ι κ).2 := by
  obtain ⟨_, hn, _, ha, hf, hs, _, hw, he, hq, _⟩ := sghostOk_parts h.ghosts hg
  have hX : Agree h.ghosts.vars (withInputs h.s.f.m.inputs ρg ι) (withInputs h.s.f.m.inputs ρ ι) := fun i hi => by
    simp only [withInputs]; split
    · rfl
    · exact hag i hi
  have hQ : Agree h.ghosts.vars (decideQ h.plain (withInputs h.s.f.m.inputs ρg ι) (withCarried h.s M κ))
      (decideQ h.s (withInputs h.s.f.m.inputs ρ ι) (withCarried h.s M κ)) := by
    intro v hv
    rw [decideQ_of, decideQ_of]
    show (match lookup (fun q => q.1 == v) (h.s.qflags ++ h.sums.map (fun d => (d.q, [d.k], sumBody h.s d))) with
      | some q => if ∀ k, holdsC (atKeys (withInputs h.s.f.m.inputs ρg ι) q.2.1 k) (withCarried h.s M κ) q.2.2 then 1 else 0
      | none => withInputs h.s.f.m.inputs ρg ι v) = _
    rw [lookup_append]
    cases hl : lookup (fun q => q.1 == v) h.s.qflags with
    | some q => exact ite_all_congr (fun i hi _ => hX i (avoids_occ (hq q (lookup_some hl).1) hi)) (fun _ _ => rfl)
    | none =>
      have hl2 : lookup (fun q => q.1 == v) (h.sums.map (fun d => (d.q, [d.k], sumBody h.s d))) = none := lookup_none (fun x hx => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
        simp only [beq_eq_false_iff_ne]; intro he'; exact hv (by rw [← he']; exact (ghosts_vars h hd).2))
      simp only [hl2]; exact hX v hv
  have hD : Agree h.ghosts.vars (decideFlags h.s.f.flags (decideQ h.plain (withInputs h.s.f.m.inputs ρg ι) (withCarried h.s M κ)) (withCarried h.s M κ))
      (decideFlags h.s.f.flags (decideQ h.s (withInputs h.s.f.m.inputs ρ ι) (withCarried h.s M κ)) (withCarried h.s M κ)) :=
    decide_agree_on hf (withCarried h.s M κ) hQ
  refine ⟨?_, fun i hi => ?_, ?_⟩
  · show evalC (decideFlags h.s.f.flags (decideQ h.plain (withInputs h.s.f.m.inputs ρg ι) (withCarried h.s M κ)) (withCarried h.s M κ)) _ h.s.f.m.assume = _
    exact congrC _ _ _ _ (fun i hi => hD i (avoids_occ ha hi))
  · have hvi : i ∉ h.sums.map (fun d => d.v) := fun hm => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm; exact hi (ghosts_vars h hd).1
    show applyS (h.s.f.m.step ++ h.sums.map (fun d => (d.v, sumNext h.s d))) (decideFlags h.s.f.flags (decideQ h.plain (withInputs h.s.f.m.inputs ρg ι) (withCarried h.s M κ)) (withCarried h.s M κ)) (withCarried h.s M κ) i = _
    rw [applyS_append_other (by simpa using hvi)]
    simp only [sNext, sView, applyS]
    cases hst : assoc h.s.f.m.step i with
    | none => exact hD i hi
    | some e =>
      have hm : (i, e) ∈ h.s.f.m.step := by
        simp only [assoc, Option.map_eq_some_iff] at hst
        obtain ⟨q, hq', rfl⟩ := hst
        obtain ⟨hqm, hqv⟩ := lookup_some hq'
        simp only [beq_iff_eq] at hqv
        rw [← hqv]; exact hqm
      exact congrE _ _ _ e (fun j hj => hD j (avoidsE_occ (hs (i, e) hm) hj))
  · funext mp key
    show everyMaps h.s (decideFlags h.s.f.flags (decideQ h.plain (withInputs h.s.f.m.inputs ρg ι) (withCarried h.s M κ)) (withCarried h.s M κ)) (withCarried h.s M κ) mp key
      = everyMaps h.s (decideFlags h.s.f.flags (decideQ h.s (withInputs h.s.f.m.inputs ρ ι) (withCarried h.s M κ)) (withCarried h.s M κ)) (withCarried h.s M κ) mp key
    simp only [everyMaps]
    cases hl : lookup (fun w => w.1 == mp) h.s.every with
    | some w => exact congrE _ _ _ w.2.2 (fun j hj => upd_agree hD w.2.1 key j (avoidsE_occ (he w (lookup_some hl).1) hj))
    | none =>
      simp only [writeMaps]
      cases hl2 : lookup (fun w => w.1 == mp) h.s.f.m.writes with
      | none => rfl
      | some w =>
        obtain ⟨h1, h2⟩ := hw w (lookup_some hl2).1
        simp only [congrE _ _ _ w.2.1 (fun j hj => hD j (avoidsE_occ h1 hj)), congrE _ _ _ w.2.2 (fun j hj => hD j (avoidsE_occ h2 hj))]

/-- **A rule that reads none of its sums**: every state the rule reaches is, outside the sums' names, one the plain
machine reaches, so a law proven of the plain machine that reads none of them is a law of the rule. -/
theorem sum_project (hc : checkSums h covers = true) (hs : sOk h.plain = true) :
    ∀ {ρ M}, SReach h.s ρ M → ∃ ρg, SReach h.plain ρg M ∧ Agree h.ghosts.vars ρg ρ := by
  intro ρ M hr
  induction hr with
  | start ρ M hM h0 hfa hpf =>
    refine ⟨applyS h.plain.f.m.init ρ M, SReach.start ρ M hM h0 hfa hpf, fun i hi => ?_⟩
    have hvi : i ∉ h.sums.map (fun d => d.v) := fun hm => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm; exact hi (ghosts_vars h hd).1
    show applyS (h.s.f.m.init ++ h.sums.map (fun d => (d.v, E.const 0))) ρ M i = applyS h.s.f.m.init ρ M i
    exact applyS_append_other (by simpa using hvi) ρ M
  | step ρ M ι κ _ ha ih =>
    obtain ⟨ρg, hrg, hag⟩ := ih
    obtain ⟨hA, hS, hW⟩ := sum_ghost_step h hg hag M ι κ
    refine ⟨_, ?_, hS⟩
    rw [← hW]
    refine SReach.step ρg M ι κ hrg ?_
    rw [sum_allowed h hc hs ρg M hrg ι κ, hA]; exact ha

/-- The laws of the plain machine that read no sum's name hold in every state the rule reaches. -/
theorem sum_project_laws (ps : List SEntry) (hl : checkSMachine h.plain ps = true) (hc : checkSums h covers = true) :
    ∀ ρ M, SReach h.s ρ M → ∀ e ∈ ps, avoids h.ghosts.vars e.law.holds = true → e.Holds ρ M := by
  intro ρ M hr e he hav
  obtain ⟨ρg, hrg, hag⟩ := sum_project h hg hc (sOk_of hl) hr
  exact sentry_transfer (V := h.ghosts.vars) (MS := []) hav (by simp [avoidsMaps]) (fun i hi => (hag i hi).symm) (fun _ _ => rfl)
    (smachine_sound h.plain ps hl ρg M hrg e he)

end project

/-! Claims about the rule with its sums -/

/-- The laws proven of the plain machine hold in every state it reaches, where every sum is exact. -/
theorem sum_laws (h : SumMachine) (ps : List SEntry) (covers : List (List (List VDef × Tree)))
    (hl : checkSMachine h.plain ps = true) (hc : checkSums h covers = true) :
    ∀ ρ M, SReach h.plain ρ M → (∀ d ∈ h.sums, IsSum (gAt d.g M) (ρ d.v)) ∧ ∀ e ∈ ps, e.Holds ρ M :=
  fun ρ M hr => ⟨sum_holds h hc ρ M hr, smachine_sound h.plain ps hl ρ M hr⟩

-- A run of the rule with its sums: each request one the rule's own assumption allows.
structure SumRun (h : SumMachine) where
  st : Nat → (Nat → Nat) × (Nat → Nat → Nat)
  req : Nat → SRequest
  start : SReach h.plain (st 0).1 (st 0).2
  allowed : ∀ n, evalC (sView h.plain (st n).1 (st n).2 (req n).1 (req n).2).1 (sView h.plain (st n).1 (st n).2 (req n).1 (req n).2).2 h.s.f.m.assume = true
  next : ∀ n, st (n + 1) = sNext h.plain (st n).1 (st n).2 (req n).1 (req n).2

-- It is a run of the plain machine: there the facts hold, so the plain machine allows each of its requests.
def SumRun.plain {h : SumMachine} {covers : List (List (List VDef × Tree))} (hc : checkSums h covers = true) (hs : sOk h.plain = true)
    (run : SumRun h) : SRun h.plain :=
  have reach : ∀ n, SReach h.plain (run.st n).1 (run.st n).2 := fun n => by
    induction n with
    | zero => exact run.start
    | succ n ih =>
      rw [run.next n]
      exact SReach.step _ _ _ _ ih (by rw [sum_allowed h hc hs _ _ ih]; exact run.allowed n)
  ⟨run.st, run.req, run.start, fun n => by rw [sum_allowed h hc hs _ _ (reach n)]; exact run.allowed n, run.next⟩

/-- Liveness of the rule with its sums, along every run that takes each helpful request infinitely often. -/
theorem sumleads_sound (h : SumMachine) (covers : List (List (List VDef × Tree))) (ps : List SEntry) (l : Live) (sp cp : SProof) (hp : List SProof)
    (hc : checkSums h covers = true) (hl : checkSMachine h.plain ps = true) (hok : sliveOk h.plain l = true)
    (hs : checkSKStep h.plain ps (sliveStep l l.pend (liveStayC l) sp) = true) (hcv : checkSKStep h.plain ps (sliveStep l l.pend (liveCoverC l) cp) = true)
    (hh : sliveHelpsOk h.plain ps l hp = true) (run : SumRun h)
    (fair : ∀ x ∈ l.helps, ∀ n, ∃ m, n ≤ m ∧ ∀ p ∈ x.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 l.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 l.to = true :=
  sleads_sound h.plain ps l sp cp hp hl hok hs hcv hh (run.plain hc (sOk_of hl)) fair

/-- Liveness of the rule with its sums under weak fairness of its own assumption: each helpful request is proven allowed
by the rule's assumption in its region (the facts the plain machine assumes besides hold there). -/
theorem sumleads_wf_sound (h : SumMachine) (covers : List (List (List VDef × Tree))) (ps : List SEntry) (l : Live) (sp cp : SProof)
    (hp : List SProof) (ap : List (List (Nat × E) × SProof × List E))
    (hc : checkSums h covers = true) (hl : checkSMachine h.plain ps = true) (hok : sliveOk h.plain l = true)
    (hs : checkSKStep h.plain ps (sliveStep l l.pend (liveStayC l) sp) = true) (hcv : checkSKStep h.plain ps (sliveStep l l.pend (liveCoverC l) cp) = true)
    (hh : sliveHelpsOk h.plain ps l hp = true) (ha : sliveAllowsOkA h.plain ps l ap h.s.f.m.assume = true) (run : SumRun h)
    (fair : ∀ x ∈ l.helps, ∀ n, (∀ m, n ≤ m → ∃ ι κ, (∀ p ∈ x.2, ι p.1 = evalE (run.st m).1 (run.st m).2 p.2)
        ∧ evalC (sView h.plain (run.st m).1 (run.st m).2 ι κ).1 (sView h.plain (run.st m).1 (run.st m).2 ι κ).2 h.s.f.m.assume = true) →
      ∃ m, n ≤ m ∧ ∀ p ∈ x.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 l.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 l.to = true :=
  sleads_wf_soundA h.plain ps l sp cp hp ap h.s.f.m.assume hl hok hs hcv hh ha (run.plain hc (sOk_of hl)) fair

/-- The same under strong fairness (Live.lean's `sleads_sf_soundA`). -/
theorem sumleads_sf_sound (h : SumMachine) (covers : List (List (List VDef × Tree))) (ps : List SEntry) (l : Live) (lv : List Nat) (sp cp : SProof)
    (hp : List SProof) (ap : List (List (Nat × E) × SProof × List E))
    (hc : checkSums h covers = true) (hl : checkSMachine h.plain ps = true) (hok : sliveOk h.plain l = true)
    (hs : checkSKStep h.plain ps (sliveStep l l.pend (liveStaySC l) sp) = true) (hcv : checkSKStep h.plain ps (sliveStep l l.pend (liveCoverC l) cp) = true)
    (hh : sliveHelpsOkS h.plain ps l lv hp = true) (ha : sliveAllowsOkA h.plain ps l ap h.s.f.m.assume = true) (run : SumRun h)
    (fair : ∀ x ∈ l.helps, (∀ n, ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 x.1 = true ∧ ∃ ι κ, (∀ p ∈ x.2, ι p.1 = evalE (run.st m).1 (run.st m).2 p.2)
        ∧ evalC (sView h.plain (run.st m).1 (run.st m).2 ι κ).1 (sView h.plain (run.st m).1 (run.st m).2 ι κ).2 h.s.f.m.assume = true) →
      ∀ n, ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 x.1 = true ∧ ∀ p ∈ x.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 l.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 l.to = true :=
  sleads_sf_soundA h.plain ps l lv sp cp hp ap h.s.f.m.assume hl hok hs hcv hh ha (run.plain hc (sOk_of hl)) fair

end Kern

#print axioms Kern.isSum_change
#print axioms Kern.dsum_le
#print axioms Kern.sum_holds
#print axioms Kern.sum_allowed
#print axioms Kern.sum_laws
#print axioms Kern.sumleads_sound
#print axioms Kern.sumleads_wf_sound
#print axioms Kern.sumleads_sf_sound
#print axioms Kern.sum_project_laws

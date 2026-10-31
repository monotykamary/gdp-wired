import Sets
import Count

/-!
CountMachine: counts in a machine's laws and steps, proven sound. Lean 4.34.0, core only; on top of `Sets.lean` (the
machines with sets) and `Count.lean` (the counted goal and `counted_sound`), neither changed.

**What a machine may count.** A count declaration (`CDecl`) names a map `mp` whose cell at x is the number Σ_{k < below}
body(k), with the declaration's variable `j` at x and its key variable `key` at k (a 0/1 body is a set's size: the
votes for x, the members of a request's set). The map is one the request carries (`mp ∈ s.carried`), so the machine
itself is an `SMachine` as it was: its runs (`CReach`) are `SReach`'s with each request's count maps at their counts,
read at the request's view (its inputs set, over the state's maps and the maps it carries). A guard (the assumption)
reads a count there: `2·|Q| > size` for a request's set Q. A law reads a count of the state: a declaration whose bound
and body read no request (`stateOnly`: no input, quantified flag, witness, flag variable or carried map), whose value
at a state is `withCnt` (each count map at its count there): `2·|{n < size: vote[n] = x + 1}| > size` for a decided x.

**The goals** are `Sets.lean`'s, with the counts read twice in a step. Before the step a law and the guard read each
count map as the request carries it (its count at the view, which for a state-only count is its count at the state).
After the step, the law is read with each count map renamed to its `post` name (`frameRd`), and the goal declares the
post name a count too, its bound and body read across the step (`afterDecl`: substituted by the step, as the law is,
with `j` and `key` kept). The start goal reads the law at the start the same way. A goal is a `CGoalM`: hypotheses
and the count maps it declares (`GHolds`: each map at its count, at every key).

**The certificate** (`CCert`, checked by `checkMC`) names the goal's hypotheses it uses (each one Lean builds), the
cells it reads (`reads`: a fresh variable for a count map's cell at a key term), and Count.lean's instances and tree.
`checkMC` turns it into Count.lean's counted goal: the named hypotheses, each read variable equal to its cell, and a
count per read (its declaration with `j` at the key term), and asks `checkCounted`. `mc_sound`: an accepted goal's
hypotheses hold at no naturals and maps where each declared map is its count.

**Soundness.** `cmachine_sound`: every entry of an accepted proof holds in every reachable state, its laws reading
each count map as the state's count (`withCnt`). The proof is `Sets.lean`'s `smachine_sound` with the counted goals in
place of `checkIn`: the goals are refuted where the count maps before the step are what the request carried (`CReach`),
and the post names are the counts of the state after it.
-/

namespace Kern
open Classical

/-! Counts of a map, and the counted goals over them -/

-- A count map: `mp` at x is Σ_{k < below} body(k), read with j at x and key at k; `post` the name a step's goal reads
-- it by after the step.
structure CDecl where
  mp : Nat
  post : Nat
  j : Nat
  key : Nat
  below : E
  body : E

-- The count at x.
def cntOf (d : CDecl) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (x : Nat) : Nat :=
  sumBelow (fun k => evalE (upd (upd ρ d.j x) d.key k) M d.body) (evalE (upd ρ d.j x) M d.below)

-- Each declared map is its count, at every key.
def GHolds (ds : List CDecl) (ρ : Nat → Nat) (M : Nat → Nat → Nat) : Prop := ∀ d ∈ ds, ∀ x, M d.mp x = cntOf d ρ M x

-- A certificate for a counted goal: the goal's hypotheses it names, the cells it reads (a variable, a count map, a key
-- term), Count.lean's instances, the table and the tree.
structure CCert where
  hyps : List C
  reads : List (Nat × Nat × E)
  insts : List CInst
  tab : List VDef
  tree : Tree

-- A read cell as Count.lean's count: its variable, the declaration with j at the key term.
def toCount (ds : List CDecl) (r : Nat × Nat × E) : Option Count :=
  (lookup (fun d => d.mp == r.2.1) ds).map fun d => ⟨r.1, d.key, substE [(d.j, r.2.2)] d.below, substE [(d.j, r.2.2)] d.body⟩

def toCounts (ds : List CDecl) : List (Nat × Nat × E) → Option (List Count)
  | [] => some []
  | r :: rs => match toCount ds r with
    | none => none
    | some c => (toCounts ds rs).map (c :: ·)

def readHyp (r : Nat × Nat × E) : C := .eq (.var r.1) (.get r.2.1 r.2.2)

-- A read's variable is fresh: no named hypothesis, declaration or key term reads it, and it is no declaration's j or key.
def readFresh (hyps : List C) (ds : List CDecl) (rs : List (Nat × Nat × E)) (v : Nat) : Bool :=
  hyps.all (fun h => !occC v h) && ds.all (fun d => !occE v d.below && !occE v d.body && d.j != v && d.key != v)
    && rs.all (fun r => !occE v r.2.2)

-- The reads: distinct fresh variables, each key term reading no declaration's key.
def readsOk (hyps : List C) (ds : List CDecl) (rs : List (Nat × Nat × E)) : Bool :=
  cDistinct (rs.map (·.1)) && rs.all (fun r => readFresh hyps ds rs r.1 && ds.all (fun d => !occE d.key r.2.2))

-- The check: the named hypotheses are the goal's, each declaration's j and key differ, the reads are fresh, and
-- Count.lean accepts the counted goal they make.
def checkMC (hyps : List C) (ds : List CDecl) (k : CCert) : Bool :=
  namedIn hyps k.hyps hyps && ds.all (fun d => d.j != d.key) && readsOk k.hyps ds k.reads
    && match toCounts ds k.reads with
      | some cs => checkCounted ⟨k.hyps ++ k.reads.map readHyp, cs⟩ k.insts k.tab k.tree
      | none => false

/-! The counted goal's soundness -/

theorem toCounts_mem {ds : List CDecl} : ∀ {rs : List (Nat × Nat × E)} {cs : List Count}, toCounts ds rs = some cs →
    ∀ c ∈ cs, ∃ r ∈ rs, toCount ds r = some c
  | [], cs, h => by simp only [toCounts, Option.some.injEq] at h; subst h; simp
  | r :: rs, cs, h => by
    cases e1 : toCount ds r with
    | none => simp [toCounts, e1] at h
    | some c1 =>
      cases e2 : toCounts ds rs with
      | none => simp [toCounts, e1, e2] at h
      | some cs' =>
        simp [toCounts, e1, e2] at h
        subst h
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨r, List.mem_cons_self, e1⟩
        · obtain ⟨r', hr', h'⟩ := toCounts_mem e2 c hc
          exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩

-- Each read's variable set to its cell's value, the rest of the environment kept.
def setReads (ρ : Nat → Nat) (M : Nat → Nat → Nat) (rs : List (Nat × Nat × E)) : Nat → Nat :=
  setWits ρ (rs.map fun r => (r.1, M r.2.1 (evalE ρ M r.2.2)))

theorem mc_sound (hyps : List C) (ds : List CDecl) (k : CCert) (hck : checkMC hyps ds k = true)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hd : GHolds ds ρ M) : ¬ ∀ h ∈ hyps, evalC ρ M h = true := by
  intro hH
  simp only [checkMC, Bool.and_eq_true] at hck
  obtain ⟨⟨⟨hnamed, hjk⟩, hrok⟩, hcc⟩ := hck
  cases hcs : toCounts ds k.reads with
  | none => simp [hcs] at hcc
  | some cs =>
  simp only [hcs] at hcc
  simp only [readsOk, Bool.and_eq_true, List.all_eq_true] at hrok
  obtain ⟨hdist, hrs⟩ := hrok
  have hmap : (k.reads.map fun r => (r.1, M r.2.1 (evalE ρ M r.2.2))).map (·.1) = k.reads.map (·.1) := by
    induction k.reads <;> simp_all
  -- ρ' : ρ with each read's variable at its cell's value.
  let ρ' := setReads ρ M k.reads
  have hother : ∀ i, (∀ r ∈ k.reads, r.1 ≠ i) → ρ' i = ρ i := fun i hi => setWits_other (by
    rw [hmap]; intro hm; obtain ⟨r, hr, he⟩ := List.mem_map.mp hm; exact hi r hr he)
  have hat : ∀ r ∈ k.reads, ρ' r.1 = M r.2.1 (evalE ρ M r.2.2) := by
    intro r hr
    have h := setWits_at (ρ := ρ) (ws := k.reads.map fun r => (r.1, M r.2.1 (evalE ρ M r.2.2))) (by rw [hmap]; exact hdist)
      (p := (r.1, M r.2.1 (evalE ρ M r.2.2))) (List.mem_map.mpr ⟨r, hr, rfl⟩)
    exact h
  have hfr : ∀ r ∈ k.reads, readFresh k.hyps ds k.reads r.1 = true := fun r hr => (hrs r hr).1
  have hfr' : ∀ r ∈ k.reads, (∀ h ∈ k.hyps, occC r.1 h = false) ∧ (∀ d ∈ ds, occE r.1 d.below = false ∧ occE r.1 d.body = false ∧ d.j ≠ r.1 ∧ d.key ≠ r.1)
      ∧ (∀ r' ∈ k.reads, occE r.1 r'.2.2 = false) := by
    intro r hr
    have := hfr r hr
    simp only [readFresh, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at this
    exact ⟨this.1.1, fun d hd => ⟨(this.1.2 d hd).1.1.1, (this.1.2 d hd).1.1.2, (this.1.2 d hd).1.2, (this.1.2 d hd).2⟩, this.2⟩
  -- A term no read's variable occurs in reads alike at ρ' and ρ.
  have hcong : ∀ e : E, (∀ r ∈ k.reads, occE r.1 e = false) → evalE ρ' M e = evalE ρ M e := fun e he =>
    congrE ρ' ρ M e (fun i hi => hother i (fun r hr hri => by have := he r hr; rw [hri] at this; simp [this] at hi))
  refine counted_sound _ _ _ _ hcc ρ' M ?_ ?_
  · -- every count is its sum at ρ'
    intro c hc
    obtain ⟨r, hr, hrc⟩ := toCounts_mem hcs c hc
    simp only [toCount, Option.map_eq_some_iff] at hrc
    obtain ⟨d, hdl, rfl⟩ := hrc
    obtain ⟨hdm, hdq⟩ := lookup_some hdl
    simp only [beq_iff_eq] at hdq
    have hjk' : d.j ≠ d.key := by have := List.all_eq_true.mp hjk d hdm; simpa using this
    have hkey : occE d.key r.2.2 = false := by have := (hrs r hr).2 d hdm; simpa using this
    have ⟨hfb, hfd, _⟩ := hfr' r hr
    simp only [Count.Holds]
    rw [hat r hr, ← hdq, hd d hdm]
    have ht : evalE ρ' M r.2.2 = evalE ρ M r.2.2 := hcong r.2.2 (fun r' hr' => (hfr' r' hr').2.2 r hr)
    simp only [cntOf]
    -- the bound and the body, with j at the key term, read at ρ' as the declaration's at ρ with j at its value
    have hB : evalE ρ' M (substE [(d.j, r.2.2)] d.below) = evalE (upd ρ d.j (evalE ρ M r.2.2)) M d.below := by
      rw [subst_evalE, applyS_one, ht]
      exact congrE _ _ M d.below (fun i hi => by
        simp only [upd]; split
        · rfl
        · exact hother i (fun r' hr' hri => by have := ((hfr' r' hr').2.1 d hdm).1; rw [hri] at this; simp [this] at hi))
    rw [hB]
    refine sumBelow_congr _ (fun kk _ => ?_)
    rw [subst_evalE, applyS_one]
    have hk' : evalE (upd ρ' d.key kk) M r.2.2 = evalE ρ M r.2.2 := by
      rw [← ht]; exact congrE _ _ M r.2.2 (fun i hi => by
        simp only [upd]; split
        · rename_i h; subst h; simp [hkey] at hi
        · rfl)
    rw [hk']
    exact congrE _ _ M d.body (fun i hi => by
      simp only [upd]
      by_cases h1 : i = d.j
      · simp [h1, hjk']
      · by_cases h2 : i = d.key
        · simp [h1, h2, Ne.symm hjk']
        · simp only [h1, h2, ite_false]
          exact (hother i (fun r' hr' hri => by have := ((hfr' r' hr').2.1 d hdm).2.1; rw [hri] at this; simp [this] at hi)).symm)
  · intro h hm
    rcases List.mem_append.mp hm with hm | hm
    · rw [congrC ρ' ρ M h (fun i hi => hother i (fun r hr hri => by
        have := (hfr' r hr).1 h hm; rw [hri] at this; simp [this] at hi))]
      exact hH h (namedIn_sound hyps k.hyps hyps (fun _ hx => hx) hnamed h hm)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
      have h1 := hat r hr
      have h2 := hcong r.2.2 (fun r' hr' => (hfr' r' hr').2.2 r hr)
      simp only [readHyp, evalC, evalE, decide_eq_true_eq, h1, h2]

/-! Counts in a machine -/

-- The maps with each count map at its count at ρ, M.
def withCnt (ds : List CDecl) (ρ : Nat → Nat) (M : Nat → Nat → Nat) : Nat → Nat → Nat := fun mp =>
  match lookup (fun d => d.mp == mp) ds with
  | some d => cntOf d ρ M
  | none => M mp

-- The runs: `SReach`'s, each request carrying each count map at its count at the request's view.
inductive CReach (s : SMachine) (ds : List CDecl) : (Nat → Nat) → (Nat → Nat → Nat) → Prop
  | start (ρ : Nat → Nat) (M : Nat → Nat → Nat) : StartMaps s.f.m M → evalC ρ M s.f.m.pre = true → (∀ l ∈ s.facts, l.Holds ρ M) →
      s.PFacts ρ M → CReach s ds (applyS s.f.m.init ρ M) M
  | step (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) : CReach s ds ρ M →
      GHolds ds (withInputs s.f.m.inputs ρ ι) (withCarried s M κ) →
      evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume = true → CReach s ds (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2

theorem creach_sreach {s : SMachine} {ds : List CDecl} : ∀ {ρ M}, CReach s ds ρ M → SReach s ρ M := by
  intro ρ M h
  induction h with
  | start ρ M hM h0 hf hp => exact .start ρ M hM h0 hf hp
  | step ρ M ι κ _ _ ha ih => exact .step ρ M ι κ ih ha

-- A count of the state alone: its bound and body read no request (input, quantified flag, witness), no flag and no
-- carried map. A law reads only these.
def stateOnly (s : SMachine) (d : CDecl) : Bool :=
  avoidsE (s.extVars ++ flagVars s.f.flags) d.below && avoidsE (s.extVars ++ flagVars s.f.flags) d.body
    && avoidsMapsE s.carried d.below && avoidsMapsE s.carried d.body

def cMaps (ds : List CDecl) : List Nat := ds.map (·.mp)
def cPosts (ds : List CDecl) : List Nat := ds.map (·.post)
def cren (ds : List CDecl) : List (Nat × Nat) := ds.map fun d => (d.mp, d.post)
def stateMaps (s : SMachine) (ds : List CDecl) : List Nat := (ds.filter (stateOnly s)).map (·.mp)

-- A law with each count map read by its post name.
def renLaw (ds : List CDecl) (l : MLaw) : MLaw := ⟨substRC [] (frameRd (cren ds) getRd) l.holds, l.key⟩

-- A count declared after σ, rd: its bound and body read across them, j and key kept.
def afterDecl (σ : List (Nat × E)) (rd : Nat → E → E) (d : CDecl) : CDecl :=
  ⟨d.post, d.post, d.j, d.key, substRE ((d.j, .var d.j) :: (d.key, .var d.key) :: σ) rd d.below,
    substRE ((d.j, .var d.j) :: (d.key, .var d.key) :: σ) rd d.body⟩

-- The goals: Sets.lean's, the law proven read with its count maps renamed; the counts the goals declare: at the start,
-- each state count after the start; at a step, each count as the request carries it, and each state count after it.
def cStartGoal (s : SMachine) (ds : List CDecl) (e : SEntry) : List C := sStartGoal s { e with law := renLaw ds e.law }
def cStartDecls (s : SMachine) (ds : List CDecl) : List CDecl := (ds.filter (stateOnly s)).map (afterDecl s.f.m.init (rdStart s.f.m))
def cStepGoal (s : SMachine) (ds : List CDecl) (ps : List SEntry) (e : SEntry) : List C := sStepGoal s ps { e with law := renLaw ds e.law }
def cStepDecls (s : SMachine) (ds : List CDecl) : List CDecl :=
  ds ++ (ds.filter (stateOnly s)).map (afterDecl (stepSub s.f (frameSub [] []) (frameRd [] getRd)) (stepRdS s (frameSub [] []) (frameRd [] getRd)))

-- A variable no part of the machine reads or binds (as a skolem is).
def mFresh (s : SMachine) (x : Nat) : Bool :=
  skFresh s x && s.f.m.init.all (fun p => !occE x p.2) && !(s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains x

-- What the machine's own parts may not read: the post names (nothing reads them but the goals), which are none of its
-- maps.
def cApart (s : SMachine) (ds : List CDecl) : Bool :=
  s.f.flags.all (fun p => avoidsMaps (cPosts ds) p.2) && s.qflags.all (fun q => avoidsMaps (cPosts ds) q.2.2)
    && s.f.m.step.all (fun p => avoidsMapsE (cPosts ds) p.2)
    && s.f.m.writes.all (fun w => avoidsMapsE (cPosts ds) w.2.1 && avoidsMapsE (cPosts ds) w.2.2)
    && s.every.all (fun w => avoidsMapsE (cPosts ds) w.2.2)
    && s.f.m.init.all (fun p => avoidsMapsE (cPosts ds) p.2) && avoidsMaps (cPosts ds) s.f.m.assume
    && s.facts.all (fun l => avoidsMaps (cPosts ds) l.holds) && s.pfacts.all (fun f => avoidsMaps (cPosts ds) f.1.holds)
    && (cPosts ds).all (fun mp => !s.carried.contains mp && !(s.f.m.maps0.map (·.1)).contains mp
        && !(s.every.map (·.1)).contains mp && !(s.f.m.writes.map (·.1)).contains mp)

-- Each declaration: its map carried, its j and key fresh and distinct, its bound and body reading no quantified flag,
-- witness, count map or post name, and no entry's skolem or further key (nor having them as j or key).
def cDeclOk (s : SMachine) (ds : List CDecl) (ps : List SEntry) (d : CDecl) : Bool :=
  s.carried.contains d.mp && d.j != d.key && mFresh s d.j && mFresh s d.key && !occE d.key d.below
    && avoidsE (s.qVars ++ s.wVars) d.below && avoidsE (s.qVars ++ s.wVars) d.body
    && avoidsMapsE (cMaps ds ++ cPosts ds) d.below && avoidsMapsE (cMaps ds ++ cPosts ds) d.body
    && ps.all (fun e => (e.sk :: e.keys2).all (fun g => !occE g d.below && !occE g d.body && g != d.j && g != d.key))

-- The entries' own conditions (Sets.lean's checkSMachine's), a law reading count maps of the state only, and no post name.
def cEntryOk (s : SMachine) (ds : List CDecl) (ps : List SEntry) (e : SEntry) : Bool :=
  avoids (s.extVars ++ flagVars s.f.flags) e.law.holds && avoidsMaps (s.carried.filter (fun mp => !(stateMaps s ds).contains mp) ++ cPosts ds) e.law.holds
    && !(s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains e.sk
    && ps.all (fun e' => !occC e.sk e'.law.holds) && !occC e.sk s.f.m.pre && s.f.m.init.all (fun p => !occE e.sk p.2)
    && skFresh s e.sk && key2Ok s ps e

structure CEntry where
  e : SEntry      -- the law, its skolem and further keys, and where its goals assume the laws and facts (its certs unused)
  start : CCert
  step : CCert

def checkCMachine (s : SMachine) (ds : List CDecl) (ps : List CEntry) : Bool :=
  sOk s && avoids (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)) s.f.m.pre && !readsC s.f.m.pre
    && sTermsOk s (flagVars s.f.flags) && factsOk s
    && cDistinct (cMaps ds ++ cPosts ds) && cApart s ds && ds.all (cDeclOk s ds (ps.map (·.e)))
    && ps.all (fun ce => cEntryOk s ds (ps.map (·.e)) ce.e
      && checkMC (cStartGoal s ds ce.e) (cStartDecls s ds) ce.start
      && checkMC (cStepGoal s ds (ps.map (·.e)) ce.e) (cStepDecls s ds) ce.step)

/-! Reading a law with its count maps renamed -/

-- The maps a renamed term reads: a renamed map's cells are its new name's.
def renM (mr : List (Nat × Nat)) (N : Nat → Nat → Nat) : Nat → Nat → Nat := fun mp =>
  match lookup (fun p => p.1 == mp) mr with
  | some p => N p.2
  | none => N mp

theorem ren_evalC (mr : List (Nat × Nat)) (X : Nat → Nat) (N : Nat → Nat → Nat) (c : C) :
    evalC X N (substRC [] (frameRd mr getRd) c) = evalC X (renM mr N) c := by
  rw [substR_evalC [] (frameRd mr getRd) X N (renM mr N) (fun m k => by
    simp only [frameRd, renM]; cases h : lookup (fun p => p.1 == m) mr <;> simp [getRd, evalE]), applyS_nil']

mutual
theorem occ_renE (mr : List (Nat × Nat)) (i : Nat) : (e : E) → occE i (substRE [] (frameRd mr getRd) e) = occE i e
  | .var j => by simp [substRE, assoc, lookup, occE]
  | .const _ => by simp [substRE, occE]
  | .add a b => by simp [substRE, occE, occ_renE mr i a, occ_renE mr i b]
  | .sub a b => by simp [substRE, occE, occ_renE mr i a, occ_renE mr i b]
  | .mul _ a => by simp [substRE, occE, occ_renE mr i a]
  | .min a b => by simp [substRE, occE, occ_renE mr i a, occ_renE mr i b]
  | .max a b => by simp [substRE, occE, occ_renE mr i a, occ_renE mr i b]
  | .prod a b => by simp [substRE, occE, occ_renE mr i a, occ_renE mr i b]
  | .ite c t f => by simp [substRE, occE, occ_renC mr i c, occ_renE mr i t, occ_renE mr i f]
  | .get m key => by
    simp only [substRE, frameRd]
    split <;> simp [getRd, occE, occ_renE mr i key]
theorem occ_renC (mr : List (Nat × Nat)) (i : Nat) : (c : C) → occC i (substRC [] (frameRd mr getRd) c) = occC i c
  | .le a b => by simp [substRC, occC, occ_renE mr i a, occ_renE mr i b]
  | .lt a b => by simp [substRC, occC, occ_renE mr i a, occ_renE mr i b]
  | .eq a b => by simp [substRC, occC, occ_renE mr i a, occ_renE mr i b]
  | .and a b => by simp [substRC, occC, occ_renC mr i a, occ_renC mr i b]
  | .or a b => by simp [substRC, occC, occ_renC mr i a, occ_renC mr i b]
  | .not a => by simp [substRC, occC, occ_renC mr i a]
end

-- A renamed law holds where the law holds with its maps renamed.
theorem renLaw_holds (ds : List CDecl) (l : MLaw) (X : Nat → Nat) (N : Nat → Nat → Nat) :
    (renLaw ds l).Holds X N ↔ l.Holds X (renM (cren ds) N) := by
  unfold MLaw.Holds
  simp only [renLaw]
  split <;> simp [ren_evalC]

/-! Counts read where a fresh variable is set -/

theorem cntOf_upd {d : CDecl} {g : Nat} (hb : occE g d.below = false) (hd : occE g d.body = false) (X : Nat → Nat) (N : Nat → Nat → Nat) (w x : Nat) :
    cntOf d (upd X g w) N x = cntOf d X N x := by
  simp only [cntOf]
  have hB : evalE (upd (upd X g w) d.j x) N d.below = evalE (upd X d.j x) N d.below :=
    congrE _ _ N d.below (fun i hi => by
      have hig : i ≠ g := fun h => by rw [h, hb] at hi; cases hi
      simp only [upd]; split <;> simp_all)
  rw [hB]
  exact sumBelow_congr _ (fun k _ => congrE _ _ N d.body (fun i hi => by
      have hig : i ≠ g := fun h => by rw [h, hd] at hi; cases hi
      simp only [upd]; split
      · rfl
      · split
        · rfl
        · simp [hig]))

theorem withCnt_upd {ds : List CDecl} {g : Nat} (h : ∀ d ∈ ds, occE g d.below = false ∧ occE g d.body = false) (X : Nat → Nat) (N : Nat → Nat → Nat) (w : Nat) :
    withCnt ds (upd X g w) N = withCnt ds X N := by
  funext mp
  simp only [withCnt]
  split
  · rename_i d hd
    have := h d (lookup_some hd).1
    funext x; exact cntOf_upd this.1 this.2 X N w x
  · rfl

theorem withCnt_at {ds : List CDecl} (hd : cDistinct (cMaps ds) = true) {d : CDecl} (hm : d ∈ ds) (X : Nat → Nat) (N : Nat → Nat → Nat) :
    withCnt ds X N d.mp = cntOf d X N := by
  simp only [withCnt]
  have : lookup (fun d' => d'.mp == d.mp) ds = some d := by
    induction ds with
    | nil => simp at hm
    | cons a as ih =>
      simp only [cMaps, List.map_cons] at hd
      obtain ⟨hna, hd'⟩ := cDistinct_cons hd
      rcases List.mem_cons.mp hm with rfl | hm'
      · simp [lookup]
      · have hne : (a.mp == d.mp) = false := by
          simp only [beq_eq_false_iff_ne]; intro he; exact hna (by rw [he]; exact List.mem_map_of_mem hm')
        simp only [lookup, hne, Bool.false_eq_true, ite_false]
        exact ih hd' hm'
  rw [this]

theorem withCnt_other {ds : List CDecl} {mp : Nat} (h : mp ∉ cMaps ds) (X : Nat → Nat) (N : Nat → Nat → Nat) : withCnt ds X N mp = N mp := by
  simp only [withCnt]
  rw [lookup_none (fun d hd => by simp only [beq_eq_false_iff_ne]; intro he; exact h (by rw [← he]; exact List.mem_map_of_mem hd))]

/-! A request's view, read where a fresh variable is set -/

theorem witnessKeys_congr {X X' : Nat → Nat} {N N' : Nat → Nat → Nat} {q : Nat × List Nat × C}
    (h : ∀ k, holdsC (atKeys X q.2.1 k) N q.2.2 ↔ holdsC (atKeys X' q.2.1 k) N' q.2.2) : witnessKeys X N q = witnessKeys X' N' q := by
  have hp : (fun k => ¬holdsC (atKeys X q.2.1 k) N q.2.2) = (fun k => ¬holdsC (atKeys X' q.2.1 k) N' q.2.2) := funext fun k => by rw [h k]
  unfold witnessKeys
  split
  · rename_i h1
    have h2 : ∃ k, ¬holdsC (atKeys X' q.2.1 k) N' q.2.2 := by obtain ⟨k, hk⟩ := h1; exact ⟨k, by rwa [← h k]⟩
    rw [dif_pos h2]
    have : ∀ (p p' : (Nat → Nat) → Prop) (e : p = p') (h1 : ∃ k, p k) (h2 : ∃ k, p' k), Classical.choose h1 = Classical.choose h2 := by
      intro p p' e h1 h2; subst e; rfl
    exact this _ _ hp h1 h2
  · rename_i h1
    have h2 : ¬∃ k, ¬holdsC (atKeys X' q.2.1 k) N' q.2.2 := fun ⟨k, hk⟩ => h1 ⟨k, by rwa [h k]⟩
    rw [dif_neg h2]

theorem sReq_upd {s : SMachine} {g : Nat} (hi : g ∉ s.f.m.inputs) (hq : g ∉ s.qVars) (hb : ∀ q ∈ s.qflags, occC g q.2.2 = false)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) (w : Nat) :
    sReq s (upd ρ g w) M ι κ = sReq s ρ M ι κ := by
  funext v
  simp only [sReq]
  split
  · rfl
  · split
    · rename_i q hql
      have hvq : v ≠ g := fun h => hq (by
        have := lookup_some hql; simp only [beq_iff_eq] at this; rw [← h, ← this.2]; exact List.mem_map_of_mem this.1)
      rw [withInputs_upd hi, decideQ_upd hq hb]
      simp only [upd, hvq, ite_false]
    · split
      · split
        · rename_i q hq'
          split
          · apply congrFun
            apply witnessKeys_congr
            intro k
            rw [withInputs_upd hi]
            simp only [← evalC_iff]
            rw [congrC _ (atKeys (withInputs s.f.m.inputs ρ ι) q.2.1 k) _ q.2.2 (fun i hi' => by
              have hig : i ≠ g := fun h => by rw [h, hb q (lookup_some hq').1] at hi'; cases hi'
              simp only [atKeys]; split
              · rfl
              · simp [upd, hig])]
          · rfl
        · rfl
      · rfl

/-! The check, taken apart -/

theorem cDistinct_append {a b : List Nat} (h : cDistinct (a ++ b) = true) : cDistinct a = true ∧ cDistinct b = true ∧ ∀ x ∈ a, x ∉ b := by
  induction a with
  | nil => exact ⟨rfl, h, by simp⟩
  | cons x xs ih =>
    obtain ⟨hx, hr⟩ := cDistinct_cons h
    obtain ⟨h1, h2, h3⟩ := ih hr
    refine ⟨?_, h2, fun y hy => ?_⟩
    · simp only [cDistinct, Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨by simpa [List.contains_iff_mem] using fun hm => hx (List.mem_append_left _ hm), h1⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact fun hm => hx (List.mem_append_right _ hm)
      · exact h3 y hy

structure CParts (s : SMachine) (ds : List CDecl) (ps : List CEntry) : Prop where
  sok : sOk s = true
  pre : avoids (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)) s.f.m.pre = true
  preR : readsC s.f.m.pre = false
  terms : sTermsOk s (flagVars s.f.flags) = true
  facts : factsOk s = true
  dist : cDistinct (cMaps ds ++ cPosts ds) = true
  apart : cApart s ds = true
  decls : ∀ d ∈ ds, cDeclOk s ds (ps.map (·.e)) d = true
  entries : ∀ ce ∈ ps, cEntryOk s ds (ps.map (·.e)) ce.e = true ∧ checkMC (cStartGoal s ds ce.e) (cStartDecls s ds) ce.start = true
    ∧ checkMC (cStepGoal s ds (ps.map (·.e)) ce.e) (cStepDecls s ds) ce.step = true

theorem cparts {s : SMachine} {ds : List CDecl} {ps : List CEntry} (h : checkCMachine s ds ps = true) : CParts s ds ps := by
  simp only [checkCMachine, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun ce hce => ⟨(h9 ce hce).1.1, (h9 ce hce).1.2, (h9 ce hce).2⟩⟩

structure ApartParts (s : SMachine) (ds : List CDecl) : Prop where
  flags : ∀ p ∈ s.f.flags, avoidsMaps (cPosts ds) p.2 = true
  qflags : ∀ q ∈ s.qflags, avoidsMaps (cPosts ds) q.2.2 = true
  step : ∀ p ∈ s.f.m.step, avoidsMapsE (cPosts ds) p.2 = true
  writes : ∀ w ∈ s.f.m.writes, avoidsMapsE (cPosts ds) w.2.1 = true ∧ avoidsMapsE (cPosts ds) w.2.2 = true
  every : ∀ w ∈ s.every, avoidsMapsE (cPosts ds) w.2.2 = true
  init : ∀ p ∈ s.f.m.init, avoidsMapsE (cPosts ds) p.2 = true
  assume : avoidsMaps (cPosts ds) s.f.m.assume = true
  facts : ∀ l ∈ s.facts, avoidsMaps (cPosts ds) l.holds = true
  pfacts : ∀ f ∈ s.pfacts, avoidsMaps (cPosts ds) f.1.holds = true
  posts : ∀ mp ∈ cPosts ds, mp ∉ s.carried ∧ mp ∉ s.f.m.maps0.map (·.1) ∧ mp ∉ s.every.map (·.1) ∧ mp ∉ s.f.m.writes.map (·.1)

theorem apart_parts {s : SMachine} {ds : List CDecl} (h : cApart s ds = true) : ApartParts s ds := by
  simp only [cApart, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, fun w hw => ⟨(h4 w hw).1, (h4 w hw).2⟩, h5, h6, h7, h8, h9, fun mp hm =>
    ⟨by simpa [List.contains_iff_mem] using (h10 mp hm).1.1.1, by simpa [List.contains_iff_mem] using (h10 mp hm).1.1.2,
      by simpa [List.contains_iff_mem] using (h10 mp hm).1.2, by simpa [List.contains_iff_mem] using (h10 mp hm).2⟩⟩

structure FreshParts (s : SMachine) (x : Nat) : Prop where
  sk : skFresh s x = true
  init : ∀ p ∈ s.f.m.init, occE x p.2 = false
  out : (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains x = false

theorem mfresh_parts {s : SMachine} {x : Nat} (h : mFresh s x = true) : FreshParts s x := by
  simp only [mFresh, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem fresh_out {s : SMachine} {x : Nat} (h : (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains x = false) :
    x ∉ s.extVars ∧ x ∉ flagVars s.f.flags ∧ x ∉ s.f.m.init.map (·.1) ∧ x ∉ s.f.m.step.map (·.1) ∧ x ∉ s.f.m.inputs ∧ x ∉ s.qVars ∧ x ∉ s.wVars := by
  have hn : x ∉ s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1) := fun hm => by
    rw [List.contains_iff_mem.mpr hm] at h; cases h
  simp only [List.mem_append, not_or] at hn
  obtain ⟨⟨⟨hE, hF⟩, hI⟩, hS⟩ := hn
  simp only [SMachine.extVars, List.mem_append, not_or] at hE
  exact ⟨by simp only [SMachine.extVars, List.mem_append, not_or]; exact hE, hF, hI, hS, hE.1.1, hE.1.2, hE.2⟩

structure DeclParts (s : SMachine) (ds : List CDecl) (ps : List SEntry) (d : CDecl) : Prop where
  carried : d.mp ∈ s.carried
  jk : d.j ≠ d.key
  jf : FreshParts s d.j
  kf : FreshParts s d.key
  kB : occE d.key d.below = false
  qwB : avoidsE (s.qVars ++ s.wVars) d.below = true
  qwD : avoidsE (s.qVars ++ s.wVars) d.body = true
  mB : avoidsMapsE (cMaps ds ++ cPosts ds) d.below = true
  mD : avoidsMapsE (cMaps ds ++ cPosts ds) d.body = true
  ent : ∀ e ∈ ps, ∀ g ∈ e.sk :: e.keys2, occE g d.below = false ∧ occE g d.body = false ∧ g ≠ d.j ∧ g ≠ d.key

theorem decl_parts {s : SMachine} {ds : List CDecl} {ps : List SEntry} {d : CDecl} (h : cDeclOk s ds ps d = true) : DeclParts s ds ps d := by
  simp only [cDeclOk, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h0⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨by simpa [List.contains_iff_mem] using h1, h2, mfresh_parts h3, mfresh_parts h4, h0, h5, h6, h7, h8,
    fun e he g hg => ⟨(h9 e he g hg).1.1.1, (h9 e he g hg).1.1.2, (h9 e he g hg).1.2, (h9 e he g hg).2⟩⟩

structure EntryParts (s : SMachine) (ds : List CDecl) (ps : List SEntry) (e : SEntry) : Prop where
  lx : avoids (s.extVars ++ flagVars s.f.flags) e.law.holds = true
  lm : avoidsMaps (s.carried.filter (fun mp => !(stateMaps s ds).contains mp) ++ cPosts ds) e.law.holds = true
  fresh : (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains e.sk = false
  slaw : ∀ e' ∈ ps, occC e.sk e'.law.holds = false
  spre : occC e.sk s.f.m.pre = false
  sinit : ∀ p ∈ s.f.m.init, occE e.sk p.2 = false
  skf : skFresh s e.sk = true
  k2 : key2Ok s ps e = true

theorem entry_parts {s : SMachine} {ds : List CDecl} {ps : List SEntry} {e : SEntry} (h : cEntryOk s ds ps e = true) : EntryParts s ds ps e := by
  simp only [cEntryOk, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

-- The entries, as checkSMachine's lemmas read them.
theorem key2_parts {s : SMachine} {ds : List CDecl} {ps : List SEntry} (hk : ∀ e ∈ ps, cEntryOk s ds ps e = true) {e : SEntry} (he : e ∈ ps) {g : Nat} (hg : g ∈ e.keys2) :
    skFresh s g = true ∧ (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains g = false
      ∧ occC g s.f.m.pre = false ∧ (∀ p ∈ s.f.m.init, occE g p.2 = false) ∧ (∀ e' ∈ ps, occC g e'.law.holds = false ∨ g ∈ e'.keys2)
      ∧ e.law.key ≠ some g := by
  have hk' := (entry_parts (hk e he)).k2
  simp only [key2Ok, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, Bool.or_eq_true, List.contains_iff_mem] at hk'
  obtain ⟨⟨⟨⟨⟨hkey, hf⟩, hc⟩, hp⟩, hi⟩, hall⟩ := hk' g hg
  exact ⟨hf, by simpa [List.contains_iff_mem] using hc, hp, hi, fun e' he' => (by have := (hall e' he').1; simpa using this), hkey⟩

/-! Maps read off a list's names -/

-- A map with the names a declaration list posts at its post counts.
def atPosts (ds : List CDecl) (F : CDecl → Nat → Nat) (N : Nat → Nat → Nat) : Nat → Nat → Nat := fun mp =>
  match lookup (fun d => d.post == mp) ds with
  | some d => F d
  | none => N mp

theorem atPosts_other {ds : List CDecl} {mp : Nat} (h : mp ∉ cPosts ds) (F : CDecl → Nat → Nat) (N : Nat → Nat → Nat) : atPosts ds F N mp = N mp := by
  simp only [atPosts]
  rw [lookup_none (fun d hd => by simp only [beq_eq_false_iff_ne]; intro he; exact h (by rw [← he]; exact List.mem_map_of_mem hd))]

theorem atPosts_at {ds : List CDecl} (hd : cDistinct (cPosts ds) = true) {d : CDecl} (hm : d ∈ ds) (F : CDecl → Nat → Nat) (N : Nat → Nat → Nat) :
    atPosts ds F N d.post = F d := by
  simp only [atPosts]
  have : lookup (fun d' => d'.post == d.post) ds = some d := by
    induction ds with
    | nil => simp at hm
    | cons a as ih =>
      simp only [cPosts, List.map_cons] at hd
      obtain ⟨hna, hd'⟩ := cDistinct_cons hd
      rcases List.mem_cons.mp hm with rfl | hm'
      · simp [lookup]
      · have hne : (a.post == d.post) = false := by
          simp only [beq_eq_false_iff_ne]; intro he; exact hna (by rw [he]; exact List.mem_map_of_mem hm')
        simp only [lookup, hne, Bool.false_eq_true, ite_false]
        exact ih hd' hm'
  rw [this]

-- Renamed, the post counts read as the counts: a count map read by its post name.
theorem renM_atPosts {ds : List CDecl} (hd : cDistinct (cMaps ds ++ cPosts ds) = true) (F : CDecl → Nat → Nat) (N : Nat → Nat → Nat) :
    ∀ mp, mp ∉ cPosts ds → renM (cren ds) (atPosts ds F N) mp = match lookup (fun d => d.mp == mp) ds with
      | some d => F d
      | none => N mp := by
  obtain ⟨hdm, hdp, hap⟩ := cDistinct_append hd
  intro mp hmp
  simp only [renM]
  have hl : ∀ (ds' : List CDecl), (∀ d ∈ ds', d ∈ ds) → (lookup (fun p => p.1 == mp) (cren ds')).map (·.2) = (lookup (fun d => d.mp == mp) ds').map (·.post) := by
    intro ds' _
    induction ds' with
    | nil => rfl
    | cons a as ih =>
      simp only [cren, List.map_cons, lookup] at ih ⊢
      by_cases ha : a.mp = mp
      · simp [ha]
      · simp only [ha, beq_self_eq_true, beq_iff_eq, ite_false]; exact ih (fun d hd => by simp_all)
  have := hl ds (fun d hd => hd)
  cases h1 : lookup (fun d => d.mp == mp) ds with
  | none =>
    rw [h1] at this
    cases h2 : lookup (fun p => p.1 == mp) (cren ds) with
    | none => simp only []; exact atPosts_other hmp F N
    | some p => rw [h2] at this; simp at this
  | some d =>
    rw [h1] at this
    cases h2 : lookup (fun p => p.1 == mp) (cren ds) with
    | none => rw [h2] at this; simp at this
    | some p =>
      rw [h2] at this
      simp only [Option.map_some, Option.some.injEq] at this
      simp only []
      rw [this]
      exact atPosts_at hdp (lookup_some h1).1 F N

/-! Terms read across a substitution that keeps j and key -/

theorem assoc_term {σ : List (Nat × E)} {i : Nat} {t : E} (h : assoc σ i = some t) : (i, t) ∈ σ := by
  simp only [assoc, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  have ⟨hm, hp⟩ := lookup_some ha
  simp only [beq_iff_eq] at hp
  rw [← hp]; exact hm

theorem applyS_congrM {σ : List (Nat × E)} {X : List Nat} (h : ∀ p ∈ σ, avoidsMapsE X p.2 = true) (ρ : Nat → Nat) {M M' : Nat → Nat → Nat}
    (hm : ∀ mp, mp ∉ X → M mp = M' mp) : applyS σ ρ M = applyS σ ρ M' := by
  funext i
  simp only [applyS]
  cases ha : assoc σ i with
  | none => rfl
  | some t => exact congrME ρ M M' t (fun mp hmp => hm mp (avoidsMapsE_occ (h _ (assoc_term ha)) hmp))

theorem applyS_jk (j key : Nat) (σ : List (Nat × E)) (Y : Nat → Nat) (N : Nat → Nat → Nat) (i : Nat) :
    applyS ((j, .var j) :: (key, .var key) :: σ) Y N i = if i = j then Y j else if i = key then Y key else applyS σ Y N i := by
  simp only [applyS, assoc, lookup, beq_iff_eq]
  by_cases h1 : j = i
  · subst h1; simp [evalE]
  · by_cases h2 : key = i
    · subst h2; simp [h1, Ne.symm h1, evalE]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem avoidsMaps_right {A B : List Nat} {c : C} (h : avoidsMaps (A ++ B) c = true) : avoidsMaps B c = true := by
  simp only [avoidsMaps, List.all_append, Bool.and_eq_true] at h; exact h.2
theorem avoidsMapsE_right {A B : List Nat} {e : E} (h : avoidsMapsE (A ++ B) e = true) : avoidsMapsE B e = true := by
  simp only [avoidsMapsE, List.all_append, Bool.and_eq_true] at h; exact h.2

/-! The start -/

theorem cstart_case (s : SMachine) (ds : List CDecl) (ps : List CEntry) (h : checkCMachine s ds ps = true) (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (hM : StartMaps s.f.m M) (h0 : evalC ρ M s.f.m.pre = true) (hfa : ∀ l ∈ s.facts, l.Holds ρ M) (hpf : s.PFacts ρ M) :
    ∀ ce ∈ ps, ce.e.law.Holds (applyS s.f.m.init ρ M) (withCnt ds (applyS s.f.m.init ρ M) M) := by
  have P := cparts h
  have A := apart_parts P.apart
  obtain ⟨_, hdp, _⟩ := cDistinct_append P.dist
  intro ce hce
  obtain ⟨hent, hst, _⟩ := P.entries ce hce
  have E' := entry_parts hent
  have hskI : ce.e.sk ∉ s.f.m.init.map (·.1) := (fresh_out E'.fresh).2.2.1
  let X0 := applyS s.f.m.init ρ M
  let M2 := atPosts ds (fun d => cntOf d X0 M) M
  have hM2 : ∀ mp, mp ∉ cPosts ds → M2 mp = M mp := fun mp h => atPosts_other h _ M
  have hlp : avoidsMaps (cPosts ds) ce.e.law.holds = true := avoidsMaps_right E'.lm
  -- The law at the start reads as the renamed law with the post names at the counts.
  refine holds_transfer (V := []) (MS := cPosts ds) ce.e.law (by simp [avoids]) hlp (fun _ _ => rfl)
    (fun mp hmp => (renM_atPosts P.dist (fun d => cntOf d X0 M) M mp hmp).symm) ?_
  rw [← renLaw_holds]
  refine goalOf_holds (renLaw ds ce.e.law) (by simp only [renLaw, occ_renC]; exact E'.slaw ce.e (List.mem_map_of_mem hce)) X0 M2 (fun v => ?_)
  apply Decidable.byContradiction; intro hn
  -- The start's reads: a declared map's constant, any other map as M2 holds it.
  have hrdS : ∀ (Y : Nat → Nat) mp k, mp ∉ cPosts ds → evalE Y M2 (rdStart s.f.m mp k) = M mp (evalE Y M2 k) := by
    intro Y mp k hmp
    simp only [rdStart]
    split
    · rename_i p hp
      have ⟨hm, hq⟩ := lookup_some hp
      simp only [beq_iff_eq] at hq
      simp only [evalE]; rw [← hq, hM p hm]
    · simp only [evalE]; rw [hM2 mp hmp]
  have hrd2 : ∀ mp k, evalE (upd ρ ce.e.sk v) M2 (rdStart s.f.m mp k) = M2 mp (evalE (upd ρ ce.e.sk v) M2 k) := by
    intro mp k
    simp only [rdStart]
    split
    · rename_i p hp
      have ⟨hm, hq⟩ := lookup_some hp
      simp only [beq_iff_eq] at hq
      have hp1 : p.1 ∉ cPosts ds := fun hc => (A.posts p.1 hc).2.1 (List.mem_map_of_mem hm)
      simp only [evalE]; rw [← hq, hM2 _ hp1, hM p hm]
    · rfl
  have hX0 : applyS s.f.m.init ρ M2 = X0 := applyS_congrM A.init ρ (fun mp hmp => hM2 mp hmp)
  apply mc_sound _ _ _ hst (upd ρ ce.e.sk v) M2
  · -- Each post count: its bound and body, read across the start, are the declaration's at the start state.
    intro d' hd' x
    obtain ⟨d, hdf, rfl⟩ := List.mem_map.mp hd'
    have hd := (List.mem_filter.mp hdf).1
    have D := decl_parts (P.decls d hd)
    obtain ⟨hskB, hskD, hskj, hskk⟩ := D.ent ce.e (List.mem_map_of_mem hce) ce.e.sk List.mem_cons_self
    have hpB : avoidsMapsE (cPosts ds) d.below = true := avoidsMapsE_right D.mB
    have hpD : avoidsMapsE (cPosts ds) d.body = true := avoidsMapsE_right D.mD
    have hjI := (fresh_out D.jf.out).2.2.1
    have hkI := (fresh_out D.kf.out).2.2.1
    simp only [afterDecl]
    rw [show M2 d.post = cntOf d X0 M from atPosts_at hdp hd _ M]
    simp only [cntOf]
    -- reading across the start at Y (the goal's state with j, and key, set): the start state with them set
    have hacross : ∀ (Y T : Nat → Nat) (e : E), avoidsMapsE (cPosts ds) e = true → occE ce.e.sk e = false →
        (∀ i, i ≠ d.j → i ≠ d.key → Y i = upd ρ ce.e.sk v i) → T d.j = Y d.j → T d.key = Y d.key → (∀ i, i ≠ d.j → i ≠ d.key → T i = X0 i) →
        evalE Y M2 (substRE ((d.j, .var d.j) :: (d.key, .var d.key) :: s.f.m.init) (rdStart s.f.m) e) = evalE T M e := by
      intro Y T e hpe hske hY hTj hTk hT
      rw [substR_evalE_on _ _ Y M2 M (cPosts ds) (fun mp k hmp => hrdS Y mp k hmp) e hpe]
      refine congrE _ _ M e (fun i hi => ?_)
      rw [applyS_jk]
      by_cases h1 : i = d.j
      · subst h1; simp [hTj]
      · by_cases h2 : i = d.key
        · subst h2; simp [h1, hTk]
        · simp only [h1, h2, ite_false]
          have hik : i ≠ ce.e.sk := fun h' => by rw [h', hske] at hi; cases hi
          rw [hT i h1 h2, ← hX0]
          simp only [applyS]
          cases ha : assoc s.f.m.init i with
          | none => simp [hY i h1 h2, upd, hik]
          | some t =>
            have hmem := assoc_term ha
            refine congrE _ _ M2 t (fun i' hi' => ?_)
            have hi'j : i' ≠ d.j := fun h' => by rw [h', D.jf.init _ hmem] at hi'; cases hi'
            have hi'k : i' ≠ d.key := fun h' => by rw [h', D.kf.init _ hmem] at hi'; cases hi'
            have hi's : i' ≠ ce.e.sk := fun h' => by rw [h', E'.sinit _ hmem] at hi'; cases hi'
            rw [hY i' hi'j hi'k]; simp [upd, hi's]
    have hB := hacross (upd (upd ρ ce.e.sk v) d.j x) (upd X0 d.j x) d.below hpB hskB
      (fun i h1 _ => by simp [upd, h1]) (by simp [upd])
      (by show upd X0 d.j x d.key = upd (upd ρ ce.e.sk v) d.j x d.key
          simp only [upd, if_neg (Ne.symm D.jk), if_neg (Ne.symm hskk)]; exact applyS_other hkI ρ M)
      (fun i h1 _ => by simp [upd, h1])
    rw [hB]
    refine sumBelow_congr _ (fun k _ => ?_)
    exact (hacross (upd (upd (upd ρ ce.e.sk v) d.j x) d.key k) (upd (upd X0 d.j x) d.key k) d.body hpD hskD
      (fun i h1 h2 => by simp [upd, h1, h2]) (by simp [upd, D.jk]) (by simp [upd]) (fun i h1 h2 => by simp [upd, h1, h2])).symm
  · intro c hc
    simp only [cStartGoal, sStartGoal, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | hc) | rfl
    · rw [noReadsC _ M2 M s.f.m.pre P.preR, congrC _ ρ M s.f.m.pre (fun i hi => by
        simp only [upd]; split
        · rename_i hik; subst hik; simp [E'.spre] at hi
        · rfl)]
      exact h0
    · exact facthyps_true s ce.e.finsts ce.e.pfinsts _ M2 (fun f hf => (pfactsOk_parts P.facts f hf).2.2)
        (facts_frame s P.facts [ce.e.sk] (cPosts ds) (fun l hl => by simp [avoids, (skFresh_parts E'.skf).2.2.2.2.2.2 l hl]) A.facts
          (fun i _ hik => by simp only [upd]; rw [if_neg (by simpa using hik)]) (fun mp _ hmp => hM2 mp hmp) hfa)
        (pfacts_frame s P.facts [ce.e.sk] (cPosts ds) (fun f hf => by simp [avoids, skFresh_pfacts E'.skf f hf]) A.pfacts
          (fun i _ hik => by simp only [upd]; rw [if_neg (by simpa using hik)]) (fun mp _ hmp => hM2 mp hmp) hpf) c hc
    · simp only [evalC, substR_evalC _ _ _ M2 M2 hrd2]
      rw [applyS_upd hskI (by simpa [List.all_eq_true] using E'.sinit), hX0]
      simpa using hn

/-! A state with the post names set: the machine reads them nowhere -/

theorem withCarried_posts {s : SMachine} {ds : List CDecl} (hpc : ∀ mp ∈ cPosts ds, mp ∉ s.carried) (F : CDecl → Nat → Nat)
    (M κ : Nat → Nat → Nat) : withCarried s (atPosts ds F M) κ = atPosts ds F (withCarried s M κ) := by
  funext mp
  by_cases hmp : mp ∈ cPosts ds
  · have hc : mp ∉ s.carried := hpc mp hmp
    have e1 : withCarried s (atPosts ds F M) κ mp = atPosts ds F M mp := by simp [withCarried, List.contains_iff_mem, hc]
    have e2 : withCarried s M κ mp = M mp := by simp [withCarried, List.contains_iff_mem, hc]
    rw [e1]
    cases hl : lookup (fun d => d.post == mp) ds with
    | none => simp only [atPosts, hl]; exact e2.symm
    | some d => simp only [atPosts, hl]
  · rw [atPosts_other hmp]; simp only [withCarried]; split
    · rfl
    · exact atPosts_other hmp F M

theorem posts_evalC {ds : List CDecl} {c : C} (h : avoidsMaps (cPosts ds) c = true) (X : Nat → Nat) (F : CDecl → Nat → Nat) (N : Nat → Nat → Nat) :
    evalC X (atPosts ds F N) c = evalC X N c :=
  congrMC X _ N c (fun mp hm => atPosts_other (avoidsMaps_occ h hm) F N)
theorem posts_evalE {ds : List CDecl} {e : E} (h : avoidsMapsE (cPosts ds) e = true) (X : Nat → Nat) (F : CDecl → Nat → Nat) (N : Nat → Nat → Nat) :
    evalE X (atPosts ds F N) e = evalE X N e :=
  congrME X _ N e (fun mp hm => atPosts_other (avoidsMapsE_occ h hm) F N)

theorem decideQ_posts {s : SMachine} {ds : List CDecl} (hq : ∀ q ∈ s.qflags, avoidsMaps (cPosts ds) q.2.2 = true) (X : Nat → Nat)
    (F : CDecl → Nat → Nat) (N : Nat → Nat → Nat) : decideQ s X (atPosts ds F N) = decideQ s X N := by
  funext v
  simp only [decideQ]
  split
  · rename_i q hl
    have hb := hq q (lookup_some hl).1
    have : (∀ k, holdsC (atKeys X q.2.1 k) (atPosts ds F N) q.2.2) ↔ (∀ k, holdsC (atKeys X q.2.1 k) N q.2.2) := by
      simp only [← evalC_iff, posts_evalC hb]
    simp only [this]
  · rfl

theorem decideFlags_posts {fl : List (Nat × C)} {ds : List CDecl} (hf : ∀ p ∈ fl, avoidsMaps (cPosts ds) p.2 = true) (X : Nat → Nat)
    (F : CDecl → Nat → Nat) (N : Nat → Nat → Nat) : decideFlags fl X (atPosts ds F N) = decideFlags fl X N :=
  applyS_congrM (X := cPosts ds) (fun p hp => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have := hf q hq
    simp only [avoidsMapsE, avoidsMaps, List.all_eq_true, Bool.not_eq_true'] at this ⊢
    intro mp hm; simp [occME, this mp hm]) X (fun mp hmp => atPosts_other hmp F N)

theorem sView_posts {s : SMachine} {ds : List CDecl} (A : ApartParts s ds) (F : CDecl → Nat → Nat) (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) : sView s ρ (atPosts ds F M) ι κ = ((sView s ρ M ι κ).1, atPosts ds F (sView s ρ M ι κ).2) := by
  simp only [sView, withCarried_posts (fun mp hm => (A.posts mp hm).1), decideQ_posts A.qflags, decideFlags_posts A.flags]

theorem sNext_posts {s : SMachine} {ds : List CDecl} (A : ApartParts s ds) (F : CDecl → Nat → Nat) (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) : sNext s ρ (atPosts ds F M) ι κ = ((sNext s ρ M ι κ).1, atPosts ds F (sNext s ρ M ι κ).2) := by
  simp only [sNext, sView_posts A]
  congr 1
  · exact applyS_congrM A.step _ (fun mp hmp => atPosts_other hmp F _)
  · funext mp key
    by_cases hmp : mp ∈ cPosts ds
    · have he : lookup (fun w => w.1 == mp) s.every = none := lookup_none (fun w hw => by
        simp only [beq_eq_false_iff_ne]; intro h'; exact (A.posts mp hmp).2.2.1 (by rw [← h']; exact List.mem_map_of_mem hw))
      have hw : lookup (fun w : Nat × E × E => w.1 == mp) s.f.m.writes = none := lookup_none (fun w hw => by
        simp only [beq_eq_false_iff_ne]; intro h'; exact (A.posts mp hmp).2.2.2 (by rw [← h']; exact List.mem_map_of_mem hw))
      have hE : everyMaps s (sView s ρ M ι κ).1 (atPosts ds F (sView s ρ M ι κ).2) mp key = atPosts ds F (sView s ρ M ι κ).2 mp key := by
        simp only [everyMaps, he, writeMaps, hw]
      have hE' : everyMaps s (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 mp key = (sView s ρ M ι κ).2 mp key := by
        simp only [everyMaps, he, writeMaps, hw]
      rw [hE]
      cases hl : lookup (fun d => d.post == mp) ds with
      | none => simp only [atPosts, hl]; exact hE'.symm
      | some d => simp only [atPosts, hl]
    · rw [atPosts_other hmp]
      simp only [everyMaps]
      split
      · rename_i w hw
        exact posts_evalE (A.every w (lookup_some hw).1) _ F _
      · simp only [writeMaps]
        split
        · rename_i w hw
          have ⟨h1, h2⟩ := A.writes w (lookup_some hw).1
          rw [posts_evalE h1, posts_evalE h2, atPosts_other hmp]
        · rw [atPosts_other hmp]

theorem sReq_posts {s : SMachine} {ds : List CDecl} (A : ApartParts s ds) (F : CDecl → Nat → Nat) (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) : sReq s ρ (atPosts ds F M) ι κ = sReq s ρ M ι κ := by
  funext v
  simp only [sReq, withCarried_posts (fun mp hm => (A.posts mp hm).1), decideQ_posts A.qflags]
  split
  · rfl
  · split
    · rfl
    · split
      · split
        · rename_i q hq'
          split
          · apply congrFun
            apply witnessKeys_congr
            intro k
            simp only [← evalC_iff, posts_evalC (A.qflags q (lookup_some hq').1)]
          · rfl
        · rfl
      · rfl

/-! One step's frame, at any state (Sets.lean's sstep_case builds the same) -/

theorem cframe {s : SMachine} (hs : sOk s = true) (hterms : sTermsOk s (flagVars s.f.flags) = true) (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    (∀ Z, SHead s Z [] (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ) [] getRd ρ M [] [] ι κ)
      ∧ SDenotes s (flagVars s.f.flags) [] (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ)
          (stepSub s.f (frameSub [] []) (frameRd [] getRd)) (stepRdS s (frameSub [] []) (frameRd [] getRd)) (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2 := by
  obtain ⟨hfav, hstp, hwr, hev⟩ := sTermsOk_parts hterms
  let W := withExt s ρ (sReq s ρ M ι κ)
  let M0 := withCarried s M κ
  have hH : ∀ Z, SHead s Z [] W M0 [] getRd ρ M [] [] ι κ := fun Z => by
    refine ⟨fun i _ => ?_, fun mp k _ => ?_⟩
    · show applyS (frameSub [] []) W M0 i = W i
      simp only [frameSub, List.map_nil, List.append_nil, applyS_nil']
    · simp [frameRd, getRd, lookup, evalE, M0]
  have hD : SDenotes s (flagVars s.f.flags) [] W M0 [] getRd ρ M := by
    refine ⟨fun i hie _ => ?_, fun mp k hmp _ => ?_⟩
    · rw [applyS_nil']; simp only [W, withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hie)]
    · simp only [getRd, evalE, M0, withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmp)]
  exact ⟨hH, sstep_denotes s (flagVars s.f.flags) [] W M0 hs (fun v hv => hv) hfav [] [] ι κ hD (hH _) (fun p hp => by simp at hp)
    hstp (fun w hw => (hwr w hw).1) hev (fun _ _ => by simp [avoidsMapsE]) (fun _ _ => by simp [avoidsMapsE]) (fun _ _ => by simp [avoidsMapsE])⟩

/-! Terms across a step that keeps j and key -/

theorem withExt_upd {s : SMachine} {g : Nat} (hg : g ∉ s.extVars) (ρ R : Nat → Nat) (w : Nat) : withExt s (upd ρ g w) R = upd (withExt s ρ R) g w := by
  funext i
  simp only [withExt, upd]
  by_cases h : i = g
  · subst h; simp [List.contains_iff_mem, hg]
  · simp [h]

-- A term of the state read across the step, j and key kept: its value at the state after the step, where the frame
-- reads j and key as the state after it does.
theorem across_step {s : SMachine} (hs : sOk s = true) (hterms : sTermsOk s (flagVars s.f.flags) = true) (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) (j key : Nat) (e : E) (he : avoidsE (s.extVars ++ flagVars s.f.flags) e = true)
    (hem : avoidsMapsE s.carried e = true)
    (hj : (sNext s ρ M ι κ).1 j = withExt s ρ (sReq s ρ M ι κ) j) (hk : (sNext s ρ M ι κ).1 key = withExt s ρ (sReq s ρ M ι κ) key) :
    evalE (withExt s ρ (sReq s ρ M ι κ)) (withCarried s M κ)
      (substRE ((j, .var j) :: (key, .var key) :: stepSub s.f (frameSub [] []) (frameRd [] getRd)) (stepRdS s (frameSub [] []) (frameRd [] getRd)) e)
      = evalE (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2 e := by
  obtain ⟨_, hD⟩ := cframe hs hterms ρ M ι κ
  rw [substR_evalE_on _ _ _ _ (sNext s ρ M ι κ).2 s.carried (fun mp k hmp => hD.2 mp k hmp (by simp)) e hem]
  refine congrE _ _ _ e (fun i hi => ?_)
  rw [applyS_jk]
  by_cases h1 : i = j
  · subst h1; simp [hj]
  · by_cases h2 : i = key
    · subst h2; simp [h1, hk]
    · simp only [h1, h2, ite_false]
      have hx := avoidsE_occ he hi
      exact hD.1 i (fun h => hx (List.mem_append_left _ h)) (fun h => hx (List.mem_append_right _ h))

-- Two reads of a count agree where its bound and body read alike.
theorem cntOf_congr (d : CDecl) (hkB : occE d.key d.below = false) {X X' : Nat → Nat} {N N' : Nat → Nat → Nat}
    (hv : ∀ i, i ≠ d.j → i ≠ d.key → occE i d.below = true ∨ occE i d.body = true → X i = X' i)
    (hm : ∀ mp, occME mp d.below = true ∨ occME mp d.body = true → N mp = N' mp) (x : Nat) : cntOf d X N x = cntOf d X' N' x := by
  simp only [cntOf]
  have hB : evalE (upd X d.j x) N d.below = evalE (upd X' d.j x) N' d.below := by
    rw [congrME _ N N' d.below (fun mp h => hm mp (Or.inl h))]
    exact congrE _ _ _ d.below (fun i hi => by
      simp only [upd]; split
      · rfl
      · rename_i h1
        have h2 : i ≠ d.key := fun h => by rw [h, hkB] at hi; cases hi
        exact hv i h1 h2 (Or.inl hi))
  rw [hB]
  exact sumBelow_congr _ (fun k _ => by
    rw [congrME _ N N' d.body (fun mp h => hm mp (Or.inr h))]
    exact congrE _ _ _ d.body (fun i hi => by
      simp only [upd]; split
      · rfl
      · split
        · rfl
        · rename_i h1 h2; exact hv i h2 h1 (Or.inr hi)))

/-! One step -/

-- A variable no step sets, decides or reads from the request: the state after a step keeps it.
theorem sNext_other {s : SMachine} {x : Nat} (h : (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains x = false)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) : (sNext s ρ M ι κ).1 x = ρ x := by
  obtain ⟨_, hF, _, hS, hI, hQ, _⟩ := fresh_out h
  simp only [sNext, sView]
  rw [applyS_other hS, decide_other hF]
  simp only [decideQ]
  rw [lookup_none (fun q hq => by
    simp only [beq_eq_false_iff_ne]; intro he
    exact hQ (by simp only [SMachine.qVars, List.mem_map]; exact ⟨q, hq, he⟩))]
  exact withInputs_other hI ρ ι

theorem avoids_left {A B : List Nat} {c : C} (h : avoids (A ++ B) c = true) : avoids A c = true := by
  simp only [avoids, List.all_append, Bool.and_eq_true] at h; exact h.1
theorem cstep_case (s : SMachine) (ds : List CDecl) (ps : List CEntry) (h : checkCMachine s ds ps = true) (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) (hp0 : evalC ρ M s.f.m.pre = true) (hfa : ∀ l ∈ s.facts, l.Holds ρ M) (hpf : s.PFacts ρ M)
    (ih : ∀ ce ∈ ps, ce.e.Holds ρ (withCnt ds ρ M)) (hG : GHolds ds (withInputs s.f.m.inputs ρ ι) (withCarried s M κ))
    (ha : evalC (sView s ρ M ι κ).1 (sView s ρ M ι κ).2 s.f.m.assume = true) :
    ∀ ce ∈ ps, ce.e.law.Holds (sNext s ρ M ι κ).1 (withCnt ds (sNext s ρ M ι κ).1 (sNext s ρ M ι κ).2) := by
  have P := cparts h
  have A := apart_parts P.apart
  have hs := P.sok
  obtain ⟨hdm, hdp, hap⟩ := cDistinct_append P.dist
  have hentry : ∀ e ∈ ps.map (·.e), cEntryOk s ds (ps.map (·.e)) e = true := fun e he => by
    obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp he; exact (P.entries ce hce).1
  have hkk : ∀ e ∈ ps.map (·.e), ∀ k, e.law.key = some k → k ∉ e.keys2 := fun e he k hk hg => (key2_parts hentry he hg).2.2.2.2.2 hk
  intro ce hce
  obtain ⟨hent, _, hstep⟩ := P.entries ce hce
  have E' := entry_parts hent
  have hsk := fresh_out E'.fresh
  let Nx := sNext s ρ M ι κ
  let F : CDecl → Nat → Nat := fun d => cntOf d Nx.1 Nx.2
  let M' := atPosts ds F M
  have hNx' : sNext s ρ M' ι κ = (Nx.1, atPosts ds F Nx.2) := sNext_posts A F ρ M ι κ
  have hpc : ∀ mp ∈ cPosts ds, mp ∉ s.carried := fun mp hm => (A.posts mp hm).1
  let Mq := withCarried s (atPosts ds F Nx.2) κ
  have hMq : Mq = atPosts ds F (withCarried s Nx.2 κ) := withCarried_posts hpc F Nx.2 κ
  -- The maps a law reads count maps of the state in: those the request carries but those, and the post names.
  let MS := s.carried.filter (fun mp => !(stateMaps s ds).contains mp) ++ cPosts ds
  have hMS : ∀ mp, mp ∉ MS → mp ∈ s.carried → ∃ d ∈ ds, d.mp = mp ∧ stateOnly s d = true := by
    intro mp hmp hc
    have : (stateMaps s ds).contains mp = true := by
      apply Classical.byContradiction; intro hn
      exact hmp (List.mem_append_left _ (List.mem_filter.mpr ⟨hc, by simpa using hn⟩))
    obtain ⟨d, hd, hdmp⟩ := List.mem_map.mp (List.contains_iff_mem.mp this)
    exact ⟨d, (List.mem_filter.mp hd).1, hdmp, (List.mem_filter.mp hd).2⟩
  have hnotP : ∀ mp, mp ∉ MS → mp ∉ cPosts ds := fun mp hmp h' => hmp (List.mem_append_right _ h')
  -- A state count read at the view is the count at the state.
  have hview : ∀ d ∈ ds, stateOnly s d = true → ∀ x, κ d.mp x = cntOf d ρ M x := by
    intro d hd hso x
    have hc : d.mp ∈ s.carried := (decl_parts (P.decls d hd)).carried
    have := hG d hd x
    simp only [withCarried, List.contains_iff_mem.mpr hc, ite_true] at this
    rw [this]
    simp only [stateOnly, Bool.and_eq_true] at hso
    obtain ⟨⟨⟨hvB, hvD⟩, hmB⟩, hmD⟩ := hso
    refine cntOf_congr d (decl_parts (P.decls d hd)).kB (fun i _ _ hi => ?_) (fun mp hm => ?_) x
    · have hx : i ∉ s.extVars := fun h' => by
        rcases hi with hi | hi
        · exact avoidsE_occ hvB hi (List.mem_append_left _ h')
        · exact avoidsE_occ hvD hi (List.mem_append_left _ h')
      exact withInputs_other (fun h' => hx (by simp only [SMachine.extVars, List.mem_append]; exact Or.inl (Or.inl h'))) ρ ι
    · have hx : mp ∉ s.carried := by
        rcases hm with hm | hm
        · exact avoidsMapsE_occ hmB hm
        · exact avoidsMapsE_occ hmD hm
      simp [withCarried, List.contains_iff_mem, hx]
  -- The law after the step: the renamed law, with the post names at the counts after it.
  refine holds_transfer (V := []) (MS := MS) (M' := renM (cren ds) Mq) ce.e.law (by simp [avoids]) E'.lm (fun _ _ => rfl) (fun mp hmp => ?_) ?_
  · rw [hMq, renM_atPosts P.dist F _ mp (hnotP mp hmp)]
    simp only [withCnt]
    cases hl : lookup (fun d => d.mp == mp) ds with
    | some d => rfl
    | none =>
      have hnc : mp ∉ s.carried := fun hc => by
        obtain ⟨d, hd, hdmp, _⟩ := hMS mp hmp hc
        have := lookup_none_all hl d hd
        simp [hdmp] at this
      show (sNext s ρ M ι κ).2 mp = withCarried s (sNext s ρ M ι κ).2 κ mp
      simp [withCarried, List.contains_iff_mem, hnc]
  rw [← renLaw_holds]
  refine goalOf_holds (renLaw ds ce.e.law) (by simp only [renLaw, occ_renC]; exact E'.slaw ce.e (List.mem_map_of_mem hce)) Nx.1 Mq (fun v => ?_)
  apply Decidable.byContradiction; intro hn
  obtain ⟨hNext, hView, _⟩ := fresh_parts E'.skf E'.fresh ρ M' ι κ v
  let ρ' := upd ρ ce.e.sk v
  let W := withExt s ρ' (sReq s ρ' M' ι κ)
  let M0 := withCarried s M' κ
  obtain ⟨hH, hD'⟩ := cframe hs P.terms ρ' M' ι κ
  have hM0 : ∀ mp, mp ∉ cPosts ds → M0 mp = withCarried s M κ mp := fun mp hmp => by
    show withCarried s M' κ mp = _
    rw [withCarried_posts hpc F M κ, atPosts_other hmp]
  apply mc_sound _ _ _ hstep W M0
  · -- The counts the goal declares.
    intro d' hd' x
    rcases List.mem_append.mp hd' with hd | hd'
    · -- before the step: the request's count at its view
      have D := decl_parts (P.decls d' hd)
      obtain ⟨hskB, hskD, _, _⟩ := D.ent ce.e (List.mem_map_of_mem hce) ce.e.sk List.mem_cons_self
      rw [hM0 d'.mp (fun h' => hap d'.mp (List.mem_map_of_mem hd) h'), hG d' hd x]
      refine cntOf_congr d' D.kB (fun i _ _ hi => ?_) (fun mp hm => ?_) x
      · show withInputs s.f.m.inputs ρ ι i = withExt s ρ' (sReq s ρ' M' ι κ) i
        have hq : i ∉ s.qVars ++ s.wVars := by
          rcases hi with hi | hi
          · exact avoidsE_occ D.qwB hi
          · exact avoidsE_occ D.qwD hi
        have hik : i ≠ ce.e.sk := fun h' => by rcases hi with hi | hi <;> (rw [h'] at hi; simp_all)
        simp only [withExt]
        by_cases hie : s.extVars.contains i = true
        · simp only [hie, ite_true, sReq]
          have hin : s.f.m.inputs.contains i = true := by
            simp only [SMachine.extVars, List.contains_iff_mem, List.mem_append] at hie
            rcases hie with (h1 | h1) | h1
            · exact List.contains_iff_mem.mpr h1
            · exact absurd (List.mem_append_left _ h1) hq
            · exact absurd (List.mem_append_right _ h1) hq
          simp only [hin, ite_true, withInputs]
        · simp only [hie, Bool.false_eq_true, ite_false]
          have hin : i ∉ s.f.m.inputs := by
            simp only [SMachine.extVars, List.contains_iff_mem, List.mem_append, not_or] at hie
            exact hie.1.1
          rw [withInputs_other hin]
          simp [ρ', upd, hik]
      · have hx : mp ∉ cPosts ds := by
          rcases hm with hm | hm
          · exact fun h' => avoidsMapsE_occ D.mB hm (List.mem_append_right _ h')
          · exact fun h' => avoidsMapsE_occ D.mD hm (List.mem_append_right _ h')
        exact (hM0 mp hx).symm
    · -- after the step: a state count read across it
      obtain ⟨d, hdf, rfl⟩ := List.mem_map.mp hd'
      have hd := (List.mem_filter.mp hdf).1
      have hso := (List.mem_filter.mp hdf).2
      have D := decl_parts (P.decls d hd)
      obtain ⟨hskB, hskD, hskj, hskk⟩ := D.ent ce.e (List.mem_map_of_mem hce) ce.e.sk List.mem_cons_self
      simp only [stateOnly, Bool.and_eq_true] at hso
      obtain ⟨⟨⟨hvB, hvD⟩, hmB⟩, hmD⟩ := hso
      have hjo := fresh_out D.jf.out
      have hko := fresh_out D.kf.out
      have hpB : avoidsMapsE (cPosts ds) d.below = true := avoidsMapsE_right D.mB
      have hpD : avoidsMapsE (cPosts ds) d.body = true := avoidsMapsE_right D.mD
      show M0 d.post x = cntOf (afterDecl _ _ d) W M0 x
      rw [show M0 d.post = F d from by
        show withCarried s M' κ d.post = F d
        rw [withCarried_posts hpc F M κ]; exact atPosts_at hdp hd F _]
      simp only [cntOf, afterDecl]
      -- the state with j at x and key at k, and its frame
      have hstate : ∀ k, sReq s (upd (upd ρ' d.j x) d.key k) M' ι κ = sReq s ρ' M' ι κ := fun k => by
        rw [sReq_upd hko.2.2.2.2.1 hko.2.2.2.2.2.1 (skFresh_parts D.kf.sk).2.1, sReq_upd hjo.2.2.2.2.1 hjo.2.2.2.2.2.1 (skFresh_parts D.jf.sk).2.1]
      have hW : ∀ k, withExt s (upd (upd ρ' d.j x) d.key k) (sReq s (upd (upd ρ' d.j x) d.key k) M' ι κ) = upd (upd W d.j x) d.key k := fun k => by
        rw [hstate k, withExt_upd hko.1, withExt_upd hjo.1]
      have hN : ∀ k, sNext s (upd (upd ρ' d.j x) d.key k) M' ι κ = (upd (upd (upd Nx.1 ce.e.sk v) d.j x) d.key k, atPosts ds F Nx.2) := fun k => by
        rw [(fresh_parts D.kf.sk D.kf.out _ M' ι κ k).1, (fresh_parts D.jf.sk D.jf.out _ M' ι κ x).1, hNext, hNx']
      -- reading a term of the state across the step at a state with fresh variables set: its value after the step there
      have hacross : ∀ (ρx : Nat → Nat) (Y : Nat → Nat) (e : E), avoidsE (s.extVars ++ flagVars s.f.flags) e = true → avoidsMapsE s.carried e = true →
          avoidsMapsE (cPosts ds) e = true → occE ce.e.sk e = false →
          withExt s ρx (sReq s ρx M' ι κ) = Y → (sNext s ρx M' ι κ).1 = upd Y ce.e.sk v ∨ True →
          (sNext s ρx M' ι κ).1 d.j = Y d.j → (sNext s ρx M' ι κ).1 d.key = Y d.key → (sNext s ρx M' ι κ).2 = atPosts ds F Nx.2 →
          evalE Y M0 (substRE ((d.j, .var d.j) :: (d.key, .var d.key) :: stepSub s.f (frameSub [] []) (frameRd [] getRd))
            (stepRdS s (frameSub [] []) (frameRd [] getRd)) e) = evalE (sNext s ρx M' ι κ).1 Nx.2 e := by
        intro ρx Y e he hem hpe _ hY _ hj hk hM
        have := across_step hs P.terms ρx M' ι κ d.j d.key e he hem (by rw [hj, hY]) (by rw [hk, hY])
        rw [hY, hM] at this
        rw [this, posts_evalE hpe]
      -- the state with j at x (the bound), and with key at k too (the body)
      have hsj : sReq s (upd ρ' d.j x) M' ι κ = sReq s ρ' M' ι κ :=
        sReq_upd hjo.2.2.2.2.1 hjo.2.2.2.2.2.1 (skFresh_parts D.jf.sk).2.1 ρ' M' ι κ x
      have hsk : ∀ k, sReq s (upd (upd ρ' d.j x) d.key k) M' ι κ = sReq s ρ' M' ι κ := fun k => by
        rw [sReq_upd hko.2.2.2.2.1 hko.2.2.2.2.2.1 (skFresh_parts D.kf.sk).2.1, hsj]
      have hNj : sNext s (upd ρ' d.j x) M' ι κ = (upd (upd Nx.1 ce.e.sk v) d.j x, atPosts ds F Nx.2) := by
        rw [(fresh_parts D.jf.sk D.jf.out _ M' ι κ x).1, hNext, hNx']
      have hNk : ∀ k, sNext s (upd (upd ρ' d.j x) d.key k) M' ι κ = (upd (upd (upd Nx.1 ce.e.sk v) d.j x) d.key k, atPosts ds F Nx.2) := fun k => by
        rw [(fresh_parts D.kf.sk D.kf.out _ M' ι κ k).1, hNj]
      have hB := hacross (upd ρ' d.j x) (upd W d.j x) d.below hvB hmB hpB hskB
        (by rw [hsj, withExt_upd hjo.1]) (Or.inr trivial)
        (by rw [hNj]; simp [upd])
        (by
          have hkey : (sNext s ρ M ι κ).1 d.key = withExt s ρ' (sReq s ρ' M' ι κ) d.key := by
            rw [sNext_other D.kf.out]; simp only [withExt]
            rw [if_neg (by simpa [List.contains_iff_mem] using hko.1)]; simp [ρ', upd, Ne.symm hskk]
          rw [hNj]; simp only [upd, if_neg (Ne.symm D.jk), if_neg (Ne.symm hskk)]; exact hkey)
        (by rw [hNj])
      rw [hB, hNj]
      have hB' : evalE (upd (upd Nx.1 ce.e.sk v) d.j x) Nx.2 d.below = evalE (upd Nx.1 d.j x) Nx.2 d.below :=
        congrE _ _ _ _ (fun i hi => by
          have hik : i ≠ ce.e.sk := fun h' => by rw [h', hskB] at hi; cases hi
          simp only [upd]; split <;> simp_all)
      simp only [] at hB' ⊢
      rw [hB']
      refine sumBelow_congr _ (fun k _ => ?_)
      have hD := hacross (upd (upd ρ' d.j x) d.key k) (upd (upd W d.j x) d.key k) d.body hvD hmD hpD hskD
        (by rw [hsk k, withExt_upd hko.1, withExt_upd hjo.1]) (Or.inr trivial)
        (by rw [hNk k]; simp [upd, D.jk]) (by rw [hNk k]; simp [upd]) (by rw [hNk k])
      rw [hD, hNk k]
      exact congrE _ _ _ _ (fun i hi => by
          have hik : i ≠ ce.e.sk := fun h' => by rw [h', hskD] at hi; cases hi
          simp only [upd]; split <;> simp_all)
  · -- The goal's hypotheses hold where the frame is read.
    obtain ⟨hfav, hstp, hwr, hev⟩ := sTermsOk_parts P.terms
    intro c hc
    simp only [cStepGoal, sStepGoal, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, List.mem_map] at hc
    rcases hc with ((rfl | hc) | ⟨c', hc', rfl⟩) | rfl
    · rw [noReadsC W M0 M s.f.m.pre P.preR, congrC W ρ M s.f.m.pre (fun i hi => ?_)]
      · exact hp0
      · have hi1 := avoids_occ P.pre hi
        have hik : i ≠ ce.e.sk := fun h' => by rw [h'] at hi; simp [E'.spre] at hi
        simp only [W, withExt]
        rw [if_neg (fun h' => hi1 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.contains_iff_mem.mp h')))))]
        simp only [ρ', upd, if_neg hik]
    · exact facthyps_true s ce.e.finsts ce.e.pfinsts W M0 (fun f hf => (pfactsOk_parts P.facts f hf).2.2)
        (facts_frame s P.facts [ce.e.sk] (cPosts ds) (fun l hl => by simp [avoids, (skFresh_parts E'.skf).2.2.2.2.2.2 l hl]) A.facts
          (fun i hie hik => by
            simp only [W, withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hie)]; simp only [ρ', upd]; rw [if_neg (by simpa using hik)])
          (fun mp hmc hmp => by rw [hM0 mp hmp]; simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmc)]) hfa)
        (pfacts_frame s P.facts [ce.e.sk] (cPosts ds) (fun f hf => by simp [avoids, skFresh_pfacts E'.skf f hf]) A.pfacts
          (fun i hie hik => by
            simp only [W, withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hie)]; simp only [ρ', upd]; rw [if_neg (by simpa using hik)])
          (fun mp hmc hmp => by rw [hM0 mp hmp]; simp only [withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmc)]) hpf) c hc
    · have hA : evalC (sView s ρ' M' ι κ).1 (sView s ρ' M' ι κ).2 s.f.m.assume = true := by
        rw [hView]; dsimp only
        rw [sView_posts A F ρ M ι κ]; dsimp only
        rw [posts_evalC A.assume]
        rw [congrC _ (sView s ρ M ι κ).1 _ _ (fun i hi => by
          have hik : i ≠ ce.e.sk := fun h' => by rw [h', (skFresh_parts E'.skf).2.2.1] at hi; cases hi
          simp only [upd, if_neg hik])]
        exact ha
      have hallY : ∀ e' ∈ ps.map (·.e), e'.Holds W M0 := fun e' he' => by
        obtain ⟨ce', hce', rfl⟩ := List.mem_map.mp he'
        have E2 := entry_parts (P.entries ce' hce').1
        refine sentry_transfer (V := s.extVars) (MS := MS) (avoids_left E2.lx) E2.lm (fun i hi => ?_) (fun mp hmp => ?_)
          (sentry_upd (Or.inl (E'.slaw ce'.e (List.mem_map_of_mem hce'))) v (ih ce' hce'))
        · simp only [W, withExt]; rw [if_neg (by simpa [List.contains_iff_mem] using hi)]
        · rw [hM0 mp (hnotP mp hmp)]
          by_cases hc : mp ∈ s.carried
          · obtain ⟨d, hd, hdmp, hso⟩ := hMS mp hmp hc
            subst hdmp
            rw [withCnt_at hdm hd]
            funext x
            simp only [withCarried, List.contains_iff_mem.mpr hc, ite_true]
            exact hview d hd hso x
          · rw [withCnt_other (fun h' => by
              obtain ⟨d, hd, hdmp⟩ := List.mem_map.mp h'
              exact hc (by rw [← hdmp]; exact (decl_parts (P.decls d hd)).carried))]
            simp [withCarried, List.contains_iff_mem, hc]
      exact sframe_hyps s [] [] W M0 hs (sLaws (ps.map (·.e)) ce.e.pinsts) (sInsts (ps.map (·.e)) ce.e.insts ce.e.pinsts) ce.e.qinsts
        (fun l hl => by
          rcases List.mem_append.mp hl with hl | hl
          · obtain ⟨e', he', rfl⟩ := List.mem_map.mp hl; exact SEntry.holds_law (hallY e' he')
          · exact pairLaws_hold _ ce.e.pinsts hkk hallY l hl)
        (hH []) (fun _ _ => by simp [avoids]) (fun _ _ => by simp [avoids]) (fun _ _ => by simp [avoidsMaps]) hA (by simp [trueC, evalC, evalE]) c' hc'
    · have hrd' : ∀ mp k, evalE W M0 (stepRdS s (frameSub [] []) (frameRd [] getRd) mp k) = Mq mp (evalE W M0 k) := by
        intro mp k
        by_cases hmp : mp ∈ s.carried
        · have hne : lookup (fun w => w.1 == mp) s.every = none := lookup_none (fun w hw => by
            simp only [beq_eq_false_iff_ne]; intro h'; exact (hev w hw).2.2.2.2.1 (by rw [h']; exact hmp))
          have hnw : lookup (fun w : Nat × E × E => w.1 == mp) s.f.m.writes = none := lookup_none (fun w hw => by
            simp only [beq_eq_false_iff_ne]; intro h'; exact (hwr w hw).2 (by rw [h']; exact hmp))
          simp only [stepRdS, hne, stepRd, hnw]
          simp [frameRd, getRd, lookup, evalE, M0, Mq, withCarried, hmp]
        · rw [hD'.2 mp k hmp (by simp), hNext]; dsimp only; rw [hNx']
          simp only [Mq, withCarried]; rw [if_neg (by simpa [List.contains_iff_mem] using hmp)]
      simp only [evalC]
      rw [substR_evalC _ _ W M0 _ hrd', goalOf_agree (renLaw ds ce.e.law) ce.e.sk _ (X' := upd Nx.1 ce.e.sk v)
        (by rw [hD'.1 ce.e.sk hsk.1 hsk.2.1, hNext]; simp [hNx', upd]) (fun i hi => ?_)]
      · simpa using hn
      · have hi1 := avoids_occ E'.lx (by simpa [renLaw, occ_renC] using hi)
        rw [hD'.1 i (fun h' => hi1 (List.mem_append_left _ h')) (fun h' => hi1 (List.mem_append_right _ h')), hNext]
        simp [hNx']

/-! Soundness -/

/-- The induction rule with counts: for params that meet the precondition, maps that start as declared and functions
that meet the facts, every entry of an accepted proof holds in every reachable state (each request carrying its count
maps at their counts), each count map read as the state's count, a law about several keys at every value of its
further keys. -/
theorem cmachine_sound (s : SMachine) (ds : List CDecl) (ps : List CEntry) (h : checkCMachine s ds ps = true) :
    ∀ ρ M, CReach s ds ρ M → ∀ ce ∈ ps, ce.e.Holds ρ (withCnt ds ρ M) := by
  have P := cparts h
  have hfok := P.facts
  have hentry : ∀ e ∈ ps.map (·.e), cEntryOk s ds (ps.map (·.e)) e = true := fun e he => by
    obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp he; exact (P.entries ce hce).1
  have hfacts : ∀ {ρ : Nat → Nat} {M : Nat → Nat → Nat} {g : Nat}, skFresh s g = true → (∀ l ∈ s.facts, l.Holds ρ M) → ∀ w, ∀ l ∈ s.facts, l.Holds (upd ρ g w) M := by
    intro ρ M g hf hfa w
    exact facts_frame s hfok [g] [] (fun l hl => by simp [avoids, (skFresh_parts hf).2.2.2.2.2.2 l hl]) (fun _ _ => by simp [avoidsMaps])
      (fun i _ hig' => by simp only [upd]; rw [if_neg (by simpa using hig')]) (fun _ _ _ => rfl) hfa
  have hpfacts : ∀ {ρ : Nat → Nat} {M : Nat → Nat → Nat} {g : Nat}, skFresh s g = true → s.PFacts ρ M → ∀ w, s.PFacts (upd ρ g w) M := by
    intro ρ M g hf hpf w
    exact pfacts_frame s hfok [g] [] (fun f hfm => by simp [avoids, skFresh_pfacts hf f hfm]) (fun _ _ => by simp [avoidsMaps])
      (fun i _ hig' => by simp only [upd]; rw [if_neg (by simpa using hig')]) (fun _ _ _ => rfl) hpf
  have hpreu : ∀ {ρ : Nat → Nat} {M : Nat → Nat → Nat} {g : Nat}, occC g s.f.m.pre = false → evalC ρ M s.f.m.pre = true → ∀ w, evalC (upd ρ g w) M s.f.m.pre = true := by
    intro ρ M g hpg h0 w
    rw [congrC _ ρ M s.f.m.pre (fun i hi => by have hig' : i ≠ g := (fun h' => by rw [h', hpg] at hi; cases hi); simp only [upd, if_neg hig'])]; exact h0
  -- The counts read no further key.
  have hcg : ∀ ce ∈ ps, ∀ g ∈ ce.e.keys2, ∀ d ∈ ds, occE g d.below = false ∧ occE g d.body = false := fun ce hce g hg d hd =>
    ⟨((decl_parts (P.decls d hd)).ent ce.e (List.mem_map_of_mem hce) g (List.mem_cons_of_mem _ hg)).1,
      ((decl_parts (P.decls d hd)).ent ce.e (List.mem_map_of_mem hce) g (List.mem_cons_of_mem _ hg)).2.1⟩
  intro ρ M hr
  induction hr with
  | start ρ M hM h0 hfa hpf =>
    intro ce hce
    suffices hs : ∀ gs : List Nat, (∀ g ∈ gs, g ∈ ce.e.keys2) → ∀ ρ', evalC ρ' M s.f.m.pre = true → (∀ l ∈ s.facts, l.Holds ρ' M) →
        s.PFacts ρ' M → holdsOver ce.e.law (withCnt ds (applyS s.f.m.init ρ' M) M) gs (applyS s.f.m.init ρ' M) from
      hs ce.e.keys2 (fun g hg => hg) ρ h0 hfa hpf
    intro gs
    induction gs with
    | nil => intro _ ρ' hp hf hq; exact cstart_case s ds ps h ρ' M hM hp hf hq ce hce
    | cons g gs ih =>
      intro hsub ρ' hp hf hq w
      obtain ⟨hfr, hc, hpg, hig, _, _⟩ := key2_parts hentry (List.mem_map_of_mem hce) (hsub g List.mem_cons_self)
      have hI := (fresh_parts hfr hc ρ' M (fun _ => 0) (fun _ _ => 0) 0).2.2
      have := ih (fun g' hg' => hsub g' (List.mem_cons_of_mem _ hg')) (upd ρ' g w) (hpreu hpg hp w) (hfacts hfr hf w) (hpfacts hfr hq w)
      rw [applyS_upd hI (by simpa [List.all_eq_true] using hig), withCnt_upd (hcg ce hce g (hsub g List.mem_cons_self))] at this
      exact this
  | step ρ M ι κ hr hG ha ih =>
    intro ce hce
    suffices hs : ∀ gs : List Nat, (∀ g ∈ gs, g ∈ ce.e.keys2) → ∀ ρ', evalC ρ' M s.f.m.pre = true → (∀ l ∈ s.facts, l.Holds ρ' M) →
        s.PFacts ρ' M → (∀ ce' ∈ ps, ce'.e.Holds ρ' (withCnt ds ρ' M)) → GHolds ds (withInputs s.f.m.inputs ρ' ι) (withCarried s M κ) →
        evalC (sView s ρ' M ι κ).1 (sView s ρ' M ι κ).2 s.f.m.assume = true →
        holdsOver ce.e.law (withCnt ds (sNext s ρ' M ι κ).1 (sNext s ρ' M ι κ).2) gs (sNext s ρ' M ι κ).1 from
      hs ce.e.keys2 (fun g hg => hg) ρ (pre_sreach s P.pre P.preR (creach_sreach hr)) (facts_sreach s hfok (creach_sreach hr))
        (pfacts_sreach s hfok (creach_sreach hr)) ih hG ha
    intro gs
    induction gs with
    | nil => intro _ ρ' hp hf hq hi hg ha'; exact cstep_case s ds ps h ρ' M ι κ hp hf hq hi hg ha' ce hce
    | cons g gs ihg =>
      intro hsub ρ' hp hf hq hi hg ha' w
      have hgk := hsub g List.mem_cons_self
      obtain ⟨hfr, hc, hpg, _, hall, _⟩ := key2_parts hentry (List.mem_map_of_mem hce) hgk
      obtain ⟨hNext, hView, _⟩ := fresh_parts hfr hc ρ' M ι κ w
      have hgi := (fresh_out hc).2.2.2.2.1
      have := ihg (fun g' hg' => hsub g' (List.mem_cons_of_mem _ hg')) (upd ρ' g w) (hpreu hpg hp w) (hfacts hfr hf w) (hpfacts hfr hq w)
        (fun ce' hce' => by
          rw [withCnt_upd (hcg ce hce g hgk)]
          exact sentry_upd (hall ce'.e (List.mem_map_of_mem hce')) w (hi ce' hce'))
        (fun d hd x => by
          rw [hg d hd x, withInputs_upd hgi, cntOf_upd (hcg ce hce g hgk d hd).1 (hcg ce hce g hgk d hd).2])
        (by
          rw [hView]; dsimp only
          rw [congrC _ (sView s ρ' M ι κ).1 _ _ (fun i hi => by
            have hig' : i ≠ g := fun h' => by rw [h', (skFresh_parts hfr).2.2.1] at hi; cases hi
            simp only [upd, if_neg hig'])]
          exact ha')
      rw [hNext] at this; dsimp only at this
      rw [withCnt_upd (hcg ce hce g hgk)] at this
      exact this

/-- `CReach` is the rule's own runs: at any state and request, the maps the request carries can be set at the count
maps to their counts (what the runtimes compute) and kept as they are elsewhere. -/
theorem counts_exist (s : SMachine) (ds : List CDecl) (hd : cDistinct (cMaps ds) = true) (hc : ∀ d ∈ ds, d.mp ∈ s.carried)
    (hav : ∀ d ∈ ds, avoidsMapsE (cMaps ds) d.below = true ∧ avoidsMapsE (cMaps ds) d.body = true)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    ∃ κ' : Nat → Nat → Nat, (∀ mp, mp ∉ cMaps ds → withCarried s M κ' mp = withCarried s M κ mp)
      ∧ GHolds ds (withInputs s.f.m.inputs ρ ι) (withCarried s M κ') := by
  let X := withInputs s.f.m.inputs ρ ι
  let κ' := withCnt ds X (withCarried s M κ)
  have hoff : ∀ mp, mp ∉ cMaps ds → withCarried s M κ' mp = withCarried s M κ mp := by
    intro mp hmp
    simp only [withCarried]; split
    · rename_i hcm
      show withCnt ds X (withCarried s M κ) mp = κ mp
      rw [withCnt_other hmp]; simp only [withCarried, hcm, ite_true]
    · rfl
  refine ⟨κ', hoff, fun d hdm x => ?_⟩
  have hcd : s.carried.contains d.mp = true := List.contains_iff_mem.mpr (hc d hdm)
  show (if s.carried.contains d.mp then κ' d.mp else M d.mp) x = _
  rw [if_pos hcd]
  show withCnt ds X (withCarried s M κ) d.mp x = _
  rw [withCnt_at hd hdm]
  unfold cntOf
  have hB : evalE (upd X d.j x) (withCarried s M κ) d.below = evalE (upd X d.j x) (withCarried s M κ') d.below :=
    congrME _ _ _ d.below (fun mp hm => (hoff mp (avoidsMapsE_occ (hav d hdm).1 hm)).symm)
  rw [hB]
  exact sumBelow_congr _ (fun k _ => congrME _ _ _ d.body (fun mp hm => (hoff mp (avoidsMapsE_occ (hav d hdm).2 hm)).symm))

end Kern

#print axioms Kern.mc_sound
#print axioms Kern.cmachine_sound
#print axioms Kern.counts_exist

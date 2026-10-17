import Progress
/-!
History: kernel.ts's `historyMachine`, the rule for a machine that keeps a log of the requests it accepts.

A machine with a history (`HMachine`) is a machine with maps and flags plus:
- `keep`: whether a request is appended to the history (read with the flags decided);
- `record`, `rvars`: the recorded inputs, and the variables (r.f) a sum or query reads them as;
- `sums`: state variables defined as the sum, over the history, of a term of the record and the params;
- `queries`: inputs whose value at each request is the sum, over the history before it, of a term of the record, the
  params and the request's other (plain) inputs;
- `rels`: relations (when, a, b): `when` (params and plain inputs) implies a ≤ b, with a and b homogeneous (+ and × by
  a constant, no constant term) over sums and queries.

`HReach` is the history semantics: the history is a list of request environments (sums and queries only read their
recorded inputs from them), every sum is recomputed from it, every query is computed from it at the request.
Lean builds what kernel.ts builds: the plain machine (`HMachine.plain`: each sum a state variable from 0, plus its term
at the request when the request is kept; the relations conjoined to the assumption) and one goal per relation, a ≤ b
for a single record (`recordGoal`), and checks kernel.ts's side conditions (`histOk`). `hmachine_sound`: if those goals
check and the plain machine's proof checks (`checkFMMachine`), every law holds in every state the history semantics
reaches. The step from one record to the whole history (`homog_sum`, `sum_le_map`): a homogeneous term of sums over one
list is the sum of the term over its elements.
-/
namespace Kern
open Cert

structure HMachine where
  f : FMMachine                 -- the machine without its history; its inputs include the queries
  keep : C                      -- whether the request is appended to the history (flags decided)
  record : List Nat             -- the recorded inputs
  rvars : List Nat              -- the record's fields as variables, one per recorded input
  sums : List (Nat × E)         -- a sum's state variable and its term over the fields and the params
  queries : List (Nat × E)      -- a query's input variable and its term over the fields, params and plain inputs
  rels : List (C × E × E)       -- (when, a, b): a ≤ b whenever `when` holds

-- A field reads its recorded input from the record; every other variable reads ρ.
def fieldEnv (h : HMachine) (rec ρ : Nat → Nat) : Nat → Nat := fun i =>
  match lookup (fun p => p.1 == i) (h.rvars.zip h.record) with
  | some p => rec p.2
  | none => ρ i

def sumAt (h : HMachine) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hist : List (Nat → Nat)) (g : E) : Nat :=
  (hist.map fun rec => evalE (fieldEnv h rec ρ) M g).sum

def withSums (h : HMachine) (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hist : List (Nat → Nat)) : Nat → Nat := fun i =>
  match assoc h.sums i with
  | some g => sumAt h ρ M hist g
  | none => ρ i

def withQueries (h : HMachine) (X : Nat → Nat) (M : Nat → Nat → Nat) (hist : List (Nat → Nat)) : Nat → Nat := fun i =>
  match assoc h.queries i with
  | some g => sumAt h X M hist g
  | none => X i

def plainInputs (h : HMachine) : List Nat := h.f.m.inputs.filter fun i => !(h.queries.map (·.1)).contains i

-- The request as the step reads it: plain inputs from ι, queries from the history, flags decided.
def reqEnv (h : HMachine) (ρ ι : Nat → Nat) (M : Nat → Nat → Nat) (hist : List (Nat → Nat)) : Nat → Nat :=
  decideFlags h.f.flags (withQueries h (withInputs (plainInputs h) ρ ι) M hist) M

def kept (h : HMachine) (X : Nat → Nat) (M : Nat → Nat → Nat) (hist : List (Nat → Nat)) : List (Nat → Nat) :=
  if evalC X M h.keep then hist ++ [X] else hist

inductive HReach (h : HMachine) : (Nat → Nat) → (Nat → Nat → Nat) → List (Nat → Nat) → Prop
  | start (ρ : Nat → Nat) (M : Nat → Nat → Nat) : StartMaps h.f.m M → evalC ρ M h.f.m.pre = true →
      HReach h (withSums h (applyS h.f.m.init ρ M) M []) M []
  | step (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hist : List (Nat → Nat)) (ι : Nat → Nat) : HReach h ρ M hist →
      evalC (reqEnv h ρ ι M hist) M h.f.m.assume = true →
      HReach h (withSums h (applyS h.f.m.step (reqEnv h ρ ι M hist) M) M (kept h (reqEnv h ρ ι M hist) M hist))
        (writeMaps h.f.m.writes (reqEnv h ρ ι M hist) M) (kept h (reqEnv h ρ ι M hist) M hist)

/-! What Lean builds -/

def fieldSub (h : HMachine) : List (Nat × E) := (h.rvars.zip h.record).map fun p => (p.1, .var p.2)
def TRUEC : C := .le (.const 0) (.const 0)
def relC (r : C × E × E) : C := .or (.not r.1) (.le r.2.1 r.2.2)
def relsC (rs : List (C × E × E)) : C := rs.foldr (fun r acc => .and (relC r) acc) TRUEC
def sumStep (h : HMachine) (s : Nat) (g : E) : E := .add (.var s) (.ite h.keep (substE (fieldSub h) g) (.const 0))

def HMachine.plain (h : HMachine) : FMMachine :=
  { m := { h.f.m with
      init := h.f.m.init ++ h.sums.map fun p => (p.1, .const 0)
      step := h.f.m.step ++ h.sums.map fun p => (p.1, sumStep h p.1 p.2)
      assume := .and h.f.m.assume (relsC h.rels) }
    flags := h.f.flags }

-- One record: the relation's two sides with each sum and query read as its term at that record.
def recordGoal (h : HMachine) (r : C × E × E) : List C :=
  [h.f.m.pre, r.1, .not (.le (substE (h.sums ++ h.queries) r.2.1) (substE (h.sums ++ h.queries) r.2.2))]

mutual
def homog (vs : List Nat) : E → Bool
  | .var i => vs.contains i
  | .add a b => homog vs a && homog vs b
  | .mul _ a => homog vs a
  | _ => false
def homogC (_vs : List Nat) : C → Bool
  | _ => false
end


-- kernel.ts's checks: sums read the fields and params, queries also the plain inputs, `when` the params and plain
-- inputs; nothing reads a map; the names don't collide; the precondition reads no input, flag or field.
def histOk (h : HMachine) : Bool :=
  let ins := h.f.m.inputs
  let qs := h.queries.map (·.1)
  let ss := h.sums.map (·.1)
  let st := h.f.m.init.map (·.1) ++ h.f.m.step.map (·.1)
  let fv := flagVars h.f.flags
  h.rvars.length == h.record.length
  && qs.all (fun q => ins.contains q)
  && h.record.all (fun i => (plainInputs h).contains i)
  && ss.all (fun s => !(ins ++ st ++ fv ++ h.rvars).contains s)
  && h.rvars.all (fun v => !(ins ++ st ++ fv).contains v)
  && fv.all (fun v => !ins.contains v)
  && h.sums.all (fun p => avoidsE (ins ++ st ++ ss ++ fv) p.2 && !readsE p.2)
  && h.queries.all (fun p => avoidsE (qs ++ st ++ ss ++ fv) p.2 && !readsE p.2)
  && h.rels.all (fun r => avoids (qs ++ st ++ ss ++ fv ++ h.rvars) r.1 && !readsC r.1 && homog (ss ++ qs) r.2.1 && homog (ss ++ qs) r.2.2)
  && avoids (ins ++ fv ++ h.rvars) h.f.m.pre && !readsC h.f.m.pre

-- Per relation, (table, tree) for its record goal, in order; then the plain machine's proof.
def checkHMachine (h : HMachine) (ps : List MEntry) (rs : List (List VDef × Tree)) : Bool :=
  histOk h && rs.length == h.rels.length && (h.rels.zip rs).all (fun p => checkGoal ⟨p.2.1, recordGoal h p.1⟩ p.2.2)
    && checkFMMachine h.plain ps

/-! Lists and sums -/

theorem sum_map_add {α : Type} (f g : α → Nat) : ∀ l : List α, (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum
  | [] => rfl
  | a :: as => by simp only [List.map_cons, List.sum_cons, sum_map_add f g as]; omega

theorem sum_map_mul {α : Type} (k : Nat) (f : α → Nat) : ∀ l : List α, (l.map fun x => k * f x).sum = k * (l.map f).sum
  | [] => by simp
  | a :: as => by simp only [List.map_cons, List.sum_cons, sum_map_mul k f as, Nat.mul_add]

theorem sum_le_map {α : Type} (f g : α → Nat) : ∀ l : List α, (∀ x ∈ l, f x ≤ g x) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | a :: as, h => by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self) (sum_le_map f g as (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem zip_mem_left {α β : Type} : ∀ (l1 : List α) (l2 : List β), l1.length = l2.length → ∀ a ∈ l1, ∃ b, (a, b) ∈ l1.zip l2
  | [], _, _, a, ha => by simp at ha
  | _ :: _, [], hl, _, _ => by simp at hl
  | x :: xs, y :: ys, hl, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨y, by simp⟩
    · obtain ⟨b, hb⟩ := zip_mem_left xs ys (by simpa using hl) a ha
      exact ⟨b, by simp [hb]⟩

-- A homogeneous term of variables that are each a sum over one list is the sum of the term over the list.
mutual
theorem homog_sum {vs : List Nat} (M : Nat → Nat → Nat) (X : Nat → Nat) (F : List (Nat → Nat))
    (hX : ∀ v ∈ vs, X v = (F.map fun Y => Y v).sum) : (a : E) → homog vs a = true →
    evalE X M a = (F.map fun Y => evalE Y M a).sum
  | .var i, h => by simp only [homog, List.contains_iff_mem] at h; simp only [evalE]; exact hX i h
  | .add a b, h => by
    simp only [homog, Bool.and_eq_true] at h
    simp only [evalE, homog_sum M X F hX a h.1, homog_sum M X F hX b h.2]
    exact (sum_map_add (fun Y => evalE Y M a) (fun Y => evalE Y M b) F).symm
  | .mul k a, h => by
    simp only [homog] at h
    simp only [evalE, homog_sum M X F hX a h]
    exact (sum_map_mul k (fun Y => evalE Y M a) F).symm
  | .const _, h => by simp [homog] at h
  | .sub _ _, h => by simp [homog] at h
  | .min _ _, h => by simp [homog] at h
  | .max _ _, h => by simp [homog] at h
  | .prod _ _, h => by simp [homog] at h
  | .ite _ _ _, h => by simp [homog] at h
  | .get _ _, h => by simp [homog] at h
theorem homog_sumC {vs : List Nat} (_M : Nat → Nat → Nat) (X : Nat → Nat) (F : List (Nat → Nat))
    (_hX : ∀ v ∈ vs, X v = (F.map fun Y => Y v).sum) : (c : C) → homogC vs c = true → True
  | _, _ => trivial
end

/-! Lookups -/

theorem assoc_append (l1 l2 : List (Nat × E)) (i : Nat) :
    assoc (l1 ++ l2) i = match assoc l1 i with | some e => some e | none => assoc l2 i := by
  simp only [assoc, lookup_append]
  cases lookup (fun p => p.1 == i) l1 <;> rfl

theorem assoc_map_key (σ : List (Nat × E)) (F : Nat → E → E) (i : Nat) :
    assoc (σ.map fun p => (p.1, F p.1 p.2)) i = (assoc σ i).map (F i) := by
  simp only [assoc, lookup_map_pred]
  cases hl : lookup (fun p => p.1 == i) σ with
  | none => rfl
  | some p =>
    have := (lookup_some hl).2
    simp only [beq_iff_eq] at this
    subst this; rfl

theorem assoc_some_of_mem {σ : List (Nat × E)} {i : Nat} (h : i ∈ σ.map (·.1)) : ∃ e, assoc σ i = some e := by
  cases ha : assoc σ i with
  | some e => exact ⟨e, rfl⟩
  | none =>
    simp only [assoc, Option.map_eq_none_iff] at ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    have := lookup_none_all ha p hp
    simp at this

theorem fieldEnv_other (h : HMachine) {i : Nat} (hi : i ∉ h.rvars) (rec ρ : Nat → Nat) : fieldEnv h rec ρ i = ρ i := by
  simp only [fieldEnv]
  cases hl : lookup (fun p => p.1 == i) (h.rvars.zip h.record) with
  | none => rfl
  | some p =>
    have ⟨hm, hp⟩ := lookup_some hl
    simp only [beq_iff_eq] at hp
    exact absurd (hp ▸ (List.of_mem_zip hm).1) hi

theorem fieldSub_apply (h : HMachine) (X : Nat → Nat) (M : Nat → Nat → Nat) : applyS (fieldSub h) X M = fieldEnv h X X := by
  funext i
  simp only [applyS, fieldSub, assoc, lookup_map_pred, fieldEnv]
  cases lookup (fun p => p.1 == i) (h.rvars.zip h.record) <;> rfl

theorem sumAt_congr (h : HMachine) {ρ ρ' : Nat → Nat} (M : Nat → Nat → Nat) (hist : List (Nat → Nat)) (g : E)
    (hag : ∀ i, occE i g = true → ρ i = ρ' i) : sumAt h ρ M hist g = sumAt h ρ' M hist g := by
  unfold sumAt
  congr 1
  apply List.map_congr_left
  intro rec _
  exact congrE _ _ M g (fun i hi => by
    simp only [fieldEnv]; split
    · rfl
    · exact hag i hi)

theorem sumAt_maps (h : HMachine) (ρ : Nat → Nat) (M M' : Nat → Nat → Nat) (hist : List (Nat → Nat)) (g : E)
    (hr : readsE g = false) : sumAt h ρ M hist g = sumAt h ρ M' hist g := by
  unfold sumAt
  congr 1
  apply List.map_congr_left
  intro rec _
  exact noReadsE _ M M' g hr


/-! The side conditions, unpacked -/

structure HOk (h : HMachine) : Prop where
  len : h.rvars.length = h.record.length
  qs_in : ∀ q ∈ h.queries.map (·.1), q ∈ h.f.m.inputs
  rec_in : ∀ i ∈ h.record, i ∈ plainInputs h
  ss_out : ∀ s ∈ h.sums.map (·.1), s ∉ h.f.m.inputs ∧ s ∉ h.f.m.init.map (·.1) ∧ s ∉ h.f.m.step.map (·.1) ∧
    s ∉ flagVars h.f.flags ∧ s ∉ h.rvars
  rv_out : ∀ v ∈ h.rvars, v ∉ h.f.m.inputs ∧ v ∉ h.f.m.init.map (·.1) ∧ v ∉ h.f.m.step.map (·.1) ∧ v ∉ flagVars h.f.flags
  fv_out : ∀ v ∈ flagVars h.f.flags, v ∉ h.f.m.inputs
  sums_ok : ∀ p ∈ h.sums, avoidsE (h.f.m.inputs ++ (h.f.m.init.map (·.1) ++ h.f.m.step.map (·.1)) ++ h.sums.map (·.1)
    ++ flagVars h.f.flags) p.2 = true ∧ readsE p.2 = false
  queries_ok : ∀ p ∈ h.queries, avoidsE (h.queries.map (·.1) ++ (h.f.m.init.map (·.1) ++ h.f.m.step.map (·.1))
    ++ h.sums.map (·.1) ++ flagVars h.f.flags) p.2 = true ∧ readsE p.2 = false
  rels_ok : ∀ r ∈ h.rels, avoids (h.queries.map (·.1) ++ (h.f.m.init.map (·.1) ++ h.f.m.step.map (·.1)) ++ h.sums.map (·.1)
    ++ flagVars h.f.flags ++ h.rvars) r.1 = true ∧ homog (h.sums.map (·.1) ++ h.queries.map (·.1)) r.2.1 = true ∧
    homog (h.sums.map (·.1) ++ h.queries.map (·.1)) r.2.2 = true
  pre_ok : avoids (h.f.m.inputs ++ flagVars h.f.flags ++ h.rvars) h.f.m.pre = true ∧ readsC h.f.m.pre = false

theorem histOk_sound {h : HMachine} (hc : histOk h = true) : HOk h := by
  simp only [histOk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlen, hqs⟩, hrec⟩, hss⟩, hrv⟩, hfv⟩, hsums⟩, hq⟩, hrels⟩, hpre⟩, hpr⟩ := hc
  simp only [List.all_eq_true] at hqs hrec hss hrv hfv hsums hq hrels
  refine ⟨by simpa using hlen, fun q hq' => by simpa using hqs q hq', fun i hi => by simpa using hrec i hi, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨hpre, by simpa using hpr⟩⟩
  · intro s hs; have := hss s hs; simpa [not_or] using this
  · intro v hv; have := hrv v hv; simpa [not_or] using this
  · intro v hv; have := hfv v hv; simpa using this
  · intro p hp; have := hsums p hp; simp only [Bool.and_eq_true] at this; exact ⟨this.1, by simpa using this.2⟩
  · intro p hp; have := hq p hp; simp only [Bool.and_eq_true] at this; exact ⟨this.1, by simpa using this.2⟩
  · intro r hr; have := hrels r hr; simp only [Bool.and_eq_true] at this; exact ⟨this.1.1.1, this.1.2, this.2⟩

/-! The history semantics simulated by the plain machine -/

theorem withSums_other (h : HMachine) {i : Nat} (hi : i ∉ h.sums.map (·.1)) (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (hist : List (Nat → Nat)) : withSums h ρ M hist i = ρ i := by
  simp only [withSums, assoc_none_of hi]

theorem plain_sub (h : HMachine) : plainInputs h ⊆ h.f.m.inputs := fun _ hi => (List.mem_filter.mp hi).1

theorem reqEnv_other {h : HMachine} (ok : HOk h) {i : Nat} (hin : i ∉ h.f.m.inputs) (hf : i ∉ flagVars h.f.flags)
    (ρ ι : Nat → Nat) (M : Nat → Nat → Nat) (hist : List (Nat → Nat)) : reqEnv h ρ ι M hist i = ρ i := by
  simp only [reqEnv]
  rw [decide_other hf]
  simp only [withQueries, assoc_none_of (fun hq => hin (ok.qs_in i hq))]
  exact withInputs_other (fun hp => hin (plain_sub h hp)) ρ ι

-- In a reached state every sum is its sum over the history.
theorem hsum_of_hreach {h : HMachine} (ok : HOk h) : ∀ {ρ M hist}, HReach h ρ M hist →
    ∀ s g, assoc h.sums s = some g → ρ s = sumAt h ρ M hist g := by
  have key : ∀ ρ1 M0 M hist s g, assoc h.sums s = some g →
      withSums h ρ1 M0 hist s = sumAt h (withSums h ρ1 M0 hist) M hist g := by
    intro ρ1 M0 M hist s g hs
    obtain ⟨p, hp, hpg⟩ : ∃ p ∈ h.sums, p.2 = g := by
      simp only [assoc, Option.map_eq_some_iff] at hs
      obtain ⟨p, hl, rfl⟩ := hs
      exact ⟨p, (lookup_some hl).1, rfl⟩
    have hg := ok.sums_ok p hp
    rw [hpg] at hg
    simp only [withSums, hs]
    rw [sumAt_maps h ρ1 M0 M hist g hg.2]
    exact sumAt_congr h M hist g (fun i hi => by
      have := avoidsE_occ hg.1 hi
      simp only [List.mem_append, not_or] at this
      exact (withSums_other h this.1.2 ρ1 M0 hist).symm)
  intro ρ M hist hr
  cases hr with
  | start ρ0 M h0 hp => exact fun s g hs => key _ M M [] s g hs
  | step ρ0 M0 hist0 ι _ _ => exact fun s g hs => key _ M0 _ _ s g hs

theorem pre_fmreach (f : FMMachine) (ps : List MEntry) (h : checkFMMachine f ps = true) :
    ∀ {ρ M}, FMReach f ρ M → evalC ρ M f.m.pre = true := by
  intro ρ M hr
  simp only [checkFMMachine, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hf, hpre⟩, _⟩, hc⟩ := h
  simp only [checkMMachine, Bool.and_eq_true] at hc
  obtain ⟨⟨hav, hrd⟩, _⟩ := hc
  obtain ⟨ρ₀, hr₀, hag⟩ := fmreach_plain f hf hr
  have := pre_mreach (m := f.plain) hav (by simpa using hrd) hr₀
  rw [congrC ρ ρ₀ M f.m.pre (fun j hj => hag j (avoids_occ hpre hj))]
  exact this

theorem relsC_true (X : Nat → Nat) (M : Nat → Nat → Nat) :
    ∀ rs : List (C × E × E), (∀ r ∈ rs, evalC X M (relC r) = true) → evalC X M (relsC rs) = true
  | [], _ => by simp [relsC, TRUEC, evalC, evalE]
  | r :: rs, hr => by
    simp only [relsC, List.foldr_cons, evalC, Bool.and_eq_true]
    exact ⟨hr r List.mem_cons_self, relsC_true X M rs (fun r' h' => hr r' (List.mem_cons_of_mem _ h'))⟩

-- At a reached state where the precondition holds, every relation holds of the request.
theorem rels_hold {h : HMachine} (ok : HOk h)
    (hrs : ∀ r ∈ h.rels, ∃ tt : List VDef × Tree, checkGoal ⟨tt.1, recordGoal h r⟩ tt.2 = true)
    {ρ : Nat → Nat} {M : Nat → Nat → Nat} {hist : List (Nat → Nat)}
    (hsum : ∀ s g, assoc h.sums s = some g → ρ s = sumAt h ρ M hist g) (hpre : evalC ρ M h.f.m.pre = true)
    (ι : Nat → Nat) : evalC (reqEnv h ρ ι M hist) M (relsC h.rels) = true := by
  apply relsC_true
  intro r hr
  obtain ⟨tt, hck⟩ := hrs r hr
  obtain ⟨hwav, ha, hb⟩ := ok.rels_ok r hr
  let X := reqEnv h ρ ι M hist
  let X0 := withInputs (plainInputs h) ρ ι
  let gsub := h.sums ++ h.queries
  let F := hist.map fun rec => applyS gsub (fieldEnv h rec X) M
  -- Each sum and each query is its sum over the history, at X.
  have hX : ∀ v ∈ h.sums.map (·.1) ++ h.queries.map (·.1), X v = (F.map fun Y => Y v).sum := by
    intro v hv
    have hF : ∀ g, assoc gsub v = some g → (F.map fun Y => Y v).sum = sumAt h X M hist g := by
      intro g hg
      simp only [F, List.map_map, sumAt]
      congr 1
      apply List.map_congr_left
      intro rec _
      simp only [Function.comp, applyS, hg]
    by_cases hs : v ∈ h.sums.map (·.1)
    · obtain ⟨g, hg⟩ := assoc_some_of_mem hs
      have hgs : assoc gsub v = some g := by simp only [gsub, assoc_append, hg]
      rw [hF g hgs]
      obtain ⟨p, hp, hpg⟩ : ∃ p ∈ h.sums, p.2 = g := by
        simp only [assoc, Option.map_eq_some_iff] at hg
        obtain ⟨p, hl, rfl⟩ := hg
        exact ⟨p, (lookup_some hl).1, rfl⟩
      have hok := ok.sums_ok p hp
      rw [hpg] at hok
      have ⟨hvin, _, _, hvf, _⟩ := ok.ss_out v hs
      show reqEnv h ρ ι M hist v = _
      rw [reqEnv_other ok hvin hvf, hsum v g hg]
      exact sumAt_congr h M hist g (fun i hi => by
        have := avoidsE_occ hok.1 hi
        simp only [List.mem_append, not_or] at this
        exact (reqEnv_other ok this.1.1.1 this.2 ρ ι M hist).symm)
    · have hq : v ∈ h.queries.map (·.1) := by
        rcases List.mem_append.mp hv with h1 | h1
        · exact absurd h1 hs
        · exact h1
      obtain ⟨g, hg⟩ := assoc_some_of_mem hq
      have hgs : assoc gsub v = some g := by simp only [gsub, assoc_append, assoc_none_of hs, hg]
      rw [hF g hgs]
      obtain ⟨p, hp, hpg⟩ : ∃ p ∈ h.queries, p.2 = g := by
        simp only [assoc, Option.map_eq_some_iff] at hg
        obtain ⟨p, hl, rfl⟩ := hg
        exact ⟨p, (lookup_some hl).1, rfl⟩
      have hok := ok.queries_ok p hp
      rw [hpg] at hok
      have hvf : v ∉ flagVars h.f.flags := fun hf => ok.fv_out v hf (ok.qs_in v hq)
      show decideFlags h.f.flags (withQueries h X0 M hist) M v = _
      rw [decide_other hvf]
      simp only [withQueries, hg]
      exact sumAt_congr h M hist g (fun i hi => by
        have := avoidsE_occ hok.1 hi
        simp only [List.mem_append, not_or] at this
        show X0 i = decideFlags h.f.flags (withQueries h X0 M hist) M i
        rw [decide_other this.2]
        simp only [withQueries, assoc_none_of this.1.1.1])
  simp only [relC, evalC, Bool.or_eq_true, Bool.not_eq_true']
  by_cases hw : evalC X M r.1 = true
  · right
    simp only [decide_eq_true_eq]
    rw [homog_sum M X F hX r.2.1 ha, homog_sum M X F hX r.2.2 hb]
    apply sum_le_map
    intro Y hY
    obtain ⟨rec, _, rfl⟩ := List.mem_map.mp hY
    have hs := sound ⟨tt.1, recordGoal h r⟩ tt.2 hck (fieldEnv h rec X) M
    have hE : ∀ c, avoids h.rvars c = true → evalC (fieldEnv h rec X) M c = evalC X M c := fun c hc =>
      congrC _ _ M c (fun i hi => fieldEnv_other h (avoids_occ hc hi) rec X)
    have hpreX : evalC X M h.f.m.pre = true := by
      have hp := ok.pre_ok.1
      rw [congrC X ρ M h.f.m.pre (fun i hi => by
        have := avoids_occ hp hi
        simp only [List.mem_append, not_or] at this
        exact reqEnv_other ok this.1.1 this.1.2 ρ ι M hist)]
      exact hpre
    apply Decidable.byContradiction
    intro hlt
    apply hs
    intro c hc
    simp only [recordGoal, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · rw [hE _ (by
        have hp := ok.pre_ok.1
        simp only [avoids, List.all_eq_true] at hp ⊢
        intro i hi; exact hp i (by simp [hi]))]
      exact hpreX
    · rw [hE _ (by
        simp only [avoids, List.all_eq_true] at hwav ⊢
        intro i hi; exact hwav i (by simp [hi]))]
      exact hw
    · simp only [evalC, subst_evalE, Bool.not_eq_true', decide_eq_false_iff_not]
      exact hlt
  · left; simpa using hw

theorem start_eq {h : HMachine} (ok : HOk h) (ρ : Nat → Nat) (M : Nat → Nat → Nat) :
    applyS h.plain.m.init ρ M = withSums h (applyS h.f.m.init ρ M) M [] := by
  funext i
  show applyS (h.f.m.init ++ h.sums.map fun p => (p.1, .const 0)) ρ M i = _
  simp only [applyS, assoc_append, withSums]
  cases hs : assoc h.sums i with
  | some g =>
    have hi : i ∉ h.f.m.init.map (·.1) := (ok.ss_out i (assoc_mem hs)).2.1
    simp only [assoc_none_of hi, assoc_map_snd (σ := h.sums) (g := fun _ => .const 0), hs, Option.map_some, evalE,
      sumAt, List.map_nil, List.sum_nil]
  | none =>
    cases hi : assoc h.f.m.init i with
    | some e => rfl
    | none => simp only [assoc_map_snd (σ := h.sums) (g := fun _ => .const 0), hs, Option.map_none]

theorem inputs_eq {h : HMachine} (ok : HOk h) (ρ ι : Nat → Nat) (M : Nat → Nat → Nat) (hist : List (Nat → Nat)) :
    withInputs h.f.m.inputs ρ (withQueries h (withInputs (plainInputs h) ρ ι) M hist)
      = withQueries h (withInputs (plainInputs h) ρ ι) M hist := by
  funext i
  by_cases hin : i ∈ h.f.m.inputs
  · simp only [withInputs, List.contains_iff_mem, hin, ite_true]
  · rw [withInputs_other hin]
    simp only [withQueries, assoc_none_of (fun hq => hin (ok.qs_in i hq))]
    exact (withInputs_other (fun hp => hin (plain_sub h hp)) ρ ι).symm

theorem step_eq {h : HMachine} (ok : HOk h) (X : Nat → Nat) (M : Nat → Nat → Nat) (hist : List (Nat → Nat))
    (hX : ∀ s g, assoc h.sums s = some g → X s = sumAt h X M hist g) :
    applyS h.plain.m.step X M = withSums h (applyS h.f.m.step X M) M (kept h X M hist) := by
  funext i
  show applyS (h.f.m.step ++ h.sums.map fun p => (p.1, sumStep h p.1 p.2)) X M i = _
  cases hs : assoc h.sums i with
  | some g =>
    have hmem := assoc_mem hs
    have hi : i ∉ h.f.m.step.map (·.1) := (ok.ss_out i hmem).2.2.1
    obtain ⟨p, hp, hpg⟩ : ∃ p ∈ h.sums, p.2 = g := by
      simp only [assoc, Option.map_eq_some_iff] at hs
      obtain ⟨p, hl, rfl⟩ := hs
      exact ⟨p, (lookup_some hl).1, rfl⟩
    have hok := ok.sums_ok p hp
    rw [hpg] at hok
    have hA : assoc (h.f.m.step ++ h.sums.map fun p => (p.1, sumStep h p.1 p.2)) i = some (sumStep h i g) := by
      rw [assoc_append, assoc_none_of hi]
      show assoc (h.sums.map fun p => (p.1, sumStep h p.1 p.2)) i = _
      rw [assoc_map_key h.sums (sumStep h), hs]; rfl
    have hL : applyS (h.f.m.step ++ h.sums.map fun p => (p.1, sumStep h p.1 p.2)) X M i = evalE X M (sumStep h i g) := by
      simp only [applyS, hA]
    have hR : withSums h (applyS h.f.m.step X M) M (kept h X M hist) i = sumAt h (applyS h.f.m.step X M) M (kept h X M hist) g := by
      simp only [withSums, hs]
    rw [hL, hR]
    -- The old records read alike after the step: the term reads no state variable.
    have hcg : ∀ hs', sumAt h (applyS h.f.m.step X M) M hs' g = sumAt h X M hs' g := fun hs' =>
      sumAt_congr h M hs' g (fun j hj => by
        have := avoidsE_occ hok.1 hj
        simp only [List.mem_append, not_or] at this
        exact applyS_other this.1.1.2.2 X M)
    rw [hcg]
    simp only [sumStep, evalE, subst_evalE, fieldSub_apply]
    rw [hX i g hs]
    unfold kept
    by_cases hk : evalC X M h.keep = true
    · simp [hk, sumAt, List.map_append, List.sum_append]
    · simp [hk]
  | none =>
    have hR : withSums h (applyS h.f.m.step X M) M (kept h X M hist) i = applyS h.f.m.step X M i := by
      simp only [withSums, hs]
    rw [hR]
    have hB : assoc (h.sums.map fun p => (p.1, sumStep h p.1 p.2)) i = none := by
      rw [assoc_map_key h.sums (sumStep h), hs]; rfl
    simp only [applyS, assoc_append]
    cases hi : assoc h.f.m.step i with
    | some e => rfl
    | none => simp only [hB]

theorem hreach_fmreach {h : HMachine} (ps : List MEntry) (ok : HOk h)
    (hrs : ∀ r ∈ h.rels, ∃ tt : List VDef × Tree, checkGoal ⟨tt.1, recordGoal h r⟩ tt.2 = true)
    (hfm : checkFMMachine h.plain ps = true) : ∀ {ρ M hist}, HReach h ρ M hist → FMReach h.plain ρ M := by
  intro ρ M hist hr
  induction hr with
  | start ρ M hM h0 =>
    rw [← start_eq ok]
    exact FMReach.start (f := h.plain) ρ M hM h0
  | step ρ M hist ι hr ha ih =>
    have hsum := hsum_of_hreach ok hr
    have hpre := pre_fmreach h.plain ps hfm ih
    have hass : evalC (decideFlags h.plain.flags (withInputs h.plain.m.inputs ρ
        (withQueries h (withInputs (plainInputs h) ρ ι) M hist)) M) M h.plain.m.assume = true := by
      show evalC (decideFlags h.f.flags (withInputs h.f.m.inputs ρ (withQueries h (withInputs (plainInputs h) ρ ι) M hist)) M) M
        (.and h.f.m.assume (relsC h.rels)) = true
      rw [inputs_eq ok]
      simp only [evalC, Bool.and_eq_true]
      exact ⟨ha, rels_hold ok hrs hsum hpre ι⟩
    have hstep := FMReach.step (f := h.plain) ρ M (withQueries h (withInputs (plainInputs h) ρ ι) M hist) ih hass
    have hin : withInputs h.plain.m.inputs ρ (withQueries h (withInputs (plainInputs h) ρ ι) M hist)
        = withQueries h (withInputs (plainInputs h) ρ ι) M hist := inputs_eq ok ρ ι M hist
    rw [hin] at hstep
    have hX : ∀ s g, assoc h.sums s = some g → reqEnv h ρ ι M hist s = sumAt h (reqEnv h ρ ι M hist) M hist g := by
      intro s g hs
      have hmem := assoc_mem hs
      have ⟨hsin, _, _, hsf, _⟩ := ok.ss_out s hmem
      obtain ⟨p, hp, hpg⟩ : ∃ p ∈ h.sums, p.2 = g := by
        simp only [assoc, Option.map_eq_some_iff] at hs
        obtain ⟨p, hl, rfl⟩ := hs
        exact ⟨p, (lookup_some hl).1, rfl⟩
      have hok := ok.sums_ok p hp
      rw [hpg] at hok
      rw [reqEnv_other ok hsin hsf, hsum s g hs]
      exact sumAt_congr h M hist g (fun i hi => by
        have := avoidsE_occ hok.1 hi
        simp only [List.mem_append, not_or] at this
        exact (reqEnv_other ok this.1.1.1 this.2 ρ ι M hist).symm)
    have hst := step_eq ok (reqEnv h ρ ι M hist) M hist hX
    show FMReach h.plain (withSums h (applyS h.f.m.step (reqEnv h ρ ι M hist) M) M (kept h (reqEnv h ρ ι M hist) M hist))
      (writeMaps h.f.m.writes (reqEnv h ρ ι M hist) M)
    rw [← hst]
    exact hstep

/-- The history rule: if the record goals and the plain machine's proof check, every law of the proof holds in every
state the machine with its history reaches (sums read as their sums over the history, queries computed from it). -/
theorem hmachine_sound (h : HMachine) (ps : List MEntry) (rs : List (List VDef × Tree)) (hc : checkHMachine h ps rs = true) :
    ∀ ρ M hist, HReach h ρ M hist → ∀ e ∈ ps, e.law.Holds ρ M := by
  simp only [checkHMachine, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨hok, hlen⟩, hgoals⟩, hfm⟩ := hc
  have ok := histOk_sound hok
  have hrs : ∀ r ∈ h.rels, ∃ tt : List VDef × Tree, checkGoal ⟨tt.1, recordGoal h r⟩ tt.2 = true := by
    intro r hr
    obtain ⟨tt, htt⟩ := zip_mem_left h.rels rs hlen.symm r hr
    exact ⟨tt, hgoals (r, tt) htt⟩
  intro ρ M hist hr
  exact fmmachine_sound h.plain ps hfm ρ M (hreach_fmreach ps ok hrs hfm hr)

end Kern

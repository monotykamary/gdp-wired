import {type Machine} from '../../core/machine.ts'

// Diagnostic GIVEN-seed export only. Lean checks that even the hand-supplied
// ground instance follows from the ORIGINAL axiom; it is not a public premise.
export function rigidMinimalWrapper(m: Machine, choice: string, ix: (name: string) => number): string {
  if (m.inputs.length || Object.keys(m.state).length || Object.keys(m.maps ?? {}).length) throw Error('minimal source wrapper requires the empty-state example')
  const names = Object.keys(m.fns!), member = names.indexOf('member'), witness = names.indexOf(choice)
  const range = m.facts!.find(f => f.name === 'rigid_member_range')!, ax = m.facts!.find(f => f.name === 'rigid_intersection_axiom')!
  const node = ix('nodes'), quorum = ix('quorums'), value = ix('values'), ra = ix(range.forall!), rb = ix(range.keys![0]!), a = ix(ax.forall!), b = ix(ax.keys![0]!)
  if (member < 0 || witness < 0) throw Error('missing rigid symbols')
  const given = m.facts!.some(f => f.name.startsWith('GIVEN'))
  return `
-- ${given ? 'GIVEN diagnostic seed; not found.' : 'UNSEEDED: ordinary instances discovered by the opt-in general strategy.'}
-- Every emitted fact is discharged from the original axiom.
theorem rigid_minimal_original_source (nodes quorums values : Nat)
    (M : Nat → Nat → Nat)
    (relation : ∀ n q, n < nodes → q < quorums → M ${member} (pk n q) ≤ 1)
    (intersection : Kern.Rigid.Encoding.Source nodes quorums ${member} M) :
    0 < quorums → 0 < nodes := by
  obtain ⟨M', same, lowered⟩ :=
    (Kern.Rigid.Encoding.source_iff_extension nodes quorums ${member} ${witness} M (by decide)).mp intersection
  let ρ : Nat → Nat := fun i => if i = ${node} then nodes else if i = ${quorum} then quorums else if i = ${value} then values else 0
  have hrange : ∀ n q, n < nodes → q < quorums → M' ${member} (pk n q) ≤ 1 := by
    intro n q hn hq
    rw [same ${member} (by decide)]
    exact relation n q hn hq
  have hground : ∀ l ∈ rigid_minimal_machine.facts, l.Holds ρ M' := by
    intro l hl
    ${given ? `simp only [rigid_minimal_machine, List.mem_singleton] at hl
    subst l
    change evalC ρ M' (Kern.Rigid.Encoding.witnessBody ${member} ${witness} (.var ${node}) (.var ${quorum}) (.const 0) (.const 0)) = true
    apply (Kern.Rigid.Encoding.eval_witnessBody ρ M' ${member} ${witness} (.var ${node}) (.var ${quorum}) (.const 0) (.const 0)).mpr
    intro ha hb
    exact lowered 0 0 (by simpa [evalE, ρ] using ha) (by simpa [evalE, ρ] using hb)` : 'simp [rigid_minimal_machine] at hl'}
  have hpfacts : rigid_minimal_machine.PFacts ρ M' := by
    intro p hp
    simp only [rigid_minimal_machine, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · change ∀ q n, evalC (upd (upd ρ ${rb} q) ${ra} n) M' _ = true
      intro q n
      rw [evalC_iff]
      change (¬(n < nodes ∧ q < quorums)) ∨ M' ${member} (pk n q) ≤ 1
      by_cases h : n < nodes ∧ q < quorums
      · exact Or.inr (hrange n q h.1 h.2)
      · exact Or.inl h
    · change holdsOver (Kern.Rigid.Encoding.witnessFact ${member} ${witness} ${node} ${quorum} ${a} ${b}).1 M'
        (Kern.Rigid.Encoding.witnessFact ${member} ${witness} ${node} ${quorum} ${a} ${b}).2 ρ
      apply (Kern.Rigid.Encoding.witnessFact_iff ρ M' ${member} ${witness} ${node} ${quorum} ${a} ${b}
        (by decide) (by decide) (by decide) (by decide) (by decide)).mpr
      simpa [ρ] using lowered
  have reachable : SReach rigid_minimal_machine ρ M' := by
    apply SReach.start ρ M'
    · intro p hp
      simp [rigid_minimal_machine] at hp
    · simp [rigid_minimal_machine, evalC, evalE]
    · exact hground
    · exact hpfacts
  have law := rigid_minimal.law0 ρ M' reachable
  simp only [ρ, ite_eq_left] at law
  intro hq
  rcases law with h | h
  · exact False.elim (h hq)
  · exact h

#print axioms rigid_minimal_original_source
`
}

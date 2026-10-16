// Step machines and their laws as Lean, proven by Lean's own omega: an independent verdict on the machine itself, so
// the TypeScript that turns a machine into solver cases is checked too, as bend --verdict checks bend2's front end.
// Usage: bun compile-lean.ts > ../lean/Verdict.lean
import {type C, type E, type Law, type Machine, atMost, n, plus, times, x} from './machine.ts'
import {admit, boundedLoss, capLaws, inflight, inflightLoss, loss} from './models.ts'

function emit(m: Machine, tag: string, laws: Law[]): string {
  const P = m.params.map(p => `(${p} : Nat)`).join(' ')
  const args = m.params.join(' ')
  const scalars = Object.keys(m.state), maps = Object.keys(m.maps ?? {})
  let bound: string | undefined
  const ex = (e: E, st = 'st'): string => {
    switch (e.op) {
      case 'var': return e.name === bound ? e.name : m.params.includes(e.name) ? e.name : m.inputs.includes(e.name) ? `i.${e.name}` : `${st}.${e.name}`
      case 'const': return String(e.value)
      case 'add': return `(${ex(e.a, st)} + ${ex(e.b, st)})`
      case 'sub': return `(${ex(e.a, st)} - ${ex(e.b, st)})`
      case 'mul': return `(${e.k} * ${ex(e.a, st)})`
      case 'min': case 'max': return `(${e.op} ${ex(e.a, st)} ${ex(e.b, st)})`
      case 'if': return `(if ${cx(e.c, st)} then ${ex(e.then, st)} else ${ex(e.else, st)})`
      case 'get': return `(${st}.${e.map} ${ex(e.key, st)})`
    }
  }
  const cx = (c: C, st = 'st'): string => {
    switch (c.op) {
      case '<': return `${ex(c.a, st)} < ${ex(c.b, st)}`
      case '<=': return `${ex(c.a, st)} ≤ ${ex(c.b, st)}`
      case '=': return `${ex(c.a, st)} = ${ex(c.b, st)}`
      case 'and': return `(${c.xs.map(y => cx(y, st)).join(' ∧ ')})`
      case 'or': return `(${c.xs.map(y => cx(y, st)).join(' ∨ ')})`
      case 'not': return `¬(${cx(c.x, st)})`
      case 'flag': return c.name
    }
  }
  const S = `${tag}.St`, I = `${tag}.In`
  const fields = [...scalars.map(s => `  ${s} : Nat`), ...maps.map(mp => `  ${mp} : Nat → Nat`)].join('\n')
  const init = [...scalars.map(s => `${s} := ${ex(m.state[s]!, 'st')}`), ...maps.map(mp => `${mp} := fun _ => ${m.maps![mp]}`)].join(', ')
  const step = [
    ...scalars.map(s => `${s} := ${ex(m.step.state?.[s] ?? x(s))}`),
    ...maps.map(mp => {
      const w = m.step.maps?.[mp]
      return w ? `${mp} := upd st.${mp} ${ex(w.key)} ${ex(w.value)}` : `${mp} := st.${mp}`
    }),
  ].join(',\n    ')
  // A law as a Lean proposition about a state `st`.
  const prop = (law: Law, st: string) => {
    bound = law.forall
    const text = law.forall ? `∀ ${law.forall}, ${cx(law.holds, st)}` : cx(law.holds, st)
    bound = undefined
    return text
  }
  const lawName = (law: Law) => law.name.split(':')[0]!.replace(/[^A-Za-z0-9_]/g, '_')
  const out: string[] = [`namespace ${tag}
structure St where
${fields}
structure In where
${m.inputs.map(i => `  ${i} : Nat`).join('\n')}
def init ${P} : St := { ${init} }
def step ${P} (st : St) (i : In) : St :=
  { ${step} }`]
  const scalarLaws = laws.filter(l => !l.forall), mapLaws = laws.filter(l => l.forall)
  // Scalar laws are proven together, as one invariant; each map law on its own.
  if (scalarLaws.length) {
    const inv = scalarLaws.map(l => `(${prop(l, 'st')})`).join(' ∧ ')
    out.push(`def Inv ${P} (st : St) : Prop := ${inv}
theorem step_inv ${P} (st : St) (i : In) (h : Inv ${args} st) : Inv ${args} (step ${args} st i) := by
  simp only [Inv, step] at h ⊢
  ${scalarLaws.length > 1 ? `refine ⟨${scalarLaws.map(() => '?_').join(', ')}⟩ <;> ` : ''}(repeat' split) <;> omega
theorem inv_always ${P} (is : List In) : Inv ${args} (is.foldl (step ${args}) (init ${args})) :=
  Cert.run_preserves (step ${args}) (Inv ${args}) (init ${args}) (by simp only [Inv, init]; omega) (step_inv ${args}) is`)
    for (const law of scalarLaws) out.push(`theorem ${lawName(law)} ${P} (is : List In) : ${prop(law, 'st').replaceAll('st.', '(is.foldl (step ' + args + ') (init ' + args + ')).')} := by
  have h := inv_always ${args} is
  simp only [Inv] at h
  omega`)
  }
  for (const law of mapLaws) {
    const map = (law.holds.op === '<=' && law.holds.a.op === 'get') ? law.holds.a.map : ''
    const w = m.step.maps![map]!
    const key = ex(w.key)
    const k = law.forall!
    out.push(`theorem step_${lawName(law)} ${P} (st : St) (i : In) (h : ${prop(law, 'st')}) : ${prop(law, `(step ${args} st i)`)} := by
  intro ${k}
  by_cases e : ${k} = ${key}
  · rw [e]
    have hk := h ${key}
    simp only [step, upd, ite_true]
    (repeat' split) <;> omega
  · have hk := h ${k}
    simp only [step, upd, e, ite_false]
    omega
theorem ${lawName(law)} ${P} (is : List In) : ${prop(law, `(is.foldl (step ${args}) (init ${args}))`)} :=
  Cert.run_preserves (step ${args}) (fun st => ${prop(law, 'st')}) (init ${args}) (by intro ${k}; simp only [init]; omega) (step_${lawName(law)} ${args}) is`)
  }
  out.push(`end ${tag}`)
  return out.join('\n\n')
}

const inv: Law = {name: 'flight_invariant: s + 50p <= b + 150', holds: atMost(plus(x('s'), times(50, x('p'))), plus(x('b'), n(150)))}
console.log(`import Cert
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! Generated from gdp-wired's machines (core/models.ts) and proven here by omega, independently of the solver. -/

def upd (f : Nat → Nat) (k v : Nat) : Nat → Nat := fun y => if y = k then v else f y

${emit(loss(), 'Loss', [boundedLoss])}

${emit(admit(), 'Admit', capLaws)}

${emit(inflight, 'Inflight', [inflightLoss, inv])}

#print axioms Loss.bounded_loss
#print axioms Admit.once_per_account
#print axioms Admit.day_cap
#print axioms Admit.hour_cap
#print axioms Admit.dom_cap
#print axioms Inflight.in_flight_loss`)

// Rule 1, the budget, in gdp-wired's typed builders: s from 0; a request of cost c adds min(c, m) while s < b.
// Law: s <= b + m after any sequence of requests. proveRule proves it by induction over steps (the kernel checks the
// tree it grows); the step compiles to JavaScript with compileJs (loaded here by .compiled()).
import {min, nat, proveRule, rule, when} from '../../core/dsl.ts'
import {compileJs} from '../../core/machine.ts'

// --- rule
export const budget = rule('budget')
  .params({b: nat, m: nat})
  .inputs({c: nat})
  .state({s: 0})
  .step(({b, m, c, s}) => ({s: when(s.lt(b), s.plus(min(c, m)), s)}))

// --- laws
export const bounded = budget.law('s <= b + m', ({s, b, m}) => s.atMost(b.plus(m)))

// --- proofs
export const verdict = () => proveRule(budget, [bounded])

// --- run
if (import.meta.main) {
  const t0 = performance.now(), v = verdict(), ms = (performance.now() - t0).toFixed(1)
  const js = budget.compiled(), params = budget.encodeParams({b: 10, m: 4})
  let st = js.init(params)
  for (const c of [3, 9, 1, 7, 2]) st = js.step(params, st, budget.encodeInput({c}))
  console.log(`budget: proven=${v.proven} checked=${v.checked} prove_ms=${ms} js_bytes=${compileJs(budget.machine).length} run s=${st.scalars.s}`)
  process.exit(v.proven && v.checked ? 0 : 1)
}

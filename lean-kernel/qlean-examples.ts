// The examples (examples/rationals.ts) as Lean, for the suite's lean-rationals job: bun qlean-examples.ts > RatExamples.lean.
// A script apart from qlean.ts, so the published build (core/rationals.ts reads qlean.ts) never reaches the examples.
import {adversarial, feeLaws, feeSplit, ledger, ledgerLaws, limiter, limiterLaws, ratOf} from '../examples/rationals.ts'
import {rationalsToLean} from './qlean.ts'

const items = [{id: 'fee_split', machine: feeSplit().machine, laws: feeLaws()}, {id: 'rate_limiter', machine: limiter().machine, laws: limiterLaws()},
  {id: 'decimal_ledger', machine: ledger().machine, laws: ledgerLaws()},
  ...adversarial.filter(a => a.holdsOver === 'ℚ').map((a, j) => ({id: `holds_over_Q_${j}`, ...ratOf(a)}))]
console.log(rationalsToLean(items, 'The rational examples (examples/rationals.ts) and the laws that hold over ℚ but not over ℕ'))

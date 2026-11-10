// Ordinary counted attempts with a trivial initial-state disjunct; no protocol laws.
import {type Law, type Machine, any, atMost, get, ite, n, same, x} from '../../core/machine.ts'
import {countedAttempts, countsDump} from '../../core/counts.ts'
import {clock, counted, fullRate, withDeadline, withWall} from '../../kernel/prove.ts'
import {checkMC, countedObligations} from '../../kernel/kernel.ts'
const bit = ite(same(get('Cells', x('member')), n(1)), n(1), n(0))
const original = countsDump.on
try {
  for (const variant of ['upper', 'frame']) {
    const m: Machine = {name: 'guarded core replay ' + variant, params: [], inputs: ['at', 'value'], state: {ready:n(0)}, maps: {Cells: 0}, counts: {Total: {j: 'row', key: 'member', below: n(2), body: bit}}, step: {state:{ready:n(1)}, maps: {Cells: {key: x('at'), value: variant === 'frame' ? n(0) : x('value')}}}}
    const law: Law = {name: variant, holds:any(same(x('ready'),n(0)),atMost(get('Total', n(0)), n(variant === 'frame' ? 0 : 2)))}
    const phases: string[] = []
    countsDump.on = event => {if ('phase' in event && typeof event.phase === 'string') phases.push(event.phase)}
    const result = withWall(performance.now() + 8000, () => counted(fullRate, () => {const until = clock() + 4000; return withDeadline(until, () => countedAttempts(m, [law], new Set(), until).traced(law, [law], 1, 4000))}, true))
    const checked = 'proof' in result && countedObligations(m, [law], {[law.name]: result.proof.instances}, 0).every(({goal, decls}) => checkMC(goal.hyps, decls, result.proof.certs[goal.name]!))
    console.log('GUARDED_CORE_REPLAY ' + JSON.stringify({variant, phases, proof:'proof' in result, checked}))
  }
} finally {countsDump.on = original}

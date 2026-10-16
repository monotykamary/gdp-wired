import {inflight, inflightLoss} from './models.ts'
import {report} from './run-proofs.ts'
import {strengthen} from './invariant.ts'
const started = performance.now()
const result = strengthen(inflight, inflightLoss)
console.log(`${result.candidates} candidates, ${result.trueAtStart} true at the start, ${result.invariants.length} inductive together (${Math.round(performance.now() - started)} ms):`)
console.log('  ' + result.invariants.map(l => l.name).join('\n  '))
report(inflight, inflightLoss, [inflightLoss, ...result.invariants])

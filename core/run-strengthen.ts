import {inflight, inflightLoss} from './models.ts'
import {report} from './run-proofs.ts'
import {inferLaws} from './infer.ts'
const started = performance.now()
const result = inferLaws(inflight, [inflightLoss])
console.log(`${result.stats.candidates} candidates, ${result.stats.alive} the runs keep, ${result.found.length} found (${Math.round(performance.now() - started)} ms):`)
console.log('  ' + result.found.map(f => f.text).join('\n  '))
report(inflight, inflightLoss, [inflightLoss, ...result.found.map(f => f.law)])

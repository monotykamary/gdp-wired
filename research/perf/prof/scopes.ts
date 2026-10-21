// One law of examples/scopes.ts (or of research/frontier/scopes.ts's maps form) under the prover's profile:
// `bun research/perf/prof/scopes.ts <which>`, which in grants | grants-maps | normalize | normalize-read.
import {proveDecision, proveSteps} from '../../../core/dsl.ts'
import {profile, solveKinds} from '../../../kernel/prove.ts'
import {grantLaws, normalizedLaws} from '../../../examples/scopes.ts'
import {grants as grantsMaps, grantSteps} from '../../frontier/scopes.ts'

const which = process.argv[2] ?? 'grants'
profile.on = true
const t = performance.now()
const v = which === 'grants' ? proveDecision(grantLaws()[0]!)
  : which === 'grants-maps' ? (() => { const r = grantsMaps(); return proveSteps(r as never, [], grantSteps(r), {search: false}) })()
  : which === 'normalize' ? proveDecision(normalizedLaws()[0]!)
  : proveDecision(normalizedLaws()[1]!)
const ms = Math.round(performance.now() - t)
console.log(JSON.stringify({which, proven: v.proven, checked: v.checked, ms, solves: profile.solves, solveMs: Math.round(profile.solveMs), rowsMs: Math.round(profile.rowsMs), nodes: profile.nodes, kinds: solveKinds}))
for (const g of profile.goals.sort((a, b) => b.ms - a.ms).slice(0, 8)) console.log(JSON.stringify({...g, ms: Math.round(g.ms), solveMs: Math.round(g.solveMs), rowsMs: Math.round(g.rowsMs)}))

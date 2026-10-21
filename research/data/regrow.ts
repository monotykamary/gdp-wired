// Debugging: grow a saved goal again, with the prover's profile: bun research/data/regrow.ts <goal.json>
import {readFileSync} from 'node:fs'
import {grow, profile, pairedKeys, solveKinds} from '../../kernel/prove.ts'
const g = JSON.parse(readFileSync(process.argv[2]!, 'utf8'))
pairedKeys.skip = true
profile.on = true
const t = performance.now(), r = grow(g, new Map(), {nodes: 0, until: performance.now() + 20000})
console.log(Math.round(performance.now() - t), 'ms', 'tree' in r ? 'proven' : r.stuck, r.nodes ?? '', JSON.stringify({solves: profile.solves, solveMs: Math.round(profile.solveMs), rowsMs: Math.round(profile.rowsMs), nodes: profile.nodes}), JSON.stringify(solveKinds))

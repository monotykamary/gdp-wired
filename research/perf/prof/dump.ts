// The root goals of one law of research/perf/prof/scopes.ts, as text, stopping at the first: `bun dump.ts <which>`.
import {setProveDump} from '../../../kernel/prove.ts'
import {showC} from './show.ts'
setProveDump(goal => { console.log(`${goal.name}: ${goal.hyps.length} hyps`); goal.hyps.forEach((h, i) => console.log(`${i}: ${showC(h)}`)); process.exit(0) })
process.argv[2] ??= 'grants'
await import('./scopes.ts')

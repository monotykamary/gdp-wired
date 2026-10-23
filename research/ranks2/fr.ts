// Dev: findRank on one ARI task, the stack of what it throws. `bun research/ranks2/fr.ts <task.ari> [ms]`
import {readFileSync} from 'node:fs'
import {parseAri} from '../../compare/term/ari.ts'
import {build} from '../../compare/term/translate.ts'
import {findRank} from '../../core/cycles.ts'
const l = build(parseAri(readFileSync(process.argv[2]!, 'utf8')), 'task').loop
try { const f = findRank(l, [], {ms: Number(process.argv[3] ?? 5000)}); console.log(f.proven, f.found?.rank?.slice(0, 200), f.why?.slice(0, 300)) } catch (e) { console.log((e as Error).stack?.split('\n').slice(0, 12).join('\n')) }

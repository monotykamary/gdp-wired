// Dev probe: one ARI task's relation rank, then each kernel goal timed. `bun research/ranks2/dev.ts <task.ari> [--inv]`
import {readFileSync} from 'node:fs'
import {parseAri} from '../../compare/term/ari.ts'
import {build} from '../../compare/term/translate.ts'
import {rankOfRelation, rankWithInvariants} from '../../core/cycles.ts'
import {relationOf} from '../../core/relation.ts'
import {loopObligations} from '../../kernel/kernel.ts'
import {grow, withDeadline} from '../../kernel/prove.ts'
import {check} from '../../kernel/kernel.ts'
const file = process.argv[2]!, inv = process.argv.includes('--inv'), noKernel = process.argv.includes('--no-kernel')
const b = build(parseAri(readFileSync(file, 'utf8')), 'task')
const l = b.loop
let t = performance.now()
const rel = relationOf(l)
console.log('relation', rel ? `${rel.paths.length} paths, ${rel.state.length} state, ${rel.params.length} params, loc ${rel.loc}` : 'none', Math.round(performance.now() - t), 'ms')
t = performance.now()
const r = inv ? rankWithInvariants(l, [], performance.now() + 30000) : rankOfRelation(l, [], performance.now() + 30000)
console.log('rank', 'rank' in r ? r.text.slice(0, +(process.env.W ?? 2000)) + ('texts' in r ? ' with ' + r.texts.join('; ') : '') : r.why, Math.round(performance.now() - t), 'ms')
if ('rank' in r && !noKernel) {
  const laws = 'laws' in r ? r.laws : []
  for (const g of loopObligations(l, laws, r.rank)) {
    t = performance.now()
    const out = withDeadline(performance.now() + 60000, () => grow(g))
    const ok = 'tree' in out && check(g, out.tree)
    console.log(g.name, ok ? 'proven' : ('stuck' in out ? out.stuck + ' ' + JSON.stringify(out.witness ?? {}) : '?'), Math.round(performance.now() - t), 'ms', 'tree' in out ? JSON.stringify(out.tree).length : '')
  }
}

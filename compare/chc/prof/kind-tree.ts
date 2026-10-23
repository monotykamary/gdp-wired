// Not a solver: where k-induction's step goal at k spends its time (`bun compare/chc/prof/kind-tree.ts <task.smt2> <k>
// [--leaves 20000] [--ms 50000]`): CDCL's model search (refuted or not), then CDCL's tree (its search, its unfolding,
// its leaves, why it stopped) and its check. One JSON line.
import {readFileSync} from 'node:fs'
import {parseChc} from '../chc.ts'
import {build} from '../translate.ts'
import {check, kInductionSteps, stepLawObligations} from '../../../kernel/kernel.ts'
import {REFUTED, cdclStats, growCdcl} from '../../../kernel/cdcl.ts'
import {clock, counted} from '../../../kernel/prove.ts'

const args = process.argv.slice(2), file = args[0]!, k = Number(args[1] ?? 3)
const opt = (n: string, d: number) => { const i = args.indexOf(n); return i < 0 ? d : Number(args[i + 1]) }
const b = build(parseChc(readFileSync(file, 'utf8'))), m = b.rule.machine
const g = stepLawObligations(m, b.rule.kindLaws(), {}, kInductionSteps(m, {law: b.law, k}).at(-1)!)[0]!
const out: Record<string, unknown> = {task: file.split('/').slice(-2).join('/'), k, hyps: g.hyps.length}
counted(200, () => {
  cdclStats.on = true
  let t = performance.now(), c = clock()
  const d = growCdcl(g, new Map(), {nodes: 0, until: clock() + opt('--ms', 50_000)}, {model: true})
  out.decide = {answer: 'tree' in d ? 'tree' : d.why === REFUTED ? 'refuted' : d.stuck, ms: Math.round(performance.now() - t), counted: Math.round(clock() - c), conflicts: cdclStats.conflicts}
  if ('tree' in d || d.why !== REFUTED) return
  Object.assign(cdclStats, {conflicts: 0, unfoldMs: 0, leaves: 0, unfoldWhy: '', resolved2: 0})
  t = performance.now(); c = clock()
  const tr = growCdcl(g, new Map(), {nodes: 0, until: clock() + opt('--ms', 50_000)}, {maxLeaves: opt('--leaves', 20_000)})
  out.tree = {answer: 'tree' in tr ? 'tree' : `${tr.stuck} ${tr.why ?? ''}`, ms: Math.round(performance.now() - t), counted: Math.round(clock() - c), conflicts: cdclStats.conflicts, unfoldMs: Math.round(cdclStats.unfoldMs), why: cdclStats.unfoldWhy, resolved2: cdclStats.resolved2, bytes: 'tree' in tr ? JSON.stringify(tr.tree).length : 0}
  if ('tree' in tr) { t = performance.now(); out.check = {ok: check(g, tr.tree), ms: Math.round(performance.now() - t)} }
})
console.log(JSON.stringify(out))

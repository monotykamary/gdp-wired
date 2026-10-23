// The benchmark's recurrent sets checked again by Lean: each nonterminating answer of solve.ts by a recurrent set (its
// certificate printed in the answer's `recur`), on the task's loop as translate.ts builds it, as a theorem
// `NeverEnds <task>_loop` by Kern.never_ends_of (NonTerm.lean). The kernel's check is run again first.
//   bun compare/term/recur-lean.ts <results.jsonl> <bench dir> <out.lean> [--shard i/n]   (every n-th certificate from the i-th)
import {readFileSync, writeFileSync} from 'node:fs'
import {parseAri} from './ari.ts'
import {build} from './translate.ts'
import {checkRecur} from '../../kernel/kernel.ts'
import {toLean} from '../../lean-kernel/emit.ts'

const [results, bench, out] = process.argv.slice(2), si = process.argv.indexOf('--shard'), shard = si < 0 ? undefined : process.argv[si + 1]!.split('/').map(Number)
let seen = 0
if (!results || !bench || !out) throw new Error('usage: bun compare/term/recur-lean.ts <results.jsonl> <bench dir> <out.lean>')
const items = [], skipped: string[] = []
for (const line of readFileSync(results, 'utf8').split('\n').filter(Boolean)) {
  const row = JSON.parse(line) as {task: string, answer: string, stages: {stage: string, by?: string, recur?: Parameters<typeof checkRecur>[1]}[]}
  const last = row.stages?.at(-1)
  if (row.answer !== 'nonterminating' || last?.by !== 'recurrent set') continue
  if (shard && seen++ % shard[1]! !== shard[0]!) continue
  if (!last.recur) { skipped.push(`${row.task}: no certificate printed`); continue }
  const loop = build(parseAri(readFileSync(`${bench}/${row.task}`, 'utf8')), row.task.split('/').pop()!).loop
  if (!checkRecur(loop, last.recur)) { skipped.push(`${row.task}: the kernel refuses it`); continue }
  items.push({id: `t${items.length}_${row.task.split('/').pop()!.replace(/\.ari$/, '')}`, neverEnds: loop, recur: last.recur})
}
writeFileSync(out, toLean(items, {title: 'The benchmark\'s runs that never end'}))
console.log(`${items.length} certificates to ${out}${skipped.length ? `; skipped ${skipped.length}:\n  ${skipped.join('\n  ')}` : ''}`)

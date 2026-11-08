// No-search replay of a saved, checked branch. Opaque term columns are re-interned before any checking.
import assert from 'node:assert/strict'
import {readFileSync} from 'node:fs'
import {gzipSync} from 'node:zlib'
import {type E} from '../../core/machine.ts'
import {type Lin, costs, work} from '../../core/solver.ts'
import {type Goal, type Path, type Tree, canon, check, columnTerm, termColumn} from '../../kernel/kernel.ts'
import {shareLemmaCuts, setProofOrigin} from '../../core/lemma-cuts.ts'
const pack = JSON.parse(readFileSync(process.argv[2]!, 'utf8')) as {goal: Goal, tree: Tree, path: [string, {lin: Lin, holds: boolean}][], columns: Record<string, E>, origins?: {at: string, goal: Goal, tree: Tree, path: [string, {lin: Lin, holds: boolean}][]}[]}
assert(pack.columns, 'capture must include portable opaque columns')
const names = new Map(Object.entries(pack.columns).map(([old, e]) => [old, termColumn(e)]))
const rekey = (s: string) => s.replace(/⟦[0-9]+⟧/g, old => { const fresh = names.get(old); assert(fresh, `missing term ${old}`); return fresh })
const row = (r: Lin): Lin => Object.fromEntries(Object.entries(r).map(([key, value]) => [rekey(key), value]))
const tree = (t: Tree): Tree => 'split' in t ? {split: row(t.split), yes: tree(t.yes), no: tree(t.no)} : {...t, ...(t.squares ? {squares: t.squares.map(row)} : {})}
const t = tree(pack.tree), path: Path = new Map(pack.path.map(([, a]) => { const lin = row(a.lin); return [canon(lin), {lin, holds: a.holds}] }))
for (const origin of pack.origins ?? []) {
  let target = t
  for (const side of origin.at) { assert('split' in target); target = side === 'y' ? target.yes : target.no }
  const op: Path = new Map(origin.path.map(([, a]) => { const lin = row(a.lin); return [canon(lin), {lin, holds: a.holds}] }))
  setProofOrigin(target, {goal: origin.goal, tree: tree(origin.tree), path: op})
}
const started = performance.now(), original = check(pack.goal, t, path), beforeCheckMs = performance.now() - started
assert(original, 'portable original does not check')
const events: Record<string, string | number | boolean>[] = []
const sharing = performance.now(), shared = shareLemmaCuts(pack.goal, t, {path, until: sharing + 60000, minimizeConditions: process.env.LAB_MINIMIZE === '1', trace: e => events.push(e)})
assert.equal(work.n, 0)
assert(Object.values(costs).every(n => n === 0))
console.log(JSON.stringify({original, beforeCheckMs, proposed: !!shared, sharingMs: performance.now() - sharing, stats: shared?.stats, events, searchWork: work.n}))
if (shared) {
  const columns = Object.fromEntries([...new Set(JSON.stringify(shared).match(/⟦[0-9]+⟧/g) ?? [])].map(c => [c, columnTerm(c)]))
  console.log('SHARED64 ' + gzipSync(JSON.stringify({...shared, columns})).toString('base64'))
}

// One ADT-LIA task through gdp-wired: `bun compare/chc-adt/solve.ts <task.smt2> [--ms 57000]`.
// Prints one JSON line per stage and a last one with the answer: sat (every clause, read over the program the
// predicates' modes make, proven by proveData, whose proofs the kernel checks), unsat (a derivation of false that the
// clauses as written confirm, horn.ts's checkDerivation), unknown, or unsupported (and why).
//   - import: the task read (horn.ts) and its model guessed: each predicate's mode, the program, its defaults (cases no
//     clause covers)
//   - law <i>: clause i as a TIP goal over the program, translated by compare/tip/translate.ts (Int always the integers)
//     and given to proveData: each query briefly first (--quick-ms), then the clauses that define a predicate (--def-ms
//     each, without induction first: they are its equations; the first not proven ends the search), then the queries
//     again, the time left shared among them. A query's counterexample is derived (horn.ts's deriveQuery) and checked
//     against the clauses.
import {readFileSync} from 'node:fs'
import {Unsupported} from '../chc/chc.ts'
import {type V} from '../tip/tip.ts'
import {translate} from '../tip/translate.ts'
import {evalY, programOf, proveData, samples} from '../../core/data.ts'
import {type Law, checkDerivation, deriveQuery, lawOf, model, readHorn} from './horn.ts'

const args = process.argv.slice(2), file = args[0]!
const opt = (k: string, d: number) => { const i = args.indexOf(k); return i < 0 ? d : Number(args[i + 1]) }
const budget = opt('--ms', 57000), defMs = opt('--def-ms', 3000), quickMs = opt('--quick-ms', 1500)
const t0 = performance.now(), now = () => Math.round(performance.now() - t0), left = () => budget - now()
const say = (o: object) => console.log(JSON.stringify({ms: now(), ...o}))
const done = (answer: string, o: object = {}) => { say({stage: 'answer', answer, ...o}); process.exit(0) }

let h, pr, laws: Law[] = []
try {
  h = readHorn(readFileSync(file, 'utf8'))
  pr = model(h)
  laws = pr.norms.map(n => lawOf(h!, pr!, n))
} catch (e) {
  if (e instanceof Unsupported) done('unsupported', {why: e.message})
  done('unsupported', {why: `import failed: ${(e as Error).message.slice(0, 200)}`, error: true})
}
say({stage: 'import', preds: h!.chc.preds.size, clauses: h!.chc.clauses.length, laws: laws.length, queries: laws.filter(l => l.query).length, defaults: pr!.defaults, modes: Object.fromEntries(pr!.modes)})

// One law through the TIP translation and proveData, within ms: proven, or a counterexample's values (TIP's), or neither.
const tip = pr!.tip
// `induction: false` first, where asked: a clause that defines a predicate is its function's equation at a case.
const prove = (l: Law, ms: number, unfold = false): {proven: boolean, cex?: Map<string, V>, why?: string} => {
  tip.goal = {params: [], body: l.goal}
  let tr
  try { tr = translate(tip, `clause${l.index}`, [], {integers: true}) } catch (e) { return {proven: false, why: `${e instanceof Unsupported ? '' : 'translation failed: '}${(e as Error).message.slice(0, 160)}`} }
  if (tr.changes.length || tr.some) return {proven: false, why: `the translation changes the statement: ${tr.changes.join(', ') || 'an existential'}`}
  let v
  try {
    v = unfold ? proveData(tr.law, {ms: ms / 3, induction: false}) : undefined
    if (!v?.proven && !v?.counterexample) v = proveData(tr.law, {ms})
  } catch (e) { return {proven: false, why: `proveData threw: ${(e as Error).message.slice(0, 120)}`} }
  if (v.proven && v.checked) return {proven: true}
  if (!v.counterexample) return {proven: false, why: `${v.goal ?? ''} ${v.stuck ?? ''}`.trim().slice(0, 160)}
  // proveData's refutation is the first of refute's samples (seed 7) that breaks the law (compare/tip/solve.ts)
  for (const s of samples(tr.law.vars, programOf([tr.law]).params, 400, 7)) {
    if (evalY(tr.law.holds, s.env, s.params)) continue
    return {proven: false, cex: new Map(tr.vars.map(x => [x.tip, tr.toTip(s.env.get(x.gdp)!, x.ty)])), why: 'refuted'}
  }
  return {proven: false, why: 'the counterexample not found again'}
}

// (a law with a false hypothesis holds as it is: an application of a predicate read as false)
const defs = laws.filter(l => !l.query && !l.trivial), queries = laws.filter(l => l.query && !l.trivial), trivial = laws.filter(l => l.trivial).length
// the queries not yet proven; those refuted without a derivation the clauses confirm are tried no more
const unproven = new Set(queries.map(l => l.index)), proven = new Set<number>(), open: number[] = []
const query = (l: Law, ms: number) => {
  const r = prove(l, ms)
  say({stage: `law ${l.index}`, query: true, proven: r.proven, ...(r.why ? {why: r.why} : {})})
  if (r.proven) { unproven.delete(l.index); proven.add(l.index); return }
  if (r.cex) {
    const d = deriveQuery(h!, pr!, l, r.cex)
    const bad = d ? checkDerivation(h!, d) : 'no derivation at its values (a case the program leaves to its default)'
    if (!bad) done('unsat', {by: `law ${l.index}`})
    say({stage: `law ${l.index} derivation`, refused: bad})
    unproven.delete(l.index)
  }
}
// First each query briefly (a refutation, an easy proof), then the clauses that define a predicate: one not proven and
// the program isn't known to be a model, nothing more to look for; else the queries with the time left (proveData's
// budget is counted work, the track's limit wall time: a margin).
for (const l of queries) { if (left() < 500) break; query(l, Math.min(quickMs, 0.3 * left() / queries.length)) }
for (const l of defs) {
  if (left() < 500) break
  const r = prove(l, Math.min(defMs, left()), true)
  say({stage: `law ${l.index}`, query: false, proven: r.proven, ...(r.why ? {why: r.why} : {})})
  if (!r.proven) { open.push(l.index); break }
}
for (let round = 0; round < 2 && !open.length && unproven.size && left() > 500; round++) {
  for (const l of queries.filter(q => unproven.has(q.index))) { if (left() < 500) break; query(l, Math.max(500, 0.7 * left() / [...unproven].length)) }
}
// every clause proven over the program: it is a model of the system
if (!open.length && proven.size === queries.length && defs.length + queries.length + trivial === laws.length) done('sat', {laws: laws.length, trivial})
done('unknown', {open: open.length, queries: queries.length, unproven: unproven.size})

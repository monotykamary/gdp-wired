// One TIP problem through gdp-wired: `bun compare/tip/solve.ts <task.smt2> [--ms 57000] [--translate-only]`.
// Diagnostics (not the benchmark's run): `--lemma '<TIP formula>'` (repeatable) gives proveData those lemmas to prove
// and use instead of its own conjectures; `--conj-size k [--conj-max m]` gives it its own conjectures (core/data.ts's
// `conjectures`) up to k symbols instead of 6, m of them; `--today`, proveData without induction (its definitions
// unfolded, the kernel's prover alone: core/data.ts's proveDataToday); `--asserts`, the facts the problem asserts beside
// its goal (TIP's hints, which cvc5 and Vampire read as axioms) given as lemmas, each proven first; `--no-transfer`,
// proveData with the law as stated only (`transfer: false`: no definition unfolded, no bridge to a built-in); `--opts
// '<json>'`, proveData's options (core/data.ts's Options) over the run's; `--naturals`, the goal's sort variables at the
// naturals (the instance there), not as abstract sorts.
// `--inline` and `--native` (the first run's diagnostics) are proveData's own now (core/transfer.ts), and do nothing.
// An existential goal (∀ v. H ⇒ ∃ x. B) is proven through a witness among its variables (each a law, translate.ts's
// `some`), or refuted through what it says whatever the witness (B's conjuncts that read no x), its counterexample
// confirmed by TIP's evaluator on that part of the goal.
// Prints one JSON line per stage and a last one with the answer: proven (proveData's cyclic proof, checked by the
// kernel), refuted (a counterexample that TIP's own evaluator, tip.ts, confirms breaks the goal as TIP states it), unknown,
// unsupported (and why), or error (a translation that disagrees with TIP's evaluator: a translator bug, never run).
//   - import: the problem read (tip.ts) and translated (translate.ts): the changes to its statement, if any
//   - agree: the translation against TIP's evaluator on random values: the goal at 200 values of its variables, and
//     each function the translation made (those not specialised at a lambda) at 100 values of its arguments
//   - prove: proveData on the law, its budget --ms (counted in work units, core/data.ts's dataRate)
import {readFileSync} from 'node:fs'
import {OutOfFuel, type Sx, type Tip, type V, Unsupported, evaluate, parseSx, parseTip, prenex, sameV, showV} from './tip.ts'
import {type Translation, translate} from './translate.ts'
import {type DataLaw, type Value, conjectures, evalX, evalY, programOf, proveData, randomFn, randomValue, rng, samples, showY} from '../../core/data.ts'

const args = process.argv.slice(2), file = args[0]!
const opt = (k: string, d: number) => { const i = args.indexOf(k); return i < 0 ? d : Number(args[i + 1]) }
const ms = opt('--ms', 57000), translateOnly = args.includes('--translate-only'), conjSize = opt('--conj-size', 0), conjMax = opt('--conj-max', 48)
const lemmaSx: Sx[] = args.flatMap((a, i) => (a === '--lemma' ? parseSx(args[i + 1]!) : []))
const t0 = performance.now(), now = () => Math.round(performance.now() - t0)
const say = (o: object) => console.log(JSON.stringify({ms: now(), ...o}))
const done = (answer: string, o: object = {}) => { say({stage: 'answer', answer, ...o}); process.exit(0) }

let tip: Tip, tr: Translation
try {
  tip = parseTip(readFileSync(file, 'utf8'))
  tr = translate(tip, file.split('/').slice(-2).join('/'), [...lemmaSx, ...(args.includes('--asserts') ? tip.asserts : [])], {sorts: args.includes('--naturals') ? 'naturals' : 'abstract'})
} catch (e) {
  if (e instanceof Unsupported) done('unsupported', {why: e.message})
  done('unsupported', {why: `translation failed: ${(e as Error).message.slice(0, 300)}`, error: true})
}
say({stage: 'import', changes: tr!.changes, notes: tr!.notes, vars: tr!.vars.length, params: tr!.params.length, fns: tr!.fns.length, specialised: tr!.fns.filter(f => f.specialised).length, datas: tr!.datas, law: showY(tr!.law.holds).slice(0, 400)})

// A sample's values as TIP's: each variable's, each function variable and uninterpreted constant as the sample's tables
// of its unknowns make it (translate.ts's `eval`).
const tipEnv = (env: Map<string, Value>, params: Record<string, (n: number) => number>): Map<string, V> => {
  const out = new Map<string, V>()
  for (const v of tr!.vars) out.set(v.tip, tr!.toTip(env.get(v.gdp)!, v.ty))
  for (const p of tr!.params) out.set(p.tip, p.eval(params))
  return out
}
const tipHolds = (env: Map<string, Value>, params: Record<string, (n: number) => number>, goal: Sx = tr!.goal) => { const e = tipEnv(env, params); return evaluate(tip!, goal, e, undefined, consts(params)) === true }
// The uninterpreted constants and functions at a sample's tables (TIP's evaluator reads them in every body).
const consts = (params: Record<string, (n: number) => number>) => new Map(tr!.params.filter(p => p.const).map(p => [p.tip, p.eval(params)]))

{
  let goals = 0, fuel = 0
  const params = programOf([tr!.law]).params
  for (const s of samples(tr!.law.vars, params, 200, 3)) {
    let a: boolean, b: boolean
    try { a = evalY(tr!.law.holds, s.env, s.params) } catch (e) { if (e instanceof RangeError) { fuel++; continue } throw e }
    try { b = tipHolds(s.env, s.params) } catch (e) { if (e instanceof OutOfFuel || e instanceof RangeError) { fuel++; continue } throw e }
    if (a !== b) done('error', {why: 'translation disagrees with TIP on the goal', at: Object.fromEntries([...tipEnv(s.env, s.params)].map(([k, v]) => [k, showV(v)])), gdp: a, tip: b})
    goals++
  }
  let calls = 0
  const rand = rng(5)
  for (const f of tr!.fns.filter(f => !f.specialised)) {
    const fn = f.callable.fn
    for (let i = 0; i < 100; i++) {
      const vals = fn.params.map(p => randomValue(p.sort, rand, 1 + (i % 6)))
      const env = new Map(fn.params.map((p, j) => [`$a${j}`, vals[j]!]))
      // (an uninterpreted constant a function reads, at a table of its own: the same in both)
      const tables = Object.fromEntries(params.map(p => [p, randomFn(rand)])), cs = consts(tables)
      let got: Value, want: V
      try { got = evalX({op: 'call', fn: fn.name, args: fn.params.map((_, j) => ({op: 'var', name: `$a${j}`}))}, env, tables) } catch (e) { if (e instanceof RangeError) { fuel++; continue } throw e }
      try { want = evaluate(tip!, [f.tipName, ...f.argTys.map((_, j) => `$a${j}`)], new Map([...cs, ...f.argTys.map((t, j) => [`$a${j}`, tr!.toTip(vals[j]!, t)] as const)]), undefined, cs) } catch (e) { if (e instanceof OutOfFuel || e instanceof RangeError) { fuel++; continue } throw e }
      if (!sameV(tr!.toTip(got, f.retTy), want)) done('error', {why: `translation disagrees with TIP on ${f.tipName}`, args: vals.map((v, j) => showV(tr!.toTip(v, f.argTys[j]!))), gdp: showV(tr!.toTip(got, f.retTy)), tip: showV(want)})
      calls++
    }
  }
  say({stage: 'agree', goals, calls, skipped: fuel})
}
// An existential goal (translate.ts's `some`): each law it was read as agrees with TIP on its own goal too.
for (const w of tr!.some?.witnesses ?? []) {
  const body = prenex(w.sx).body
  for (const smp of samples(w.law.vars, programOf([w.law]).params, 100, 3)) {
    let a: boolean, b: boolean
    try { a = evalY(w.law.holds, smp.env, smp.params); b = tipHolds(smp.env, smp.params, body) } catch (e) { if (e instanceof OutOfFuel || e instanceof RangeError) continue; throw e }
    if (a !== b) done('error', {why: `translation disagrees with TIP on the witness ${w.terms.join(', ')}`, gdp: a, tip: b})
  }
}
if (translateOnly) done('translated', {changes: tr!.changes})
// An existential goal: refuted where what it says whatever the witness is (a counterexample TIP's evaluator confirms
// breaks that: then no witness can make the goal hold there), proven where a witness among its variables proves it.
if (tr!.some) {
  const sm = tr!.some, until = performance.now() + ms
  if (sm.weak) {
    const wv = proveData(sm.weak.law, {ms: ms / 2}), body = prenex(sm.weak.sx).body
    say({stage: 'prove', law: 'whatever the witness', proven: wv.proven, checked: wv.checked, counterexample: !!wv.counterexample, proveMs: wv.ms})
    if (wv.counterexample) for (const smp of samples(sm.weak.law.vars, programOf([sm.weak.law]).params, 400, 7)) {
      if (evalY(sm.weak.law.holds, smp.env, smp.params)) continue
      let holds: boolean | string
      try { holds = tipHolds(smp.env, smp.params, body) } catch (e) { holds = `evaluator: ${(e as Error).message}` }
      const at = Object.fromEntries([...tipEnv(smp.env, smp.params)].filter(([, x]) => !(typeof x === 'object' && 'fn' in x)).map(([k, x]) => [k, showV(x)]))
      // (each function variable as the table the sample drew, at 0..7)
      const fns = Object.fromEntries(tr!.params.map(pm => [pm.tip, Array.from({length: 8}, (_, i) => smp.params[pm.gdp]!(i))]))
      if (holds === false) done('refuted', {changes: tr!.changes, at, fns, via: 'what the existential says whatever its witness'})
      break
    }
  }
  for (const w of sm.witnesses) {
    const left = until - performance.now()
    if (left < 500) break
    const wv = proveData(w.law, {ms: left / Math.max(1, sm.witnesses.length)})
    say({stage: 'prove', law: `witness ${w.terms.join(', ')}`, proven: wv.proven, checked: wv.checked, proveMs: wv.ms})
    if (wv.proven && wv.checked) done('proven', {changes: tr!.changes, witness: w.terms, scheme: wv.scheme, lemmas: wv.lemmas})
  }
  done('unknown', {changes: tr!.changes, why: 'an existential goal: no witness among its variables proves it, and nothing refutes it'})
}

const given: DataLaw[] = [...tr!.lemmas, ...(conjSize ? conjectures(programOf([tr!.law]), tr!.law, conjMax, conjSize) : [])]
if (given.length) say({stage: 'lemmas given', n: given.length, hand: tr!.lemmas.map(l => showY(l.holds).slice(0, 200))})
let v: ReturnType<typeof proveData>
try { v = proveData(tr!.law, {ms, ...(given.length ? {lemmas: given} : {}), ...(args.includes('--today') ? {induction: false} : {}), ...(args.includes('--no-transfer') ? {transfer: false} : {}), ...(args.includes('--opts') ? JSON.parse(args[args.indexOf('--opts') + 1]!) as object : {})}) } catch (e) { done('error', {why: `proveData threw: ${(e as Error).message.slice(0, 200)}`}) }
say({stage: 'prove', proven: v!.proven, checked: v!.checked, proveMs: v!.ms, scheme: v!.scheme, lemmas: v!.lemmas, tried: v!.tried, ...(v!.through ? {through: v!.through} : {}), ...(v!.goal ? {goal: v!.goal.slice(0, 200), stuck: v!.stuck?.slice(0, 200)} : {})})
if (v!.proven && v!.checked) done('proven', {changes: tr!.changes, scheme: v!.scheme, lemmas: v!.lemmas, ...(v!.through ? {through: v!.through} : {})})
if (v!.counterexample) {
  // proveData's refutation is the first of refute's samples (seed 7) that breaks the law: found again here, its values
  // given to TIP's evaluator, which must say the goal is false there.
  for (const s of samples(tr!.law.vars, programOf([tr!.law]).params, 400, 7)) {
    if (evalY(tr!.law.holds, s.env, s.params)) continue
    let holds: boolean | string
    try { holds = tipHolds(s.env, s.params) } catch (e) { holds = `evaluator: ${(e as Error).message}` }
    const at = Object.fromEntries([...tipEnv(s.env, s.params)].filter(([, x]) => !(typeof x === 'object' && 'fn' in x)).map(([k, x]) => [k, showV(x)]))
    if (holds === false) done('refuted', {changes: tr!.changes, at})
    done('unknown', {why: 'a counterexample TIP\'s evaluator doesn\'t confirm', at, tip: holds})
  }
  done('unknown', {why: 'the counterexample not found again'})
}
done('unknown', {changes: tr!.changes, goal: v!.goal?.slice(0, 200), stuck: v!.stuck?.slice(0, 200)})

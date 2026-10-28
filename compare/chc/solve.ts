// One CHC-COMP task through gdp-wired: `bun compare/chc/solve.ts <task.smt2> [--runs-ms 5000] [--bmc-ms 15000] [--no-houdini]`.
// Prints one JSON line per stage and a last one with the answer: sat (the law proven and the kernel's check passed),
// unsat (a run reaching error that the CHC itself confirms, checkDerivation), unknown, or unsupported (and why).
//   - import: the CHC read and built as a rule (translate.ts)
//   - prove: proveRule on the law alone (its refutation by runs included)
//   - runs: random runs of the compiled rule, each step a clause the state can take and request values up to a bound
//     that doubles per round
//   - guided: runs the prover guides, each request a model of its clause's condition where the run is (the clauses that
//     derive false tried first at each state)
//   - kind and bmc: on the container's second CPU at the lowest priority (compare/chc/kind.ts, started once the task is
//     read, until the search's deadline; `--kind-ms 0` leaves it out), k-induction (core/kind.ts) and bounded runs
//     (core/bmc.ts: a deterministic loop's forced run, then a model of a k-step goal from the start to error, k = 1, 2,
//     ...) in turn, in doubling slices; proven, or a run checkDerivation confirms, it ends this process and answers
//     itself. With `--bmc-here` (or `--kind-ms 0`) the bounded runs are this process's stage after the guided runs,
//     within --bmc-ms (15,000), as before. Interpolation over the unrolling (core/interp.ts) shares k-induction's slice
//     (`--imc 2`, the default; `--imc 1` its own turn, `--imc 0` none); `--kind 0`: no k-induction there
//   - compose (`--compose 1`, the default; 0 for the rule of the CHC as written): every stage but k-induction searches the
//     system with its chains composed away (compose.ts), its runs expanded and its invariants lifted to the original
//     rule, where each answer is checked; `--slice 1` also weakens it by its cone of influence
//   - houdini: the library's search for the invariants the law needs (core/infer.ts), from the states the runs reached:
//     candidates per predicate (loc = p → a bound, a difference, a sum), those a run's state breaks dropped, then the
//     kernel's counterexamples to induction choosing which to add; `--old-houdini`, this folder's first Houdini
//     (houdini.ts: every candidate kept, rounds of proveRule until the rest are inductive together)
import {readFileSync} from 'node:fs'
import {Unsupported, parseChc} from './chc.ts'
import {type Raw, build, checkDerivation, requestOf, stepsOf} from './translate.ts'
import {proveRule} from '../../core/dsl.ts'
import {houdini} from './houdini.ts'
import {inferLaws} from '../../core/infer.ts'
import {findBoundedRun} from '../../core/bmc.ts'
import type {C, E, Law, State} from '../../core/machine.ts'
import {grow} from '../../kernel/prove.ts'
import {substC} from '../../kernel/kernel.ts'
import {type Composed, expand, invOf, liftProven, prepare} from './compose.ts'

// GDP_CHC_ARGS: more flags, read before the command line's (a run's knobs, through modal_chc.py's --env).
const args = [process.argv[2]!, ...(process.env.GDP_CHC_ARGS ?? '').split(' ').filter(Boolean), ...process.argv.slice(3)], file = args[0]!
const opt = (k: string, d: number) => { const i = args.indexOf(k); return i < 0 ? d : Number(args[i + 1]) }
// A sat answer's certificate: the kernel's usual trees, checked by kernel.ts (GDP_CERT=cyclic for the cyclic translation
// as well, core/cyclic.ts; on the dev tasks main answers the same either way, runs/chc7/d1-main against d1-mainu). kind.ts
// inherits it.
process.env.GDP_CERT ??= 'usual'
const liftMs = opt('--lift-ms', 8000), bmcMs = opt('--bmc-ms', 15000), runsMs = opt('--runs-ms', 5000), guideMs = opt('--guide-ms', 8000), houdiniMs = opt('--houdini-ms', 60000), useHoudini = !args.includes('--no-houdini'), oldHoudini = args.includes('--old-houdini')
const t0 = performance.now(), ms = () => Math.round(performance.now() - t0)
const say = (o: object) => console.log(JSON.stringify({task: file, ms: ms(), ...o}))
const done = (answer: string, o: object = {}) => { say({stage: 'answer', answer, ...o}); process.exit(0) }

// `--compose 1`: the chains composed away first (compose.ts); every search here then reads the composed rule, its
// unsat runs expanded and its sat invariants lifted to the original's, each checked there. The original rule (`bo`)
// is what every answer is checked on.
let chc, b, bo, cc: Composed | undefined
try {
  chc = parseChc(readFileSync(file, 'utf8'))
  bo = build(chc)
  void bo.rule.machine
  cc = prepare(chc, {slice: opt('--slice', 0) !== 0, chains: opt('--compose', 1) !== 0})
  if (cc) { b = build(cc.chc); void b.rule.machine }
  b ??= bo
} catch (e) {
  if (e instanceof Unsupported) done('unsupported', {why: e.message})
  done('unsupported', {why: `import failed: ${(e as Error).message.slice(0, 200)}`, error: true})
}
const {rule: r, law} = b!
say({stage: 'import', preds: chc!.preds.size, clauses: chc!.clauses.length, ints: b!.nInt, bools: b!.nBool, inputs: b!.inInt + b!.inBool, ...(cc ? {composed: cc.chc.clauses.length, eliminated: cc.eliminated.length} : {})})

// k-induction beside the other stages (compare/chc/kind.ts), until the search's deadline; stopped when this answers.
// At the lowest priority (nice 19): of the 41 tasks this or main answered alone, 32 and 35 answered that way, 30, 31 and
// 32 at the same priority, main 9, 16 and 18 (runs/kind/ch-nice-*, chc-mine, ch-mine-*, chc-base, ch-base-*).
// The bounded runs go there too (`--bmc-here` keeps them in this process's stage, after the guided runs, as before), in
// turn with k-induction, so this process's invariant search starts after the guided runs.
const kindMs = opt('--kind-ms', Math.max(0, houdiniMs - 2000 - ms())), bmcThere = kindMs > 0 && !args.includes('--bmc-here') && bmcMs > 0
const kind = kindMs > 0 ? Bun.spawn(['nice', '-n', '19', 'bun', `${import.meta.dir}/kind.ts`, file, '--ms', String(kindMs), '--parent', String(process.pid), '--bmc', bmcThere ? '1' : '0', '--imc', String(opt('--imc', 1)), '--imc-x', String(opt('--imc-x', 2)), '--imc-first', String(opt('--imc-first', 1)), '--bmc-depth', String(opt('--bmc-depth', 64)), '--induction', String(opt('--induction', -1)), '--kind', String(opt('--kind', 0)), '--compose', String(opt('--compose', 1)), '--slice', String(opt('--slice', 0))], {stdout: 'inherit', stderr: 'ignore'}) : undefined
process.on('exit', () => { kind?.kill() })

// A run, replayed on the compiled rule and checked against the CHC.
const g = r.compiled()
const unsat = (stage: string, raws: Raw[]) => {
  let orig: Raw[] | string = raws
  if (cc) { try { orig = expand(bo!, b!, cc, stepsOf(b!, raws)) } catch (e) { orig = `not expanded: ${(e as Error).message.slice(0, 80)}` } }
  let bad = typeof orig === 'string' ? orig : undefined
  if (!bad) { try { bad = checkDerivation(bo!, chc!, stepsOf(bo!, orig as Raw[])) } catch (e) { bad = `not replayed: ${(e as Error).message.slice(0, 80)}` } }
  if (bad) { say({stage, refused: bad}); return }
  done('unsat', {by: stage, steps: raws.length, ...(cc ? {original: (orig as Raw[]).length} : {})})
}
// A sat answer of the rule searched: itself where nothing was composed; else its invariant (the laws proven beside the
// law) lifted to the original rule and proven there.
const sat = (stage: string, laws: Law[], extra: object = {}) => {
  if (!cc) done('sat', {by: stage, ...extra})
  const inv = invOf([b!.law, ...r.kindLaws(), ...laws])
  if (!inv) { say({stage, lifted: false, why: 'a law with a key or "there exists"'}); return }
  const v = liftProven(cc!, bo!, inv, performance.now() + Math.max(1000, houdiniMs - 1000 - ms()))
  say({stage: `${stage} lift`, ...v})
  if (v.proven) done('sat', {by: stage, lifted: v.laws, ...extra})
}

const direct = proveRule(r, [law], {search: false})
say({stage: 'prove', proven: direct.proven, checked: direct.checked, ...(direct.stuck ? {stuck: direct.stuck.slice(0, 120)} : {})})
if (direct.proven && direct.checked) sat('prove', [])
if (direct.run) unsat('prove', direct.run.trace.map(t => decodeRequest(t)))

// Bounded runs (core/bmc.ts): a deterministic loop's forced run, then a run of k steps from the start that reaches error,
// for k = 1, 2, ..., each a model of a k-step goal; within --bmc-ms, counted and in wall time (the track's limit is wall
// time), and the limit.
const bounded = () => {
  if (bmcMs <= 0 || bmcThere) return
  // each depth tried: [k, its outcome's letter (refuted, sat, unknown), counted ms, wall ms]
  const depths: [number, string, number, number][] = []
  let w0 = ms()
  const found = findBoundedRun(r.machine, [law], {ms: bmcMs, wall: performance.now() + Math.min(bmcMs, Math.max(0, houdiniMs - 2000 - ms())), progress: (k, o, c) => { depths.push([k, o[0]!, c, ms() - w0]); w0 = ms() }})
  say({stage: 'bmc', depth: depths.at(-1)?.[0] ?? 0, found: !!found, depths})
  if (found) unsat('bmc', found.trace.map(t => decodeRequest(t as Record<string, unknown>)))
}

function decodeRequest(t: Record<string, unknown>): Raw { return requestOf(b!, t) }

// Random runs: a seeded walk; at each step a clause whose body is where the run is, request values in ±bound. The
// states they reach are kept (a sample) for Houdini.
const seen: State[] = []
{
  // dsl.ts's generator: the high bits of a linear congruence (the low ones repeat with a short period)
  let x = 7
  const rand = (k: number) => { x = (x * 1103515245 + 12345) % 2 ** 31; return Math.floor(x / 2 ** 31 * k) }
  const at = b!.plans.map(p => (p.clause.body[0] ? b!.loc[b!.predNames.indexOf(p.clause.body[0].pred)]! : 'start'))
  const until = performance.now() + runsMs
  let trials = 0
  for (let bound = 1; performance.now() < until; bound = Math.min(bound * 2, 1 << 20)) {
    for (let t = 0; t < 50 && performance.now() < until; t++, trials++) {
      let st = g.init({})
      const raws: Record<string, number | boolean | string>[] = []
      for (let d = 0; d < 256; d++) {
        const here = r.decode(st).loc, choices = at.flatMap((a, j) => (a === here ? [j] : []))
        if (!choices.length) break
        let moved = false
        for (let tries = 0; tries < 24 && !moved; tries++) {
          const raw: Record<string, number | boolean | string> = {c: b!.clauseNames[choices[rand(choices.length)]!]!}
          for (let k = 0; k < b!.inInt; k++) raw[`x${k}`] = rand(2 * bound + 1) - bound
          for (let k = 0; k < b!.inBool; k++) raw[`y${k}`] = rand(2) === 1
          let next
          // A request naming a clause that doesn't fire is refused (the rule's assumption): another is drawn. A value past
          // 2^53 − 1 ends the run (the rule refuses it too): that trial stops here.
          try { next = g.step({}, st, r.encodeInput(raw as never)) } catch (e) { if (e instanceof RangeError && e.message.includes('assumption')) continue; if (e instanceof RangeError) break; throw e }
          if (JSON.stringify(next.scalars) === JSON.stringify(st.scalars)) continue
          raws.push(raw); st = next; moved = true
          if (seen.length < 4000) seen.push(next); else if (rand(8) === 0) seen[rand(4000)] = next
        }
        if (!moved) break
        if (r.decode(st).loc === 'error') unsat('runs', raws)
      }
    }
  }
  say({stage: 'runs', trials})
}

// Runs the prover guides: at each state, a request for a clause that fires there, a model of the clause's condition
// with the state's values put in (kernel/prove.ts grow: a goal it doesn't refute comes back with a witness). The clauses
// that derive false are tried first; then another clause at random, some of the request's values fixed at random first
// (freed when that has no model). The compiled rule takes each request as it takes any, its assumption checked.
{
  const until = performance.now() + guideMs
  const bad = new Set(b!.plans.flatMap((p, j) => (p.clause.head ? [] : [j])))
  const at = b!.plans.map(p => (p.clause.body[0] ? b!.loc[b!.predNames.indexOf(p.clause.body[0].pred)]! : 'start'))
  const k = (value: number): E => ({op: 'const', value})
  let x = 11
  const rand = (n: number) => { x = (x * 1103515245 + 12345) % 2 ** 31; return Math.floor(x / 2 ** 31 * n) }
  const modelFor = (st: State, j: number, fix: Record<string, number>): Record<string, number | boolean | string> | undefined => {
    const vars: Record<string, E> = {c: k(j)}
    for (const [n, v] of Object.entries(st.scalars)) vars[n] = k(v)
    for (const [n, v] of Object.entries(fix)) if (n.startsWith('x')) (vars[n] = k(Math.max(0, v)), vars[`${n}$neg`] = k(Math.max(0, -v))); else vars[n] = k(v)
    const hyps: C[] = [substC(b!.fires[j]!, {vars, maps: {}, flags: {}}), ...Array.from({length: b!.inBool}, (_, q): C => ({op: '<=', a: {op: 'var', name: `y${q}`}, b: k(1)}))]
    const out = grow({name: 'a request', hyps}, new Map(), {nodes: 0, until: performance.now() + 300, units: false})
    if ('tree' in out || out.stuck !== 'sat' || !out.witness) return undefined
    const w = out.witness, raw: Record<string, number | boolean | string> = {c: b!.clauseNames[j]!}
    for (let q = 0; q < b!.inInt; q++) raw[`x${q}`] = `x${q}` in fix ? fix[`x${q}`]! : (w[`x${q}`] ?? 0) - (w[`x${q}$neg`] ?? 0)
    for (let q = 0; q < b!.inBool; q++) raw[`y${q}`] = (`y${q}` in fix ? fix[`y${q}`] : w[`y${q}`] ?? 0) === 1
    return raw
  }
  const take = (st: State, raw: Record<string, number | boolean | string>) => { try { return g.step({}, st, r.encodeInput(raw as never)) } catch (e) { if (e instanceof RangeError) return undefined; throw e } }
  let trials = 0, steps = 0
  while (performance.now() < until) {
    trials++
    let st = g.init({})
    const raws: Record<string, number | boolean | string>[] = []
    for (let d = 0; d < 2000 && performance.now() < until; d++) {
      const here = r.decode(st).loc, choices = at.flatMap((a, j) => (a === here ? [j] : []))
      for (const j of choices.filter(j => bad.has(j))) {
        const raw = modelFor(st, j, {}), next = raw && take(st, raw)
        if (next && r.decode(next).loc === 'error') unsat('guided', [...raws, raw!])
      }
      const others = choices.filter(j => !bad.has(j))
      let moved = false
      for (let tries = 0; tries < 6 && !moved && others.length; tries++) {
        const j = others[rand(others.length)]!, fix: Record<string, number> = {}
        const ints = Object.entries(st.scalars).filter(([n]) => n.startsWith('i') && !n.endsWith('$neg')).map(([n, v]) => v - (st.scalars[`${n}$neg`] ?? 0))
        if (tries < 4) {
          for (let q = 0; q < b!.inInt; q++) if (rand(2)) fix[`x${q}`] = [0, 1, -1, ...ints, ...ints.map(v => v + 1), ...ints.map(v => v - 1)][rand(3 + 3 * ints.length)]!
          for (let q = 0; q < b!.inBool; q++) if (rand(2)) fix[`y${q}`] = rand(2)
        }
        const raw = modelFor(st, j, fix), next = raw && take(st, raw)
        if (!next || JSON.stringify(next.scalars) === JSON.stringify(st.scalars)) continue
        raws.push(raw!); st = next; moved = true; steps++
        if (seen.length < 4000) seen.push(next); else if (rand(8) === 0) seen[rand(4000)] = next
      }
      if (!moved) break
    }
  }
  say({stage: 'guided', trials, steps})
}

bounded()

if (useHoudini && !oldHoudini) {
  // --houdini-ms is the stage's deadline from the start; the search is timed (`timed`), as the track's limit is wall time
  // for every solver, not counted as it is by default
  // (the join 0.8 of the search: the kernel's search after it rarely answers where the join ran out of time,
  // runs/inv2/i-s8 beside i-cfw)
  const h = inferLaws(r, [law], [], {ms: Math.max(1000, houdiniMs - ms() - (cc ? liftMs : 0)), timed: true, minimize: false, join: 0.8, seen, first: direct, progress: (phase, info) => say({stage: `infer ${phase}`, ...info})})
  say({stage: 'houdini', engine: 'infer', candidates: h.stats.candidates, alive: h.stats.alive, kept: h.found.length, proofs: h.stats.proofs, proven: h.proven && h.checked, ...(h.proven ? {} : {why: `${h.goal ?? ''} ${h.stuck ?? ''}`.trim().slice(0, 120)})})
  if (h.proven && h.checked) sat('houdini', h.found.map(f => f.law), {invariants: h.found.length})
}
if (useHoudini && oldHoudini) {
  const h = houdini(b!, chc!, seen, {ms: houdiniMs})
  say({stage: 'houdini', candidates: h.candidates, afterRuns: h.afterRuns, kept: h.kept.length, rounds: h.rounds, proven: h.proven, ...(h.why ? {why: h.why} : {})})
  if (h.proven && !cc) done('sat', {by: 'houdini', invariants: h.kept.length})
}
// (the second CPU may still answer: its end, at the deadline, is this one's; a step of it that overruns the deadline,
// such as a kernel proof that reads past it, is stopped with this process half a second after it, before the track's cap)
if (kind) await Promise.race([kind.exited, new Promise(res => setTimeout(res, Math.max(0, houdiniMs + 500 - ms())))])
done('unknown')

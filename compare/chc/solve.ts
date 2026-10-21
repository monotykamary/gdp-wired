// One CHC-COMP task through gdp-wired: `bun compare/chc/solve.ts <task.smt2> [--runs-ms 5000] [--no-houdini]`.
// Prints one JSON line per stage and a last one with the answer: sat (the law proven and the kernel's check passed),
// unsat (a run reaching error that the CHC itself confirms, checkDerivation), unknown, or unsupported (and why).
//   - import: the CHC read and built as a rule (translate.ts)
//   - prove: proveRule on the law alone (its refutation by runs included)
//   - runs: random runs of the compiled rule, each step a clause the state can take and request values up to a bound
//     that doubles per round
//   - houdini: candidate laws per predicate, those a run's state breaks dropped, then rounds of proveRule until the rest
//     are inductive together, then proveRule on the law and those kept (houdini.ts)
import {readFileSync} from 'node:fs'
import {Unsupported, parseChc} from './chc.ts'
import {type Step, build, checkDerivation} from './translate.ts'
import {proveRule} from '../../core/dsl.ts'
import {houdini} from './houdini.ts'
import type {State} from '../../core/machine.ts'

const args = process.argv.slice(2), file = args[0]!
const opt = (k: string, d: number) => { const i = args.indexOf(k); return i < 0 ? d : Number(args[i + 1]) }
const runsMs = opt('--runs-ms', 5000), houdiniMs = opt('--houdini-ms', 60000), useHoudini = !args.includes('--no-houdini')
const t0 = performance.now(), ms = () => Math.round(performance.now() - t0)
const say = (o: object) => console.log(JSON.stringify({task: file, ms: ms(), ...o}))
const done = (answer: string, o: object = {}) => { say({stage: 'answer', answer, ...o}); process.exit(0) }

let chc, b
try {
  chc = parseChc(readFileSync(file, 'utf8'))
  b = build(chc)
  void b.rule.machine
} catch (e) {
  if (e instanceof Unsupported) done('unsupported', {why: e.message})
  done('unsupported', {why: `import failed: ${(e as Error).message.slice(0, 200)}`, error: true})
}
const {rule: r, law} = b!
say({stage: 'import', preds: chc!.preds.size, clauses: chc!.clauses.length, ints: b!.nInt, bools: b!.nBool, inputs: b!.inInt + b!.inBool})

// A run, replayed on the compiled rule and checked against the CHC.
const g = r.compiled()
const replay = (raws: Record<string, number | boolean | string>[]) => {
  let st = g.init({})
  const steps: Step[] = []
  for (const raw of raws) {
    const before = r.decode(st), next = g.step({}, st, r.encodeInput(raw as never))
    steps.push({clause: Number(String(raw.c).slice(1)), input: raw, before, after: r.decode(next)})
    st = next
  }
  return steps
}
const unsat = (stage: string, raws: Record<string, number | boolean | string>[]) => {
  const bad = checkDerivation(b!, chc!, replay(raws))
  if (bad) { say({stage, refused: bad}); return }
  done('unsat', {by: stage, steps: raws.length})
}

const direct = proveRule(r, [law])
say({stage: 'prove', proven: direct.proven, checked: direct.checked, ...(direct.stuck ? {stuck: direct.stuck.slice(0, 120)} : {})})
if (direct.proven && direct.checked) done('sat', {by: 'prove'})
if (direct.run) unsat('prove', direct.run.trace.map(t => decodeRequest(t)))

function decodeRequest(t: Record<string, unknown>): Record<string, number | boolean | string> {
  const out: Record<string, number | boolean | string> = {c: b!.clauseNames[t.c as number]!}
  for (let k = 0; k < b!.inInt; k++) out[`x${k}`] = (t[`x${k}`] as number) - (t[`x${k}$neg`] as number)
  for (let k = 0; k < b!.inBool; k++) out[`y${k}`] = t[`y${k}`] === 1
  return out
}

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
          // A value past 2^53 − 1 ends the run (the rule refuses it): that trial stops here.
          try { next = g.step({}, st, r.encodeInput(raw as never)) } catch (e) { if (e instanceof RangeError) break; throw e }
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

if (useHoudini) {
  const h = houdini(b!, chc!, seen, {ms: houdiniMs})
  say({stage: 'houdini', candidates: h.candidates, afterRuns: h.afterRuns, kept: h.kept.length, rounds: h.rounds, proven: h.proven, ...(h.why ? {why: h.why} : {})})
  if (h.proven) done('sat', {by: 'houdini', invariants: h.kept.length})
}
done('unknown')

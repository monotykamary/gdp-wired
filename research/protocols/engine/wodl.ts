// gen/wo's pilots: decideLaw on wo's written laws' goals (every law's goals with the others assumed), each EPR decision's
// outcome, ms and the hypotheses it reads as not EPR-shaped.
//   bun research/protocols/engine/wodl.ts given [ms] [law-substring]   the written ∀ laws, the kinds' and the caller's
//   bun research/protocols/engine/wodl.ts ghost [ms]                   the ∃ law's ghost form (plain) over the ghosted
//                                                                      machine, the written ∀ laws assumed
//   bun research/protocols/engine/wodl.ts replay <dump.jsonl> [ms] [lo:hi]   wodump.ts's goals again; WO_Z3=1: each also
//       asked of Z3 (exp/z3's translator, z3ref/, untrusted, a referee only), the verdicts that differ counted
import {readFileSync} from 'node:fs'
import {type Law, type Machine} from '../../../core/machine.ts'
import {clock, counted, decideLaw, fullRate, withDeadline, withWall} from '../../../kernel/prove.ts'
import {decideHook} from '../../../kernel/epr.ts'
import {protocols} from '../models.ts'

const within = <T>(ms: number, f: () => T): T => { const end = performance.now() + ms; return withWall(end, () => counted(fullRate, () => withDeadline(clock() + ms, f), true)) }
const [mode = 'given', a1, a2, a3] = process.argv.slice(2), ms = Number((mode === 'replay' ? a2 : a1) ?? 1000)
const p = protocols.find(q => q.id === 'consensus_wo_decide')!, r: any = p.make(), human: Law[] = p.human(r), kinds: Law[] = r.kindLaws(), caller: Law[] = p.laws(r)
const isSome = (l: any) => !!l.some?.length || JSON.stringify(l.holds).includes('"ex"')
const foralls = human.filter(l => !isSome(l)), ex: any = human.find(isSome)
let m = r.machine
const ls: Law[] = [...kinds, ...foralls, ...caller]
if (mode === 'ghost') {
  // (the ∃ law's witness a ghost of the machine, its law plain over it, as the engine asks it)
  console.log('∃ law:', JSON.stringify(ex).slice(0, 600))
  const y = ex.some?.[0], g = y && ex.witness?.ghost?.[y]
  if (!g) { console.log('no ghost on the written ∃ law'); process.exit(0) }
  m = {...m, state: {...m.state, [y]: g.start}, step: {...m.step, state: {...m.step.state, [y]: g.step}}}
  ls.push({name: ex.name, holds: ex.holds})
}
if (mode === 'set') {
  // (the written set proven whole as the engine's set proof asks it: fast (proveSetFast, through the ∃ law's ghost), or not)
  const {proveRule} = await import('../../../core/dsl.ts')
  for (const fast of process.env.WO_BOTH ? [true, false] : [true]) {
    const t = performance.now(), v: any = proveRule(r, [...human, ...caller], {search: false, fast})
    console.log(JSON.stringify({fast, proven: v.proven, checked: v.checked, goal: v.goal, stuck: v.stuck, ms: Math.round(performance.now() - t)}))
  }
  process.exit(0)
}
if (mode === 'join') {
  // (the join's last query on wo: every k: Leader[k] <= VoteRequestMsg[k], the caller's law and the kinds' assumed)
  const {forall} = await import('../../../core/dsl.ts')
  ls.length = 0
  ls.push(...kinds, ...caller, r.law('every k: Leader[k] <= VoteRequestMsg[k]', ({Leader, VoteRequestMsg}: any) => forall((k: any) => Leader.at(k).implies(VoteRequestMsg.at(k)))))
}
const trace = !!process.env.WO_TRACE
const seen: {goal: string, out: string, ms: number, unshaped: number[], core: number}[] = []
decideHook.on = (goal, d, t, shaped) => {
  const un = (shaped ?? []).flatMap((s, i) => (s ? [] : [i]))
  seen.push({goal: goal.name, out: 'unknown' in d ? d.unknown : d.sat ? 'sat' : 'unsat', ms: Math.round(t), unshaped: un, core: 'core' in d ? d.core.length : 0})
  if (process.env.WO_CORES && 'core' in d) console.log('  CORE', goal.name.slice(-40), goal.hyps.length, JSON.stringify(d.core), d.core.map(i => JSON.stringify(goal.hyps[i]).slice(0, 220)).join('\n    '))
  if (trace) { console.log('  EPR', JSON.stringify(seen.at(-1))); for (const i of un.slice(0, 4)) console.log('    unshaped', i, JSON.stringify(goal.hyps[i]).slice(0, 400)) }
}
if (mode === 'replay') {
  const z3: any = process.env.WO_Z3 ? await import('./z3ref/z3.ts') : undefined
  const machines = new Map<string, Machine>(), sets = new Map<string, Law[]>(), goals: {m: Machine, ls: Law[], i: number, out: string}[] = []
  for (const line of readFileSync(a1!, 'utf8').split('\n')) {
    if (!line) continue
    const o = JSON.parse(line)
    if (o.machine) machines.set(o.id, o.machine); else if (o.set) sets.set(o.id, o.set); else goals.push({m: machines.get(o.m)!, ls: sets.get(o.s)!, i: o.i, out: o.out})
  }
  const [lo, hi, step = 1] = a3 ? a3.split(':').map(Number) as [number, number, number?] : [0, goals.length]
  const why = new Map<string, number>()
  let und = 0, wrong = 0, z3und = 0, both = 0, n2 = 0, dlMs = 0
  for (const [k, g] of goals.slice(lo, hi).entries()) {
    if (k % step) continue
    seen.length = 0
    const t = performance.now(), d = within(ms, () => decideLaw(g.m, g.ls, g.i)), dt = performance.now() - t
    n2++; dlMs += dt
    const dl = !d ? 'undecided' : d.proven ? 'proven' : 'model'
    if (!d) { und++; for (const s2 of new Set(seen.map(x => x.out))) why.set(s2, (why.get(s2) ?? 0) + 1) }
    let zv = ''
    if (z3) { const z = z3.z3Decide(g.m, g.ls, g.i, Math.max(ms, 2000)); zv = !z ? 'undecided' : z.proven ? 'proven' : 'model'; if (!z) z3und++ }
    const bad = !!z3 && d && zv !== 'undecided' && zv !== dl
    if (bad) wrong++
    if (z3 && d && zv !== 'undecided') both++
    console.log(JSON.stringify({at: lo + k, law: g.ls[g.i]!.name.slice(0, 100), laws: g.ls.length, engine: g.out, dl, ms: Math.round(dt), ...(z3 ? {z3: zv} : {}), ...(bad ? {WRONG: 1} : {}), outs: [...new Set(seen.map(x => x.out))].slice(0, 3), core: seen.reduce((n, x) => n + x.core, 0), unshaped: [...new Set(seen.flatMap(x => x.unshaped))].length}))
  }
  console.log(JSON.stringify({goals: n2, undecided: und, meanMs: Math.round(dlMs / Math.max(1, n2)), ...(z3 ? {z3undecided: z3und, bothDecided: both, wrong} : {}), why: Object.fromEntries(why)}))
  process.exit(0)
}
const z3g: any = process.env.WO_Z3 ? await import('./z3ref/z3.ts') : undefined
let undecided = 0
for (let i = 0; i < ls.length; i++) {
  if (a2 && !ls[i]!.name.includes(a2)) continue
  seen.length = 0
  const t = performance.now(), d = within(ms, () => decideLaw(m, ls, i)), dt = Math.round(performance.now() - t)
  if (!d) undecided++
  if (d && !d.proven && process.env.WO_W) console.log('  model:', Object.entries(d.witness).filter(([, x]) => x).map(([k, x]) => `${k}=${x}`).join(' ').slice(0, 3000))
  console.log(JSON.stringify({law: ls[i]!.name.slice(0, 90), verdict: !d ? 'undecided' : d.proven ? 'proven' : `model ${d.goal.replace(/.* @/, '@')}`, ms: dt,
    decisions: seen.length, outs: [...new Set(seen.map(s => s.out))].slice(0, 4), unshaped: [...new Set(seen.flatMap(s => s.unshaped))].length,
    ...(z3g ? {z3: (z => (!z ? 'undecided' : z.proven ? 'proven' : `model ${z.goal.replace(/.* @/, '@')}`))(z3g.z3Decide(m, ls, i, 5000))} : {})}))
}
console.log(JSON.stringify({laws: ls.length, undecided}))
process.exit(0)

// Section 17 trace: one frozen-family helper × operation × counted pass, every countsDump event as one line (`S17 {...}`,
// heavy fields reduced to sizes), the counted clock, wall and RSS at each, and the attempt's end (`S17_END`). Research
// only: no proof is produced, nothing is admitted. Runs unchanged on the frozen 15eff72f tree and on this one.
import {readFileSync} from 'node:fs'
import {traceError} from './trace-error.ts'
import {all, same, x, n, type Law, type Machine} from '../../core/machine.ts'
import {countedAttempts, countsDump} from '../../core/counts.ts'
import {finiteCountChoice} from '../../core/count-cases.ts'
import {clock, counted, fullRate, fullWork, withWall} from '../../kernel/prove.ts'
const [file, tag, opText, passText, wallText = '60000', budgetText = '1e12'] = process.argv.slice(2)
const p = JSON.parse(readFileSync(file!, 'utf8')), op = Number(opText), pass = Number(passText) as 0 | 1, wallMs = Number(wallText), budget = Number(budgetText)
const choice = finiteCountChoice(p.m)
if (!choice || !choice[1].has(op)) throw Error('operation not present')
const law: Law = p.laws[p.targets[tag!]]
if (!law) throw Error('missing target')
const m: Machine = {...p.m, assume: all(...(p.m.assume ? [p.m.assume] : []), same(x(choice[0]), n(op)))}
const t0 = performance.now(), w0 = fullWork()
let seq = 0
// One compact line per event: the counted clock, wall and RSS; a query's hypothesis count and instance totals; a model's
// key values and every count read's value with its map and key, post and pre side by side; an error's text.
const keyText = (e: unknown): string => JSON.stringify(e).replace(/\{"op":"var","name":"([^"]+)"\}/g, '$1').replace(/\{"op":"const","value":(\d+)\}/g, '$1').replace(/\{"op":"add","a":(.*?),"b":(.*?)\}$/, '$1+$2').replace(/\{"op":"mul","k":(\d+),"a":(.*?)\}/g, '$1*$2')
let readsOf: Record<string, string> = {}
countsDump.on = e => {
  const r = e as Record<string, unknown>, out: Record<string, unknown> = {seq: ++seq, ms: Math.round(performance.now() - t0), units: Math.round((fullWork() - w0) / fullRate), rssMiB: Math.round(process.memoryUsage().rss / 1048576), phase: r.phase}
  const c = r.certificateRequest as {reads?: [string, string, unknown][], insts?: unknown[]} | undefined
  if (c?.reads) { readsOf = Object.fromEntries(c.reads.map(([map, v, key]) => [v, `${map}[${keyText(key)}]`])); out.reads = c.reads.length; out.insts = c.insts?.length }
  if (Array.isArray(r.hyps)) out.hyps = r.hyps.length
  if (r.instances && typeof r.instances === 'object') { const inst = r.instances as Record<string, unknown[]>; out.flagInst = Object.entries(inst).filter(([k]) => k.startsWith('?')).reduce((s, [, v]) => s + v.length, 0); const laws = Object.entries(inst).filter(([k]) => !k.startsWith('?')); out.lawInst = laws.reduce((s, [, v]) => s + v.length, 0); out.lawsWithInst = laws.length }
  if (r.witness && typeof r.witness === 'object') {
    const w = r.witness as Record<string, number>
    out.keys = Object.fromEntries(Object.entries(w).filter(([k]) => !k.startsWith('?') && !k.startsWith('r$') && !k.startsWith('w$')))
    out.counts = Object.fromEntries(Object.entries(w).filter(([k]) => k.startsWith('r$')).map(([k, v]) => [`${k}=${readsOf[k] ?? '?'}`, v]))
  }
  if (r.error !== undefined) out.error = traceError(r.error)
  if (r.completion && typeof r.completion === 'object') out.completion = {genuine: (r.completion as {genuine?: boolean}).genuine, reason: (r.completion as {reason?: string}).reason}
  for (const k of ['stuck', 'outcome', 'added', 'local', 'whole', 'context', 'required', 'known', 'round', 'seedCount']) if (k in r) out[k] = r[k]
  console.log('S17 ' + JSON.stringify(out))
}
let result: Record<string, unknown> | undefined, error: string | undefined
try {
  counted(fullRate, () => withWall(t0 + wallMs, () => {
    const until = clock() + budget, a = countedAttempts(m, p.caller.map((i: number) => p.laws[i]), new Set(p.support.map((i: number) => p.laws[i])), until) as {houdini?: boolean, traced: (law: Law, ls: Law[], pass: 0 | 1, ms: number) => Record<string, unknown>}
    a.houdini = true
    result = a.traced(law, p.laws, pass, budget)
  }))
} catch (e) { error = String(e) }
console.log('S17_END ' + JSON.stringify({tag, op, pass, law: law.name, ms: Math.round(performance.now() - t0), units: Math.round((fullWork() - w0) / fullRate), rssMiB: Math.round(process.memoryUsage().rss / 1048576), events: seq,
  result: result && ('proof' in result ? 'proof' : {stuck: result.stuck, why: result.why, refuted: result.refuted}), error}))

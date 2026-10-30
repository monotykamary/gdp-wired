// gen/laneA2: where a protocol's EPR decisions spend their units, and how much of their encoding repeats from one goal
// to the next (the case for one incremental solver a round).
//   GDP_INFER_TRACE=2 bun research/protocols/engine/incprobe.ts <id> [ms]
import {proveRule} from '../../../core/dsl.ts'
import {decideHook, decideInfo, eprMeter} from '../../../kernel/epr.ts'
import {decideLawHook} from '../../../kernel/prove.ts'
import {protocols} from '../models.ts'

const [id = 'ring_leader_election', ms0] = process.argv.slice(2), ms = Number(ms0 ?? 60_000)
decideInfo.on = true
let n0 = eprMeter.n, p0 = eprMeter.p, dl = 0, prevHyps = new Set<string>(), prevSig = ''
const tot = {decides: 0, units: 0, build: 0, prop: 0, ms: 0, hyps: 0, sharedPrev: 0, sameSig: 0, sameSigHyps: 0, lazy: 0}
const seenHyp = new Map<string, number>(), sigs = new Map<string, number>(), byOut = new Map<string, number>(), ordsH = new Map<number, number>()
let start = eprMeter.n, startP = eprMeter.p
decideHook.on = (goal, d, t) => {
  const units = eprMeter.n - start, prop = eprMeter.p - startP, build = (decideInfo.built ?? start) - start
  start = eprMeter.n; startP = eprMeter.p
  const hs = goal.hyps.map(h => JSON.stringify(h)), set = new Set(hs)
  let shared = 0
  for (const h of set) { if (prevHyps.has(h)) shared++; seenHyp.set(h, (seenHyp.get(h) ?? 0) + 1) }
  const sig = decideInfo.sig ?? ''
  tot.decides++; tot.units += units; tot.build += build; tot.prop += prop; tot.ms += t; tot.hyps += set.size; tot.sharedPrev += shared
  if (sig === prevSig) { tot.sameSig++; tot.sameSigHyps += shared }
  if (decideInfo.lazy) tot.lazy++
  sigs.set(sig, (sigs.get(sig) ?? 0) + 1)
  const out = 'unknown' in d ? `unknown:${d.unknown.slice(0, 40)}` : d.sat ? 'sat' : 'unsat'
  byOut.set(out, (byOut.get(out) ?? 0) + 1)
  const ob = Math.ceil((decideInfo.ords ?? 0) / 8) * 8; ordsH.set(ob, (ordsH.get(ob) ?? 0) + 1)
  if (process.env.INC_EACH) console.log(JSON.stringify({k: tot.decides, dl, g: goal.name.replace(/.* @/, '@'), nh: set.size, shared, same: sig === prevSig, ords: decideInfo.ords, cl: decideInfo.clauses, units, build, prop, ms: Math.round(t), out}))
  prevHyps = set; prevSig = sig
}
start = eprMeter.n; startP = eprMeter.p
decideLawHook.on = () => { dl++; start = eprMeter.n; startP = eprMeter.p }
const p = protocols.find(q => q.id === id)!, r = p.make(), t0 = performance.now(), v: any = proveRule(r, p.laws(r), {search: {ms}})
console.log(JSON.stringify({id, verdict: v.proven && v.checked ? "proven" : "unknown", wall: Math.round(performance.now() - t0), decideLaws: dl, ...tot, ms2: Math.round(tot.ms), distinctHyps: seenHyp.size, sigs: sigs.size, eprAll: eprMeter.n - n0, propAll: eprMeter.p - p0}))
console.log(JSON.stringify({outs: Object.fromEntries(byOut), ords: Object.fromEntries([...ordsH].sort((a, b) => a[0] - b[0])), topSigs: [...sigs.values()].sort((a, b) => b - a).slice(0, 12)}))
process.exit(0)

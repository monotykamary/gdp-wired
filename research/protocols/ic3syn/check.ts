// Each port against its source on one small instance: every reachable state by BFS (models.ts's `check`: the params,
// each input's values, the state read as the TLA+ spec's variables), counted as the spec's states, beside TLC's distinct
// states on the same constants (tlc.py runs both). One JSON line per protocol; --cfg <dir> writes each port's TLC cfg.
//   bun research/protocols/ic3syn/check.ts [--only id,id] [--cfg dir] [--ms 60000] [--broken]
// `bad` counts the reachable states that break the safety property as the port reads it (`bad`): 0 for the port, and
// above 0 for its broken variant (--broken, which stops at the first), which shows the property is not vacuous on the
// instance. The op input's
// values are its choices' positions (0, 1, ...).
import {writeFileSync} from 'node:fs'
import {interpret} from '../../../core/machine.ts'
import {protocols} from './models.ts'

const arg = (name: string) => { const i = process.argv.indexOf(`--${name}`); return i < 0 ? undefined : process.argv[i + 1] }
const only = arg('only')?.split(','), cfgDir = arg('cfg'), ms = Number(arg('ms') ?? 60_000), broken = process.argv.includes('--broken')

const product = (dom: Record<string, unknown[]>): Record<string, unknown>[] =>
  Object.entries(dom).reduce<Record<string, unknown>[]>((acc, [k, vs]) => acc.flatMap(a => vs.map(v => ({...a, [k]: v}))), [{}])

if (process.argv.includes('--list')) { console.log(protocols.map(p => p.id).join(',')); process.exit(0) }
for (const p of protocols.filter(q => q.check && (!only || only.includes(q.id)))) {
  const c = p.check!
  if (cfgDir) { if (c.tlc) writeFileSync(`${cfgDir}/${p.id}.cfg`, c.tlc.cfg); console.log(JSON.stringify({id: p.id, module: c.tlc?.module, fix: c.tlc?.fix ?? []})); continue }
  const r: any = p.make(broken ? p.bug : undefined), m = r.machine, run = interpret(m), params = c.params ?? {}
  const given = product(c.inputs).filter(i => !c.uses || Object.entries(i).every(([k, v]) => k === 'op' || c.uses![i.op as number]!.includes(k) || v === c.inputs[k]![0])), plain = given.flatMap(i => (c.expand && !c.byState ? c.expand(i) : [i]))
  const reqsAt = (st: any) => (c.byState ? given.flatMap(i => c.expand!(i, read(st))) : plain)
  const dflt = (st: any, name: string) => st.defaults?.[name] ?? m.maps?.[name] ?? 0
  const read = (st: any) => ({cell: (map: string, key: number) => st.maps[map]?.get(key) ?? dflt(st, map), scalar: (name: string) => st.scalars[name]})
  const keyOf = (st: any) => JSON.stringify([st.scalars, Object.keys(st.maps).sort().map(k => [k, dflt(st, k), [...st.maps[k]].filter(([, v]: any) => v !== dflt(st, k)).sort((a: any, b: any) => a[0] - b[0])])])
  const t0 = performance.now(), st0 = run.init(params), seen = new Set([keyOf(st0)]), spec = new Set<string>()
  const proj = (st: any) => { const x = c.project(read(st)); if (x !== undefined) spec.add(JSON.stringify(x)); return x }
  let frontier = [st0], depth = 0, refused = 0, stepped = 0, bad = 0, done = true
  proj(st0); if (p.bad?.(read(st0))) bad++
  while (frontier.length) {
    if (performance.now() - t0 > ms) { done = false; break }
    const next: any[] = []
    for (const st of frontier) for (const q of reqsAt(st)) {
      let s2: any
      try { s2 = run.step(params, st, q); stepped++ } catch { refused++; continue }
      const k = keyOf(s2); if (seen.has(k)) continue
      if (c.keep && !c.keep(read(s2))) continue
      seen.add(k); next.push(s2); proj(s2)
      if (p.bad?.(read(s2))) bad++
      if (broken && bad) break
    }
    if (next.length) depth++
    frontier = broken && bad ? [] : next
  }
  console.log(JSON.stringify({id: p.id, broken, states: spec.size, raw: seen.size, depth, done, requests: given.length, bad, ...(c.states ? {tlc: c.states} : {}), ms: Math.round(performance.now() - t0)}))
}

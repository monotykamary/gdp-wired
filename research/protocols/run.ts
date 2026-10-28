// The pilot: for each protocol of models.ts, its safety law proven with nothing written (proveRule's search), the
// invariant a person writes checked by the kernel (the search off), and the broken variant, which must be refused with
// a run. One JSON line per protocol on stdout.
//   bun research/protocols/run.ts [--ms 20000] [--only id,id] [--skip given,broken]
// (--only lock_server_sync@one,lock_server_async@one: the diagnostic cuts to one server, models.ts's `cuts`)
import {proveRule} from '../../core/dsl.ts'
import {cuts, protocols} from './models.ts'

const arg = (name: string) => { const i = process.argv.indexOf(`--${name}`); return i < 0 ? undefined : process.argv[i + 1] }
const ms = Number(arg('ms') ?? 20_000), only = arg('only')?.split(','), skip = new Set(arg('skip')?.split(',') ?? [])
const timed = <T>(f: () => T): [T, number] => { const t = performance.now(), v = f(); return [v, Math.round(performance.now() - t)] }
const verdictOf = (v: any) => v.proven && v.checked ? 'proven' : v.run ? 'refuted' : 'unknown'
const brief = (v: any) => ({verdict: verdictOf(v), ...(v.goal ? {goal: v.goal} : {}), ...(v.stuck ? {stuck: v.stuck} : {}), ...(v.why ? {why: String(v.why).slice(0, 160)} : {}),
  ...(v.run ? {run: v.run.trace?.length} : {}), ...(v.found?.laws?.length ? {found: v.found.laws.map((f: any) => f.source ?? f.text)} : {})})

for (const p of [...protocols, ...cuts].filter(p => only ? only.includes(p.id) : !p.id.includes('@'))) {
  const out: Record<string, unknown> = {id: p.id}
  try {
    const r = p.make(), laws = p.laws(r)
    const [v, t] = timed(() => proveRule(r, laws, {search: {ms}}))
    out.search = {...brief(v), ms: t}
    if (!skip.has('given')) { const [g, tg] = timed(() => proveRule(r, [...p.human(r), ...laws], {search: false})); out.given = {...brief(g), ms: tg} }
    if (!skip.has('broken')) { const bad = p.make(p.bug), [b, tb] = timed(() => proveRule(bad, p.laws(bad))); out.broken = {bug: p.bug, ...brief(b), ms: tb} }
  } catch (e) { out.error = String((e as Error).stack ?? e).slice(0, 400) }
  console.log(JSON.stringify(out))
}

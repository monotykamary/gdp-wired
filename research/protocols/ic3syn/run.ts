// The IC3Syn ports' safety laws proven with nothing written (proveRule's search), and each broken variant refuted. One
// JSON line per protocol on stdout; with GDP_INFER_TRACE=2 the search's phases go to stderr (jobs.ts greps them).
//   bun research/protocols/ic3syn/run.ts [--ms 60000] [--only id,id] [--skip search,broken]
import {proveRule} from '../../../core/dsl.ts'
import {protocols} from './models.ts'

const arg = (name: string) => { const i = process.argv.indexOf(`--${name}`); return i < 0 ? undefined : process.argv[i + 1] }
const ms = Number(arg('ms') ?? 60_000), only = arg('only')?.split(','), skip = new Set(arg('skip')?.split(',') ?? [])
const timed = <T>(f: () => T): [T, number] => { const t = performance.now(), v = f(); return [v, Math.round(performance.now() - t)] }
const verdictOf = (v: any) => v.proven && v.checked ? 'proven' : v.run ? 'refuted' : 'unknown'
const brief = (v: any) => ({verdict: verdictOf(v), ...(v.goal ? {goal: v.goal} : {}), ...(v.stuck ? {stuck: v.stuck} : {}), ...(v.why ? {why: String(v.why).slice(0, 200)} : {}),
  ...(v.run ? {run: v.run.trace?.length} : {}), ...(v.found?.laws?.length ? {found: v.found.laws.map((f: any) => f.source ?? f.text)} : {})})

for (const p of protocols.filter(q => only ? only.includes(q.id) : true)) {
  const out: Record<string, unknown> = {id: p.id, ic3syn: p.ic3syn}
  try {
    const r = p.make(), laws = p.laws(r)
    if (!skip.has('search')) { const [v, t] = timed(() => proveRule(r, laws, {search: {ms}})); out.search = {...brief(v), ms: t} }
    if (!skip.has('broken')) { const bad = p.make(p.bug), [b, tb] = timed(() => proveRule(bad, p.laws(bad), {search: {ms}})); out.broken = {bug: p.bug, ...brief(b), ms: tb} }
  } catch (e) { out.error = String((e as Error).stack ?? e).slice(0, 600) }
  console.log(JSON.stringify(out))
}

// The layer on a rule the Python reader extracted: LiteLLM's per-session iteration limiter
// (research/langs/litellm/rules/MaxIterationsHandler.ts, read from litellm/proxy/hooks/max_iterations_limiter.py at
// v1.106.6 and checked against it by running both), every call of async_pre_call_hook at once over the shared counter.
// Its own step law, "every call of a limited session counts one", lifted to the step that writes the counter:
//   atomic          the in-memory path as it runs: _in_memory_increment awaits InMemoryCache.async_get_cache and
//                   async_set_cache (litellm/caching/in_memory_cache.py:179, 238), coroutines that never suspend, so
//                   asyncio runs no other call between the read and the write
//   read committed  the same code over a store whose get and set are calls that suspend (a remote cache without the
//                   Lua INCR LiteLLM uses for Redis): a call reads, another reads, both write the same count
//   bun research/distributed/litellm.ts [--ms 10000]
import {all, proveSteps} from '../../core/dsl.ts'
import {isolation, modelsOf, system} from '../../core/system.ts'
import {_PROXY_MaxIterationsHandlerRule as hook} from '../langs/litellm/rules/MaxIterationsHandler.ts'

const arg = (n: string) => { const i = process.argv.indexOf(`--${n}`); return i < 0 ? undefined : process.argv[i + 1] }
const ms = Number(arg('ms') ?? 10_000), COUNT = 'internal_usage_cache_session_iterations_count.value'
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Env = any
for (const level of ['atomic', 'read committed'] as const) {
  const h = isolation(hook.machine, level), split = level !== 'atomic'
  const commit = Object.keys(h.state).filter(s => s.startsWith('rd$')).length + 1
  const r = system(`LiteLLM max iterations (${level})`, {hook: split ? {rule: h, id: 't'} : h})
  // (a request's own input: as it came, or as its transaction kept it)
  const own = (b: Env, i: string) => (split ? b[`in$${i}`].at(b.t) : b[i])
  const law = r.stepLaw('every call of a limited session counts one',
    (b: Env, a: Env) => a[COUNT].at(own(b, 'get_session_id')).eq(b[COUNT].at(own(b, 'get_session_id')).plus(1)),
    (b: Env) => all(...(split ? [b['pc$'].at(b.t).eq(commit)] : []), own(b, 'get_session_id_none').eq(0), own(b, 'get_max_iterations_none').eq(0)))
  const t0 = performance.now(), v = proveSteps(r, [], [law], {search: {ms}})
  const verdict = v.proven && v.checked ? 'proven' : v.run ? `refuted (a run of ${v.run.trace.length} steps)` : 'unknown'
  console.log(`${level} | assumes ${modelsOf(r).map(m => m.name).join(', ')} | ${law.name} | ${verdict} | ${Math.round(performance.now() - t0)} ms`)
  if (v.run) for (const s of v.run.trace) console.log(`    ${JSON.stringify(s)}`)
}

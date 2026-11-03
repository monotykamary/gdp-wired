// Supplemental realization check: no injected scheduling gates, only observation of existing refs.
// Native Effect preemption (one uniform 32-operation budget) drives the actual concurrent calls.
import * as runtime from 'effect'
import {readFileSync, unlinkSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {pathToFileURL} from 'node:url'
import {createHash, randomUUID} from 'node:crypto'
import {instrumentEffect} from './replay_effect.ts'
import {holds, parseCall} from './replay.ts'

type Request = {file: string, entry: string, expr: string, run: string[], directory: string}
export async function nativeEffect(request: Request) {
  const source = readFileSync(request.file, 'utf8')
  const instrumented = instrumentEffect(source, request.entry, 'unused-native-observer')
  const code = instrumented.code.replace(/yield\* __mutation(?:Before|After)\(__mutationFiber,\s*\d+\);/g, '')
  if (/yield\* __mutation/.test(code)) throw new Error('a scheduling hook remains')
  const path = join(request.directory, `native-${randomUUID()}.ts`)
  const abort = new AbortController(), timer = setTimeout(() => abort.abort(), 10_000)
  try {
    writeFileSync(path, code)
    const module = await import(pathToFileURL(path).href) as Record<string, unknown>
    const service = await runtime.Effect.runPromise(module[request.entry] as runtime.Effect.Effect<Record<string, unknown>>)
    const calls = request.run.flatMap(line => {
      const text = line.replace(/^fiber \d+: /, '').replace(/, its step \d+ of \d+$/, '')
      return text.endsWith(')') ? [parseCall(text)] : []
    })
    if (calls.length < 2) throw new Error('concurrent realization needs two source calls')
    const operations = calls.map(call => {
      const names = instrumented.parameters[call.method]
      const fn = service[call.method]
      if (!names || typeof fn !== 'function' || names.length !== Object.keys(call.args).length || names.some(n => !Object.hasOwn(call.args, n))) throw new Error('source signature mismatch')
      return Reflect.apply(fn, service, names.map(n => call.args[n])) as runtime.Effect.Effect<unknown>
    })
    await runtime.Effect.runPromise(runtime.Effect.all(operations, {concurrency: 'unbounded'}).pipe(runtime.Effect.provideService(runtime.Scheduler.MaxOpsBeforeYield, 32)), {signal: abort.signal})
    const state: Record<string, unknown> = {}
    const refs = service.__mutationRefs as Record<string, {api: 'TxRef' | 'Ref', ref: unknown}>
    for (const [name, info] of Object.entries(refs)) {
      const read = info.api === 'TxRef' ? runtime.TxRef.get(info.ref as runtime.TxRef.TxRef<unknown>) : runtime.Ref.get(info.ref as runtime.Ref.Ref<unknown>)
      state[name] = await runtime.Effect.runPromise(read)
    }
    return {ok: true, broken: !holds(request.expr, state, state), sourceSha256: createHash('sha256').update(source).digest('hex'), calls, state, schedulingHooks: false, maxOpsBeforeYield: 32}
  } finally { clearTimeout(timer); abort.abort(); try { unlinkSync(path) } catch { /* creation can fail */ } }
}

if (import.meta.main) {
  try { console.log(JSON.stringify(await nativeEffect(JSON.parse(readFileSync(process.argv[2]!, 'utf8')) as Request))) }
  catch (error) { console.log(JSON.stringify({ok: false, broken: false, why: error instanceof Error ? error.message : 'native runtime failed'})); process.exitCode = 1 }
}

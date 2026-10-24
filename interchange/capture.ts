// The suite's certificates as interchange documents: preloaded into any bun run or test (bun --preload, bun test
// --preload), it takes every certificate a trusted entry point is handed, with the kernel's answer there, and at exit
// writes each as a document into $GDP_CAPTURE (a directory), with a summary of what it took and whether each read back to
// the same objects in this process (`identity`). Nothing on disk changes: kernel/kernel.ts, kernel/cyclic.ts and
// core/data.ts are wrapped as they load, in memory, each entry point renamed and called through a recorder that returns
// its answer unchanged. interchange/verify.ts then checks the documents again in other processes (the bundled checker,
// the WebAssembly module, the second checker) and compares.
//
// Taken: checkLaws, checkStepLaws (and as a liveness, when its step laws are a livenessParts'), checkKInduction,
// checkRecur, checkQMachine, checkQTree, refuseCyclic, checkCyclic, core/data.ts's terminations; a loop's, fold's or
// progress's goals (loopObligations, foldObligations, progressObligations) once each has had a tree checked; and goals
// checked alone (check called from outside the kernel), the first 300 and one in 40 after that. Each kind past
// GDP_CAPTURE_MAX (2,000) is counted, not kept.
import {plugin} from 'bun'
import {mkdirSync, readFileSync, writeFileSync} from 'node:fs'
import {basename, join} from 'node:path'

const dir = process.env.GDP_CAPTURE
type Rec = {fn: string, args: unknown[], out?: unknown, threw?: string}
const recs: Rec[] = [], seen: Record<string, number> = {}, max = Number(process.env.GDP_CAPTURE_MAX ?? 2000)
let quiet = false
const keep = (fn: string): boolean => {
  const n = (seen[fn] = (seen[fn] ?? 0) + 1)
  if (fn === 'check' || fn === 'checkQTree') return n <= 300 || (n % 40 === 0 && n <= 300 + 40 * max)
  return n <= max
}
// The recorder each wrapped entry point calls through: the answer (or the error) is the kernel's, returned unchanged.
const hook = {call(fn: string, f: (...a: unknown[]) => unknown, args: unknown[]): unknown {
  // (a check reached through a path argument is the kernel's own recursion, not an entry)
  const top = !quiet && !((fn === 'check' || fn === 'checkQTree') && args[2] !== undefined)
  const rec: Rec | undefined = top && keep(fn) ? {fn, args} : undefined
  try {
    const out = f(...args)
    if (rec) { rec.out = out; recs.push(rec) }
    return out
  } catch (e) {
    if (rec) { rec.threw = e instanceof Error ? e.message : String(e); recs.push(rec) }
    throw e
  }
}}
;(globalThis as Record<string, unknown>).__gdpCapture = hook

const wrap = (src: string, names: string[]): string => {
  let out = src
  for (const n of names) {
    const fnDecl = `export function ${n}(`, constDecl = `export const ${n} =`
    if (out.includes(fnDecl)) out = out.replace(fnDecl, `function ${n}(`)
    else if (out.includes(constDecl)) out = out.replace(constDecl, `const ${n} =`)
    else throw new Error(`capture: no export ${n}`)
    out += `\nconst ${n}$capture = (...a: any[]) => (globalThis as any).__gdpCapture.call(${JSON.stringify(n)}, ${n}, a)\nexport {${n}$capture as ${n}}\n`
  }
  return out
}
if (dir) plugin({name: 'gdp-capture', setup(build) {
  build.onLoad({filter: /kernel\/kernel\.ts$/}, args => ({loader: 'ts', contents: wrap(readFileSync(args.path, 'utf8'),
    ['check', 'checkLaws', 'checkStepLaws', 'checkKInduction', 'checkRecur', 'checkQTree', 'checkQMachine', 'loopObligations', 'foldObligations', 'progressObligations', 'livenessParts'])}))
  build.onLoad({filter: /kernel\/cyclic\.ts$/}, args => ({loader: 'ts', contents: wrap(readFileSync(args.path, 'utf8'), ['refuseCyclic', 'checkCyclic'])}))
  // core/data.ts's termination (not exported): renamed, and called through the recorder by its callers.
  build.onLoad({filter: /core\/data\.ts$/}, args => {
    const src = readFileSync(args.path, 'utf8')
    if (!src.includes('\nfunction termination(')) throw new Error('capture: no termination in core/data.ts')
    return {loader: 'ts', contents: `${src.replace('\nfunction termination(', '\nfunction termination$raw(')}\nfunction termination(ring: any, why: any): any { return (globalThis as any).__gdpCapture.call('termination', termination$raw, [ring, why]) }\n`}
  })
}})

// The reader and the kernel, loaded now (wrapped: the plugin is in place), the very modules the run imports.
const fmt = dir ? await import('./format.ts') : undefined, k = dir ? await import('../kernel/kernel.ts') : undefined, cyc = dir ? await import('../kernel/cyclic.ts') : undefined

// --- at exit: each record as a certificate, written --------------------------------------------------------------------
type Answer = boolean | string
const answerOf = (r: Rec): Answer => (r.threw !== undefined ? `throws: ${r.threw}` : r.fn === 'refuseCyclic' ? r.out === undefined : r.out === true)
// The identity a round trip keeps: the same values, a field holding undefined the same as no field, and -0 the same as
// 0 (JSON has no -0, and the kernel reads it as 0: k(-0) is {}, BigInt(-0) is 0n). Prototypes aside, as JSON has none.
const same = (a: unknown, b: unknown): boolean => {
  if (a === b) return true
  if (typeof a !== 'object' || typeof b !== 'object' || a === null || b === null) return false
  if (Array.isArray(a) !== Array.isArray(b)) return false
  if (Array.isArray(a)) return a.length === (b as unknown[]).length && a.every((x, i) => same(x, (b as unknown[])[i]))
  const ka = Object.keys(a).filter(k => (a as Record<string, unknown>)[k] !== undefined), kb = Object.keys(b).filter(k => (b as Record<string, unknown>)[k] !== undefined)
  return ka.length === kb.length && ka.every(k => Object.hasOwn(b, k) && same((a as Record<string, unknown>)[k], (b as Record<string, unknown>)[k]))
}
// Where two values first differ (a path), for the summary.
const diff = (a: unknown, b: unknown, at: string): string => {
  if (same(a, b)) return ''
  if (typeof a !== 'object' || typeof b !== 'object' || a === null || b === null) return `${at}: ${String(JSON.stringify(a)).slice(0, 80)} vs ${String(JSON.stringify(b)).slice(0, 80)}`
  for (const key of new Set([...Object.keys(a), ...Object.keys(b)])) {
    const d = diff((a as Record<string, unknown>)[key], (b as Record<string, unknown>)[key], `${at}.${key}`)
    if (d) return d
  }
  return `${at}: (prototypes or hidden fields)`
}
// At exit; under bun test (which fires no exit event to a preload) after the last test file.
let flushed = false
if (dir && fmt && k && cyc) {
  process.on('exit', () => flush(fmt, k, cyc))
  if (process.env.NODE_ENV === 'test') { const t = await import('bun:test'); t.afterAll(() => flush(fmt, k, cyc)) }
}
function flush(fmt: typeof import('./format.ts'), k: typeof import('../kernel/kernel.ts'), cyc: typeof import('../kernel/cyclic.ts')): void {
  if (flushed || !dir) return
  flushed = true
  quiet = true
  const script = (process.argv[1] ?? 'run').replace(/^.*\/(?=[^/]+\/[^/]+$)/, '').replace(/[^\w.-]+/g, '_'), tag = `${script}-${process.pid}`
  mkdirSync(dir, {recursive: true})
  type Cert = import('./format.ts').Certificate
  const out: {cert: Cert, kernel: Answer, fn: string}[] = []
  // Goals made by a builder, each with the tree last checked against it.
  const treeOf = new Map<object, unknown>()
  for (const r of recs) if (r.fn === 'check' && r.args[0] && r.args[1]) treeOf.set(r.args[0] as object, r.args[1])
  const byName = (goals: {name: string}[]): Record<string, never> | undefined => {
    const trees: Record<string, never> = {}
    for (const g of goals) { const t = treeOf.get(g); if (!t) return undefined; trees[g.name] = t as never }
    return trees
  }
  const composed = (goals: {name: string}[], trees: Record<string, unknown>): Answer => {
    try { return goals.every(g => trees[g.name] !== undefined && k.check(g as never, trees[g.name] as never)) } catch (e) { return `throws: ${e instanceof Error ? e.message : String(e)}` }
  }
  // A proof as the kernel reads it: its fields past the kernel's are not the certificate's (prove.ts keeps the cyclic
  // proof it made beside the trees; that proof is taken on its own, from refuseCyclic).
  const lawsProof = (p: unknown) => { const q = p as {instances: never, trees: never}; return q && typeof q === 'object' ? {instances: q.instances, trees: q.trees} : p }
  const stepProof = (p: unknown) => { const q = p as {laws: unknown, instances: never, perStep?: never, trees: never}; return q && typeof q === 'object' ? {laws: lawsProof(q.laws), instances: q.instances, ...(q.perStep ? {perStep: q.perStep} : {}), trees: q.trees} : p }
  const goalOf = (g: unknown): never => { const q = g as {name: string, hyps: unknown}; return (q && typeof q === 'object' ? {name: q.name, hyps: q.hyps} : g) as never }
  const lives = recs.filter(r => r.fn === 'livenessParts' && r.out)
  const lastLaws = (m: unknown, i: number) => { for (let j = i - 1; j >= 0; j--) { const r = recs[j]!; if (r.fn === 'checkLaws' && r.args[0] === m && r.out === true) return r } return undefined }
  for (const [i, r] of recs.entries()) {
    const a = r.args as [never, never, never, never]
    switch (r.fn) {
      // (a goal as the kernel reads it, its name and hypotheses: lean-kernel/emit.ts keeps a goal's zkeys beside them)
      case 'check': out.push({fn: r.fn, kernel: answerOf(r), cert: {kind: 'goals', goals: [{goal: goalOf(a[0]), tree: a[1]}]}}); break
      case 'checkQTree': out.push({fn: r.fn, kernel: answerOf(r), cert: {kind: 'qgoals', goals: [{goal: a[0], tree: a[1]}]}}); break
      case 'checkLaws': out.push({fn: r.fn, kernel: answerOf(r), cert: {kind: 'laws', machine: a[0], laws: a[1], proof: lawsProof(a[2]) as never}}); break
      case 'checkStepLaws': {
        out.push({fn: r.fn, kernel: answerOf(r), cert: {kind: 'stepLaws', machine: a[0], laws: a[1], stepLaws: a[2], proof: stepProof(a[3]) as never}})
        const sls = a[2] as unknown[], lv = lives.find(l => (l.out as {stay: unknown}).stay === sls[0])
        if (lv && sls.length === 2 + (lv.out as {helps: unknown[]}).helps.length) out.push({fn: 'checkStepLaws (a liveness)', kernel: answerOf(r), cert: {kind: 'liveness', machine: a[0], laws: a[1], liveness: lv.args[1] as never, proof: stepProof(a[3]) as never}})
        break
      }
      case 'checkKInduction': out.push({fn: r.fn, kernel: answerOf(r), cert: {kind: 'kInduction', machine: a[0], laws: a[1], kInduction: a[2], proof: stepProof(a[3]) as never}}); break
      case 'checkRecur': out.push({fn: r.fn, kernel: answerOf(r), cert: {kind: 'recur', loop: a[0], recur: a[1]}}); break
      case 'checkQMachine': out.push({fn: r.fn, kernel: answerOf(r), cert: {kind: 'qmachine', machine: a[0], laws: a[1], trees: a[2]}}); break
      case 'refuseCyclic': case 'checkCyclic': out.push({fn: r.fn, kernel: answerOf(r), cert: {kind: 'cyclic', cyclic: a[0]}}); break
      case 'loopObligations': case 'foldObligations': case 'progressObligations': {
        if (!Array.isArray(r.out)) break
        const trees = byName(r.out as {name: string}[])
        if (!trees) break
        const kernel = composed(r.out as {name: string}[], trees)
        if (r.fn === 'loopObligations') out.push({fn: r.fn, kernel, cert: {kind: 'loop', loop: a[0], laws: a[1], rank: a[2], trees}})
        else if (r.fn === 'foldObligations') out.push({fn: r.fn, kernel, cert: {kind: 'fold', fold: a[0], laws: a[1], trees}})
        else {
          const lp = lastLaws(a[0], i)
          const kp = typeof kernel === 'boolean' && lp ? kernel && lp.out === true : kernel
          out.push({fn: r.fn, kernel: lp ? kp : false, cert: {kind: 'progress', machine: a[0], laws: a[1], progress: a[3], instances: a[2], trees, ...(lp ? {lawsProof: lawsProof(lp.args[2]) as never} : {})}})
        }
        break
      }
      case 'termination': {
        const ts = r.out as {measure: {comps: {coef: number[], c: number}[]}, text: string, obligations: {law: {name: string}, proof?: {proven: boolean, proof?: unknown}}[]}[] | undefined
        const ring = a[0] as unknown as {name: string}[]
        if (!ts?.length) break
        const obligations = ts.flatMap((t, j) => t.obligations.flatMap(o => (o.proof?.proven && o.proof.proof ? [{function: ring[j]!.name, law: o.law.name, cyclic: o.proof.proof as never}] : [])))
        if (obligations.length !== ts.reduce((s, t) => s + t.obligations.length, 0)) break
        let kernel: Answer
        try { kernel = obligations.every(o => cyc.refuseCyclic(o.cyclic) === undefined) } catch (e) { kernel = `throws: ${e instanceof Error ? e.message : String(e)}` }
        out.push({fn: r.fn, kernel, cert: {kind: 'termination', functions: ring.map(f => f.name), text: ts[0]!.text, measures: ts.map(t => t.measure), obligations}})
        break
      }
    }
  }
  const summary: {script: string, seen: Record<string, number>, kept: Record<string, number>, written: Record<string, number>, identity: {ok: number, failed: number, first?: string},
    outside: Record<string, number>, outsideWhy: string[]} = {script, seen, kept: {}, written: {}, identity: {ok: 0, failed: 0}, outside: {}, outsideWhy: []}
  for (const [i, o] of out.entries()) {
    summary.kept[o.cert.kind] = (summary.kept[o.cert.kind] ?? 0) + 1
    let text: string
    try { text = JSON.stringify(fmt.toInterchange(o.cert, {capture: {kernel: o.kernel, fn: o.fn, script}})) } catch (e) {
      // Outside the format (a refusal's own test: a negative constant, a name it reserves): counted with the kernel's answer.
      const why = `${o.cert.kind} (kernel ${typeof o.kernel === 'string' ? 'throws' : o.kernel}): ${e instanceof Error ? e.message : String(e)}`.slice(0, 300)
      summary.outside[`${o.cert.kind}: kernel ${typeof o.kernel === 'string' ? 'throws' : o.kernel}`] = (summary.outside[`${o.cert.kind}: kernel ${typeof o.kernel === 'string' ? 'throws' : o.kernel}`] ?? 0) + 1
      if (summary.outsideWhy.length < 20) summary.outsideWhy.push(why)
      continue
    }
    // In this process (the same term columns): read back, the certificate is the one taken.
    let ok = false
    try { ok = same(fmt.fromInterchange(JSON.parse(text)), o.cert) } catch (e) { summary.identity.first ??= `${o.cert.kind} #${i}: ${e instanceof Error ? e.message : String(e)}` }
    if (ok) summary.identity.ok++
    else { summary.identity.failed++; summary.identity.first ??= `${o.cert.kind} #${i}: read back, not the same at ${diff(fmt.fromInterchange(JSON.parse(text)), o.cert, '')}` }
    writeFileSync(join(dir, `${tag}-${String(i).padStart(5, '0')}-${o.cert.kind}.json`), text)
    summary.written[o.cert.kind] = (summary.written[o.cert.kind] ?? 0) + 1
  }
  writeFileSync(join(dir, `${tag}.summary`), JSON.stringify(summary))
  void basename
}

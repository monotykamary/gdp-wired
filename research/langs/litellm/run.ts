// LiteLLM's rules extracted from a checkout and their laws proven: upstream at the pin, or a fork.
//
//   bun research/langs/litellm/run.ts --src <litellm checkout> [--python <python with its deps>] [--only <id>]
//                                     [--ms 60000] [--json <out.json>] [--write]
//
// Each item (specs.ts) is extracted with gdp-wired/extract-py, checked against the checkout's own code by running both
// (the python given must import it: `pip install -e '.[proxy]'` in the checkout), and each law proven of the rule:
// proven, refuted (with the request that breaks it) or unknown. A refusal names where the code left the subset and why.
// `--write` keeps the rules as printed (research/langs/litellm/rules/, what the corpus scores) when run on the pin.
import {existsSync, mkdirSync, writeFileSync} from 'node:fs'
import {join, resolve} from 'node:path'
import {proveSteps} from '../../../core/dsl.ts'
import {extractPython} from '../../../core/extract-py.ts'
import {toSource} from '../../../core/extract.ts'
import {PIN, SPECS} from './specs.ts'

const argv = process.argv.slice(2)
const opt = (k: string, d = '') => { const i = argv.indexOf(`--${k}`); return i < 0 ? d : argv[i + 1] ?? d }
const src = resolve(opt('src', process.env.LITELLM_SRC ?? ''))
if (!opt('src') && !process.env.LITELLM_SRC) throw new Error('--src <litellm checkout> (or $LITELLM_SRC)')
if (!existsSync(join(src, 'litellm'))) throw new Error(`${src} is not a LiteLLM checkout (no litellm/ in it)`)
const python = opt('python', process.env.LITELLM_PYTHON ?? 'python3'), ms = Number(opt('ms', '60000')), only = opt('only')
const HERE = import.meta.dir
type Out = {id: string, ok: boolean, refusals?: {where: string, what: string}[], mismatch?: string, notes: string[], evidence?: unknown, ms: number, laws: {name: string, verdict: 'proven' | 'refuted' | 'unknown' | 'error', ms: number, witness?: unknown, why?: string}[]}
const results: Out[] = []
for (const s of SPECS.filter(x => !only || x.id === only)) {
  const t0 = performance.now()
  const x = extractPython(join(src, s.file), {...s.opts, root: src, python})
  const out: Out = {id: s.id, ok: x.ok, notes: x.notes, ms: Math.round(performance.now() - t0), laws: [], ...(x.evidence ? {evidence: x.evidence} : {})}
  console.log(`\n${s.id}: ${x.ok ? 'extracted' : 'refused'} in ${out.ms} ms (reads ${s.reads})`)
  if (!x.ok) {
    out.refusals = x.refusals
    for (const r of x.refusals) console.log(`  refused at ${r.where}: ${r.what}`)
    results.push(out)
    continue
  }
  const ev = x.evidence!
  console.log(`  checked: ${ev.requests} requests from the start, ${ev.fromStates} from drawn states, ${ev.probes.steps} from the prover's witnesses, ${ev.coverage.hit} of ${ev.coverage.arms} arms`)
  if (argv.includes('--write')) {
    const dir = join(HERE, 'rules')
    mkdirSync(dir, {recursive: true})
    const name = s.id.split('/').pop()!.replace(/^_+/, '')
    writeFileSync(join(dir, `${name}.ts`), `// ${s.id}: extracted from ${PIN.repo} ${PIN.tag} (${PIN.commit}), ${s.reads}. ${PIN.licence}, (c) ${PIN.author}.\n// Boundary: ${s.boundary}.\n${toSource(x).replace(/from 'gdp-wired'/, "from '../../../../core/dsl.ts'")}`)
  }
  for (const l of s.laws) {
    const t1 = performance.now()
    let verdict: Out['laws'][number]['verdict'] = 'error', witness: unknown, why: string | undefined
    try {
      const v = proveSteps(x.rule as never, x.invariants ?? [], [l.law(x.rule as never)], {search: {ms}})
      verdict = v.proven ? 'proven' : v.witness || v.run ? 'refuted' : 'unknown'
      witness = v.witness ?? v.run
      why = v.why
    } catch (e) { why = (e as Error).message }
    const lms = Math.round(performance.now() - t1)
    out.laws.push({name: l.name, verdict, ms: lms, ...(witness ? {witness} : {}), ...(why ? {why} : {})})
    console.log(`  ${verdict.padEnd(8)} ${l.name} (${lms} ms)${verdict === 'refuted' ? `: ${JSON.stringify(witness)}` : verdict === 'error' || verdict === 'unknown' ? `: ${why ?? ''}` : ''}`)
  }
  results.push(out)
}
const jsonOut = opt('json')
if (jsonOut) writeFileSync(jsonOut, `${JSON.stringify({pin: PIN, src, results}, null, 1)}\n`)

// Real C projects' rules extracted at their pinned versions and their laws proven.
//
//   bun research/langs/c/run.ts [--src <dir>] [--only <id>] [--ms 60000] [--json <out>] [--write]
//
// Each project is fetched at its pin (a tarball) into <dir> (default runs/langs/c/src, not committed) unless it is
// there, extracted with gdp-wired's C front end (clang reads it with the project's flags; the check compiles it beside
// a generated harness), and each law proven of the rule: proven, refuted (with the request that breaks it) or unknown.
// `--write` keeps the rules as printed (research/langs/c/rules/), which the corpus scores.
import {execFileSync} from 'node:child_process'
import {existsSync, mkdirSync, writeFileSync} from 'node:fs'
import {join, resolve} from 'node:path'
import {proveRule, proveSteps} from '../../../core/dsl.ts'
import {extractC} from '../../../core/extract-c.ts'
import {toSource} from '../../../core/extract.ts'
import {SPECS} from './specs.ts'

const argv = process.argv.slice(2)
const opt = (k: string, d = '') => { const i = argv.indexOf(`--${k}`); return i < 0 ? d : argv[i + 1] ?? d }
const HERE = import.meta.dir, src = resolve(opt('src', join(HERE, '../../../runs/langs/c/src'))), ms = Number(opt('ms', '60000')), only = opt('only')
mkdirSync(src, {recursive: true})
const results: unknown[] = []
for (const s of SPECS.filter(x => !only || x.id === only)) {
  const dir = join(src, `${s.project}-${s.version}`)
  if (!existsSync(join(dir, s.file))) {
    mkdirSync(dir, {recursive: true})
    execFileSync('sh', ['-c', `curl -sfL -A gdp-wired '${s.tarball}' | tar x${s.tarball.endsWith('.xz') ? 'J' : 'z'} -C '${dir}' --strip-components=1`])
  }
  const t0 = performance.now()
  const x = extractC(join(dir, s.file), {...s.opts, flags: s.flags.map(f => f.replace(/^-I(?!\/)/, `-I${dir}/`)), root: dir})
  console.log(`\n${s.id}: ${x.ok ? 'extracted' : 'refused'} in ${Math.round(performance.now() - t0)} ms (${s.project} ${s.version}, reads ${s.reads})`)
  const out = {id: s.id, ok: x.ok, refusals: x.refusals, evidence: x.evidence, notes: x.notes, laws: [] as unknown[]}
  results.push(out)
  if (!x.ok) { for (const r of x.refusals) console.log(`  refused at ${r.where}: ${r.what}`); continue }
  const ev = x.evidence!
  console.log(`  checked: ${ev.requests} requests from the start, ${ev.fromStates} from drawn states, ${ev.probes.steps} from the prover's witnesses`)
  if (argv.includes('--write')) writeFileSync(join(HERE, 'rules', `${s.id.split('/').pop()!.replace(/\W+/g, '_')}.ts`), `// ${s.id}: extracted from ${s.project} ${s.version} (${s.repo}), ${s.reads}. ${s.licence}, (c) ${s.author}.\n${toSource(x).replace(/from 'gdp-wired'/, "from '../../../../core/dsl.ts'")}`)
  for (const l of s.laws) {
    const t1 = performance.now()
    let verdict = 'error', witness: unknown, why: string | undefined
    try {
      const law = l.law(x.rule as never)
      const v = 'then' in (law as object) ? proveSteps(x.rule as never, x.invariants ?? [], [law as never], {search: {ms}}) : proveRule(x.rule as never, [...(x.invariants ?? []), law as never], {search: {ms}})
      verdict = v.proven ? 'proven' : v.witness || v.run ? 'refuted' : 'unknown'; witness = v.witness ?? v.run; why = v.why
    } catch (e) { why = (e as Error).message }
    const lms = Math.round(performance.now() - t1)
    out.laws.push({name: l.name, verdict, ms: lms, ...(witness ? {witness} : {}), ...(why ? {why} : {})})
    console.log(`  ${verdict.padEnd(8)} ${l.name} (${lms} ms)${verdict === 'refuted' ? `: ${JSON.stringify(witness)}` : verdict !== 'proven' ? `: ${why ?? ''}` : ''}`)
  }
}
const j = opt('json')
if (j) writeFileSync(j, `${JSON.stringify(results, null, 1)}\n`)

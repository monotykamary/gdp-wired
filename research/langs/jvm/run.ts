// Java and Kotlin projects' rules extracted at their pinned versions and their laws proven.
//
//   bun research/langs/jvm/run.ts [--src <dir>] [--only <id>] [--ms 60000] [--json <out>] [--write]
//
// Each project's files are fetched from GitHub at the tag (and its release's jar from Maven Central, where the check
// runs the shipped classes) into <dir> (default runs/langs/jvm/src, not committed) unless they are there, extracted
// with gdp-wired's JVM front ends (the check compiles the file with javac or kotlinc, or loads the jar, and runs it
// through core/jvm/Harness.java), and each law proven of the rule: proven, refuted (with the request that breaks it)
// or unknown. `--write` keeps the rules as printed (research/langs/jvm/rules/), which the corpus scores. A JDK (17 or
// later; $JAVA_HOME) and, for Kotlin, kotlinc ($KOTLIN_HOME or on the PATH) are needed.
import {execFileSync} from 'node:child_process'
import {existsSync, mkdirSync, realpathSync, writeFileSync} from 'node:fs'
import {dirname, join, resolve} from 'node:path'
import {proveRule, proveSteps} from '../../../core/dsl.ts'
import {extractJvm} from '../../../core/extract-jvm.ts'
import {toSource} from '../../../core/extract.ts'
import {SPECS} from './specs.ts'

const argv = process.argv.slice(2)
const opt = (k: string, d = '') => { const i = argv.indexOf(`--${k}`); return i < 0 ? d : argv[i + 1] ?? d }
const HERE = import.meta.dir, src = resolve(opt('src', join(HERE, '../../../runs/langs/jvm/src'))), ms = Number(opt('ms', '60000')), only = opt('only')
const kotlinLib = () => {
  const home = process.env.KOTLIN_HOME ?? resolve(dirname(realpathSync(execFileSync('sh', ['-c', 'command -v kotlinc'], {encoding: 'utf8'}).trim())), '..')
  return [`${home}/lib`, `${home}/libexec/lib`].find(d => existsSync(`${d}/kotlin-stdlib.jar`))!
}
const fetch1 = (url: string, to: string) => { if (existsSync(to)) return; mkdirSync(dirname(to), {recursive: true}); execFileSync('curl', ['-sfL', '-A', 'gdp-wired', '-o', to, url]) }
const results: unknown[] = []
for (const s of SPECS.filter(x => !only || x.id === only)) {
  const dir = join(src, `${s.project}-${s.version}`)
  for (const f of s.files) fetch1(`https://raw.githubusercontent.com/${s.repo}/${s.tag}/${f}`, join(dir, f))
  const jars = (s.jars ?? []).map(j => (j === '$kotlin-stdlib' ? `${kotlinLib()}/kotlin-stdlib.jar` : (fetch1(`https://repo1.maven.org/maven2/${j}`, join(dir, 'jars', j.split('/').pop()!)), join(dir, 'jars', j.split('/').pop()!))))
  const t0 = performance.now()
  const x = extractJvm(s.lang, join(dir, s.files[0]!), {...s.opts, root: join(dir, s.root), classpath: jars})
  console.log(`\n${s.id}: ${x.ok ? 'extracted' : 'refused'} in ${Math.round(performance.now() - t0)} ms (${s.project} ${s.version}, reads ${s.reads})`)
  const out = {id: s.id, ok: x.ok, refusals: x.refusals, evidence: x.evidence, notes: x.notes, laws: [] as unknown[]}
  results.push(out)
  if (!x.ok) { for (const r of x.refusals) console.log(`  refused at ${r.where}: ${r.what}`); continue }
  const ev = x.evidence!
  console.log(`  checked: ${ev.requests} requests from the start, ${ev.fromStates} from drawn states, ${ev.probes.steps} from the prover's witnesses`)
  if (argv.includes('--write')) writeFileSync(join(HERE, 'rules', `${s.id.split('/').pop()!.replace(/\./g, '_')}.ts`), `// ${s.id}: extracted from ${s.project} ${s.version} (${s.repo} at ${s.tag}), ${s.reads}. ${s.licence}, (c) ${s.author}.\n${toSource(x).replace(/from 'gdp-wired'/, "from '../../../../core/dsl.ts'")}`)
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

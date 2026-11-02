// The trading corpus: open-source matching engines, order books and risk modules, their laws decided through the path
// users take. Each engine (engines/<id>.json) names its repository at a pinned commit, the files read, and what its user
// writes: `gdp: law` comment lines over the code's names (`edits`, each inserted above the first line matching
// `before`, at its indentation) and a gdp.toml beside the code (the methods read). Nothing else is written; the CLI
// does the rest. The schema is research/distributed/corpus's.
//
//   bun research/trading/corpus/run.ts <id> <checkout> [--ms 120000] [--json out.json]   one engine, its checkout
//   bun research/trading/corpus/run.ts --jobs [--ms 120000] > jobs.json                    a job per engine (boat)
//   bun research/trading/corpus/run.ts --collect <runs dir> [--md results.md]             the verdicts and times
import {existsSync, readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {dirname, join} from 'node:path'
import {spawnSync} from 'node:child_process'

export type Edit = {file: string, before: string, lines: string[]}
export type Engine = {id: string, repo: string, commit: string, licence: string, lang: string, kind: string, about: string,
  check: string[], setup?: string, toml?: string, tomlAt?: string, edits: Edit[], cli?: string[], env?: Record<string, string>, cpu?: number, memory?: number}
const HERE = import.meta.dir, argv = process.argv.slice(2)
const opt = (k: string, d = '') => { const i = argv.indexOf(`--${k}`); return i < 0 ? d : argv[i + 1] ?? d }
export const engines = (): Engine[] => readdirSync(join(HERE, 'engines')).filter(f => f.endsWith('.json')).sort().map(f => JSON.parse(readFileSync(join(HERE, 'engines', f), 'utf8')) as Engine)
// What the user writes: the comment lines and gdp.toml's lines (comments and blank lines aside).
export const written = (s: Engine) => ({lines: s.edits.reduce((n, e) => n + e.lines.length, 0), toml: (s.toml ?? '').split('\n').filter(l => l.trim() && !l.trim().startsWith('#')).length})

function apply(s: Engine, src: string) {
  for (const e of s.edits) {
    const f = join(src, e.file), lines = readFileSync(f, 'utf8').split('\n'), re = new RegExp(e.before)
    const i = lines.findIndex(l => re.test(l))
    if (i < 0) throw new Error(`${s.id}: no line of ${e.file} matches ${e.before}`)
    const ind = /^\s*/.exec(lines[i]!)![0]
    lines.splice(i, 0, ...e.lines.map(l => ind + l))
    writeFileSync(f, lines.join('\n'))
  }
  if (s.toml) writeFileSync(join(src, s.tomlAt ?? dirname(s.check[0]!), 'gdp.toml'), s.toml)
}

if (argv[0] === '--jobs') {
  const ms = opt('ms', '120000')
  console.log(JSON.stringify(engines().map(s => ({name: `trade-${s.id}`, cpu: s.cpu ?? 2, memory: s.memory ?? 8, timeout: 5400,
    cmd: `set -o pipefail; R=$PWD; rm -rf /tmp/eng-${s.id} && git clone -q --filter=blob:none ${s.repo} /tmp/eng-${s.id} && cd /tmp/eng-${s.id} && git checkout -q ${s.commit} && git rev-parse HEAD && (${s.setup ?? 'true'}) > /tmp/setup-${s.id}.log 2>&1; tail -3 /tmp/setup-${s.id}.log; cd $R && bun install --frozen-lockfile >/dev/null 2>&1 && bun research/trading/corpus/run.ts ${s.id} /tmp/eng-${s.id} --ms ${ms} --json /tmp/out-${s.id}.json; echo '--- json'; cat /tmp/out-${s.id}.json`})), null, 1))
} else if (argv[0] === '--collect') {
  const dir = argv[1]!, rows: string[] = []
  let proven = 0, broken = 0, unknown = 0, other = 0
  for (const s of engines()) {
    const log = join(dir, `trade-${s.id}.log`), text = existsSync(log) ? readFileSync(log, 'utf8') : '', w = written(s)
    const at = text.indexOf('--- json\n'), j = at < 0 ? undefined : (() => { try { return JSON.parse(text.slice(at + 9).split(/\n--- (stderr)/)[0]!) as {rules: {entry?: string, ok: boolean, refusals: {where: string, what: string}[], laws: {name: string, verdict: string, ms: number, why?: string}[]}[]} } catch { return undefined } })()
    const head = `| ${s.id} | ${s.lang} | ${s.kind}`
    if (!j) { rows.push(`${head} | — | no result | — | ${w.lines} + ${w.toml} |`); other++; continue }
    for (const r of j.rules.filter(x => x.laws.length)) {
      for (const l of r.laws) {
        if (l.verdict === 'proven') proven++; else if (l.verdict === 'broken') broken++; else if (l.verdict === 'unknown') unknown++; else other++
        const why = l.verdict === 'not read' ? ` (${(r.refusals[0] ? `${r.refusals[0].where.split('/').pop()}: ${r.refusals[0].what}` : l.why ?? '').replace(/\|/g, '/').slice(0, 160)})` : l.verdict === 'unknown' && l.why ? ` (${l.why.slice(0, 100)})` : ''
        rows.push(`${head} | ${r.entry ?? ''}: ${l.name} | ${l.verdict}${why} | ${(l.ms / 1000).toFixed(1)} s | ${w.lines} + ${w.toml} |`)
      }
    }
  }
  const md = [`${proven} proven, ${broken} refuted, ${unknown} unknown, ${other} not read or no result`, '',
    '| Engine | Language | Kind | Law | Verdict | Time | Written (comment lines + gdp.toml lines) |', '| --- | --- | --- | --- | --- | --- | --- |', ...rows].join('\n')
  if (opt('md')) writeFileSync(opt('md'), `${md}\n`)
  console.log(md)
} else {
  const [id, src] = argv
  const s = engines().find(x => x.id === id)
  if (!s || !src) throw new Error('run.ts <id> <checkout>')
  apply(s, src)
  const cli = join(HERE, '../../../core/cli.ts'), t0 = performance.now()
  const r = spawnSync('bun', [cli, 'check', ...s.check.map(f => join(src, f)), '--no-propose', '--ms', opt('ms', '120000'), ...(s.cli ?? []), ...(opt('json') ? ['--json'] : [])], {cwd: src, encoding: 'utf8', maxBuffer: 1 << 28, env: {...process.env, ...s.env}})
  if (opt('json')) writeFileSync(opt('json'), r.stdout)
  else process.stdout.write(r.stdout)
  process.stderr.write(r.stderr.slice(-4000))
  console.error(`${s.id}: ${Math.round(performance.now() - t0)} ms, exit ${r.status}`)
}

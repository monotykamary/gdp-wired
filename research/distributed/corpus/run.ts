// The distributed corpus: real services' pattern laws decided through the path users take. Each service
// (services/<id>.json) names its repository at a pinned commit, the files read, and what its user writes: `gdp: law`
// and `gdp: env` comment lines over the code's names (`edits`, each inserted above the first line matching `before`,
// at its indentation) and a gdp.toml beside the code. Nothing else is written; the CLI does the rest.
//
//   bun research/distributed/corpus/run.ts <id> <checkout> [--ms 60000] [--json out.json]   one service, its checkout
//   bun research/distributed/corpus/run.ts --jobs [--ms 60000] > jobs.json                    a job per service (boat)
//   bun research/distributed/corpus/run.ts --collect <runs dir> [--md results.md]            the verdicts and times
//   GDP_REPRO_DIR=<dir> bun research/distributed/corpus/run.ts --repro > jobs.json            a refutation run on the service's code
import {existsSync, readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {dirname, join} from 'node:path'
import {spawnSync} from 'node:child_process'

export type Edit = {file: string, before: string, lines: string[]}
export type Service = {id: string, repo: string, commit: string, licence: string, lang: string, patterns: string[], about: string,
  check: string[], setup?: string, toml?: string, tomlAt?: string, edits: Edit[], cli?: string[], env?: Record<string, string>,
  // A run of the refutation on the service's own code: a script of repro/, the containers it needs (each on its usual port), its setup.
  repro?: {script: string, containers?: string[], setup?: string}}
const HERE = import.meta.dir, argv = process.argv.slice(2)
const opt = (k: string, d = '') => { const i = argv.indexOf(`--${k}`); return i < 0 ? d : argv[i + 1] ?? d }
export const services = (): Service[] => readdirSync(join(HERE, 'services')).filter(f => f.endsWith('.json')).sort().map(f => JSON.parse(readFileSync(join(HERE, 'services', f), 'utf8')) as Service)
// What the user writes: the comment lines and gdp.toml's lines (comments and blank lines aside).
export const written = (s: Service) => ({lines: s.edits.reduce((n, e) => n + e.lines.length, 0), toml: (s.toml ?? '').split('\n').filter(l => l.trim() && !l.trim().startsWith('#')).length})

function apply(s: Service, src: string) {
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
  const ms = opt('ms', '60000')
  console.log(JSON.stringify(services().map(s => ({name: `dist-${s.id}`, cpu: 2, timeout: 3600,
    cmd: `set -o pipefail; R=$PWD; rm -rf /tmp/svc-${s.id} && git clone -q --filter=blob:none ${s.repo} /tmp/svc-${s.id} && cd /tmp/svc-${s.id} && git checkout -q ${s.commit} && git rev-parse HEAD && (${s.setup ?? 'true'}) > /tmp/setup-${s.id}.log 2>&1; tail -3 /tmp/setup-${s.id}.log; cd $R && bun install --frozen-lockfile >/dev/null 2>&1 && bun research/distributed/corpus/run.ts ${s.id} /tmp/svc-${s.id} --ms ${ms} --json /tmp/out-${s.id}.json; echo '--- json'; cat /tmp/out-${s.id}.json; echo '--- harness'; tail -40 /tmp/harness-${s.id}.log 2>/dev/null`})), null, 1))
} else if (argv[0] === '--repro') {
  // (each container started on the VM and removed after, whatever the script did)
  const port: Record<string, string> = {redis: '6379:6379', postgres: '5432:5432', memcached: '11211:11211'}
  console.log(JSON.stringify(services().filter(s => s.repro).map(s => {
    const cs = (s.repro!.containers ?? []).map((c, i) => ({name: `gdprepro${i}`, c, p: port[c.split(':')[0]!] ?? ''}))
    const up = cs.map(c => `docker rm -f ${c.name} >/dev/null 2>&1; docker run -d --name ${c.name} ${c.p ? `-p ${c.p}` : ''} ${c.c.startsWith('postgres') ? '-e POSTGRES_PASSWORD=gdp' : ''} ${c.c} >/dev/null`).join('; ')
    const down = cs.map(c => `docker rm -f ${c.name} >/dev/null 2>&1`).join('; ')
    // (the script read from $GDP_REPRO_DIR, kept out of the tree, and carried in the job itself)
    const dir = process.env.GDP_REPRO_DIR ?? join(HERE, 'repro'), file = join(dir, s.repro!.script.replace(/^repro\//, ''))
    if (!existsSync(file)) return undefined
    const b64 = Buffer.from(readFileSync(file)).toString('base64'), run = `/tmp/repro-${s.id}${s.repro!.script.endsWith('.py') ? '.py' : '.sh'}`
    return {name: `repro-${s.id}`, cpu: 2, timeout: 1800, cmd: `${cs.length ? `${up}; trap '${down}' EXIT; ` : ''}echo ${b64} | base64 -d > ${run}; rm -rf /tmp/svc-${s.id} && git clone -q --filter=blob:none ${s.repo} /tmp/svc-${s.id} && cd /tmp/svc-${s.id} && git checkout -q ${s.commit} && git rev-parse HEAD && (${s.repro!.setup ?? s.setup ?? 'true'}) > /tmp/setup-${s.id}.log 2>&1; tail -3 /tmp/setup-${s.id}.log; sleep 3; ${s.repro!.script.endsWith('.py') ? 'python3 -P' : 'bash'} ${run}`}
  }).filter(Boolean), null, 1))
} else if (argv[0] === '--collect') {
  const dir = argv[1]!, rows: string[] = [], all: unknown[] = []
  let proven = 0, broken = 0, unknown = 0, other = 0
  for (const s of services()) {
    const log = join(dir, `dist-${s.id}.log`)
    const text = existsSync(log) ? readFileSync(log, 'utf8') : ''
    const at = text.indexOf('--- json\n'), j = at < 0 ? undefined : (() => { try { return JSON.parse(text.slice(at + 9).split(/\n--- (harness|stderr)/)[0]!) as {rules: {entry?: string, ok: boolean, env?: string[], refusals: {what: string}[], laws: {name: string, verdict: string, ms: number, why?: string}[]}[]} } catch { return undefined } })()
    const w = written(s)
    if (!j) { rows.push(`| ${s.id} | ${s.lang} | ${s.patterns.join(', ')} | — | no result | — | ${w.lines} + ${w.toml} |`); other++; continue }
    all.push({id: s.id, rules: j.rules})
    // (the rules a law is stated on; the file's other classes, read and refused, aside)
    for (const r of j.rules.filter(x => x.laws.length)) {
      if (!r.ok && !r.laws.length) rows.push(`| ${s.id} | ${s.lang} | ${s.patterns.join(', ')} | ${r.entry ?? ''} | refused: ${r.refusals[0]?.what.slice(0, 120) ?? ''} | — | ${w.lines} + ${w.toml} |`)
      for (const l of r.laws) {
        if (l.verdict === 'proven') proven++; else if (l.verdict === 'broken') broken++; else if (l.verdict === 'unknown') unknown++; else other++
        rows.push(`| ${s.id} | ${s.lang} | ${s.patterns.join(', ')} | ${r.entry ?? ''}: ${l.name} | ${l.verdict}${l.why && l.verdict !== 'proven' && l.verdict !== 'broken' ? ` (${l.why.slice(0, 100)})` : ''} | ${(l.ms / 1000).toFixed(1)} s | ${w.lines} + ${w.toml} |`)
      }
    }
  }
  const md = [`${proven} proven, ${broken} refuted, ${unknown} unknown, ${other} not read or no result`, '',
    '| Service | Language | Patterns | Law | Verdict | Time | Written (comment lines + gdp.toml lines) |', '| --- | --- | --- | --- | --- | --- | --- |', ...rows].join('\n')
  if (opt('md')) writeFileSync(opt('md'), `${md}\n`)
  if (opt('json')) writeFileSync(opt('json'), JSON.stringify(all, null, 1))
  console.log(md)
} else {
  const [id, src] = argv
  const s = services().find(x => x.id === id)
  if (!s || !src) throw new Error('run.ts <id> <checkout>')
  apply(s, src)
  const cli = join(HERE, '../../../core/cli.ts')
  const t0 = performance.now()
  const r = spawnSync('bun', [cli, 'check', ...s.check.map(f => join(src, f)), '--no-propose', '--ms', opt('ms', '60000'), ...(s.cli ?? []), ...(opt('json') ? ['--json'] : [])], {cwd: src, encoding: 'utf8', maxBuffer: 1 << 28, env: {...process.env, ...s.env}})
  if (opt('json')) writeFileSync(opt('json'), r.stdout)
  else process.stdout.write(r.stdout)
  process.stderr.write(r.stderr.slice(-4000))
  console.error(`${s.id}: ${Math.round(performance.now() - t0)} ms, exit ${r.status}`)
}

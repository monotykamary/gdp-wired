// One item of the regulated corpus through the path a user takes: its files at the pinned commit (fetch.ts), what the
// user writes applied (laws.patch: `gdp: law`, `gdp: cite` and `gdp: env` comments only; gdp.toml beside the target),
// then `gdp-wired check <target> --json` (core/cli.ts, what `npx gdp-wired-cli check` runs), each law's verdict, time
// and citations kept, each proven law's certificate written (--cert).
//   bun research/regulated/corpus/run.ts <item> [--out runs/regulated/<name>] [--ms 60000] [--items <dir>]
import {cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, statSync, writeFileSync} from 'node:fs'
import {spawnSync} from 'node:child_process'
import {tmpdir} from 'node:os'
import {dirname, join, resolve} from 'node:path'
import {cacheOf, fetchItem, itemsIn} from './fetch.ts'

const here = import.meta.dir, root = join(here, '../../..')
const argv = process.argv.slice(2), opt = (k: string, d: string) => (argv.includes(`--${k}`) ? argv[argv.indexOf(`--${k}`) + 1]! : d)
const itemsDir = resolve(opt('items', join(here, 'items'))), out = opt('out', join(root, 'runs/regulated/local')), ms = opt('ms', '60000')
const name = argv[0]!, it = itemsIn(itemsDir).find(i => i.name === name)
if (!it) throw new Error(`no item ${name} in ${itemsDir}`)
if (!existsSync(cacheOf(it))) await fetchItem(it)

// What the user writes: the patch's added lines (each must be a comment of gdp's) and gdp.toml's lines.
const patch = join(itemsDir, name, 'laws.patch'), toml = join(itemsDir, name, 'gdp.toml')
const added = existsSync(patch) ? readFileSync(patch, 'utf8').split('\n').filter(l => l.startsWith('+') && !l.startsWith('+++')).map(l => l.slice(1)) : []
const notGdp = added.filter(l => l.trim() && !/^\s*(#|\/\/|--|\*|\/\*)\s*gdp:\s*(law|cite|env)\b/.test(l))
if (notGdp.length) throw new Error(`${name}: laws.patch adds more than gdp comments: ${notGdp[0]}`)
const tomlLines = existsSync(toml) ? readFileSync(toml, 'utf8').split('\n').filter(l => l.trim() && !l.trim().startsWith('#')) : []

const work = mkdtempSync(join(tmpdir(), `regulated-${name}-`))
cpSync(cacheOf(it), work, {recursive: true})
if (existsSync(patch)) {
  const p = spawnSync('git', ['apply', '-p1', '--unidiff-zero', patch], {cwd: work, encoding: 'utf8'})
  if (p.status !== 0) throw new Error(`${name}: laws.patch doesn't apply: ${p.stderr}`)
}
const target = join(work, it.target)
if (existsSync(toml)) cpSync(toml, join(statSync(target).isDirectory() ? target : dirname(target), 'gdp.toml'))
mkdirSync(out, {recursive: true})
const flags = Object.entries((it as {opts?: Record<string, string>}).opts ?? {}).flatMap(([k, v]) => [`--${k}`, v])
const t0 = performance.now()
const p = spawnSync('bun', [join(root, 'core/cli.ts'), 'check', target, '--json', '--no-propose', '--ms', ms, '--cert', join(out, 'certs', name), ...flags], {cwd: work, encoding: 'utf8', maxBuffer: 1 << 28})
const wall = Math.round(performance.now() - t0)
let res: {rules?: {entry?: string, ok: boolean, refusals: unknown[], checked?: string, laws: {name: string, verdict: string, ms: number, kind?: string, cites?: string[], run?: string[], replayed?: string, why?: string, where?: string, expr: string}[]}[], exit?: number} = {}
try { res = JSON.parse(p.stdout) } catch { /* (no JSON: the crash below) */ }
const record = {item: name, repo: it.repo, commit: it.commit, licence: it.licence, language: it.language, domain: it.domain, target: it.target,
  writes: {comments: added.filter(l => l.trim()).length, laws: added.filter(l => /gdp:\s*law\b/.test(l)).length, cites: added.filter(l => /gdp:\s*cite\b/.test(l)).length, toml: tomlLines.length},
  exit: p.status, wall, rules: (res.rules ?? []).map(r => ({entry: r.entry, ok: r.ok, refusals: r.refusals, checked: r.checked,
    laws: r.laws.map(l => ({name: l.name, expr: l.expr, where: l.where, kind: l.kind, verdict: l.verdict, ms: l.ms, cites: l.cites, run: l.run, replayed: l.replayed, why: l.why}))})),
  ...(res.rules ? {} : {crash: (p.stderr || p.stdout).slice(-3000)})}
writeFileSync(join(out, `${name}.json`), `${JSON.stringify(record, null, 1)}\n`)
for (const r of record.rules) {
  console.log(`${name}: ${r.entry ?? '(no entry)'} ${r.ok ? 'read' : `refused: ${JSON.stringify(r.refusals).slice(0, 300)}`}`)
  for (const l of r.laws) console.log(`  ${l.verdict.padEnd(8)} ${String(l.ms).padStart(7)} ms  ${l.name}${l.why ? `  (${l.why.slice(0, 200)})` : ''}`)
}
if (!res.rules) console.log(`${name}: crashed: ${record.crash}`)
// (the record on one line too, for a batch whose files stay on its machine: jobs.ts's logs, collect.ts)
console.log(`RECORD ${JSON.stringify(record)}`)

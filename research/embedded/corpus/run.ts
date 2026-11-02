// The embedded corpus run: each item's files fetched at its commit, its laws written in as `gdp: law` comments where
// items.ts says, its gdp.toml beside the file, and the CLI run on it as a user runs it (`gdp-wired check <file> --json`).
//
//   bun research/embedded/corpus/run.ts [--only <id>] [--ms 60000] [--src runs/embedded/src] [--json <out>] [--md <out>]
//   bun research/embedded/corpus/run.ts --jobs > jobs.json        one boat job an item (clang set up first)
//   bun research/embedded/corpus/run.ts --score <dir> [--md <out>] [--json <out>]   the jobs' results, scored
//
// The sources are fetched into --src (not committed) and copied into a fresh work tree per run, where the laws are
// inserted; nothing of the projects is vendored here. A law's verdict is the CLI's: proven, broken (with the run the
// code takes), unknown (with why) or not read; `wrong` counts a law proven that items.ts believes false or broken that
// it believes true.
import {execFileSync, spawnSync} from 'node:child_process'
import {cpSync, existsSync, mkdirSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {dirname, join, resolve} from 'node:path'
import {ITEMS, type Item} from './items.ts'

const argv = process.argv.slice(2), opt = (k: string, d = '') => { const i = argv.indexOf(`--${k}`); return i < 0 ? d : argv[i + 1] ?? d }
const HERE = import.meta.dir, ROOT = resolve(HERE, '../../..'), src = resolve(opt('src', join(ROOT, 'runs/embedded/src'))), ms = Number(opt('ms', '60000'))

export type LawResult = {item: string, name: string, expect: string, verdict: string, ms: number, why?: string, run?: string[], note?: string}
export type ItemResult = {id: string, project: string, domain: string, ok: boolean, refusals: {where: string, what: string}[], checked?: string, laws: LawResult[], seconds: number}

const raw = (it: Item, f: string) => `https://raw.githubusercontent.com/${it.repo}/${it.commit}/${f}`
// The item's files at its commit, fetched once.
export function fetchItem(it: Item): string {
  const dir = join(src, `${it.repo.replace('/', '__')}@${it.commit}`)
  for (const f of it.files) {
    const to = join(dir, f)
    if (existsSync(to)) continue
    mkdirSync(dirname(to), {recursive: true})
    execFileSync('curl', ['-sfL', '--retry', '3', '-A', 'gdp-wired', raw(it, f), '-o', to])
  }
  return dir
}
// A fresh work tree: the files, the stand-ins, the laws, gdp.toml.
function prepare(it: Item): {tree: string, target: string} {
  const from = fetchItem(it), tree = resolve(ROOT, 'runs/embedded/work', it.id), shim = it.shims ? join(HERE, 'shims', it.shims) : ''
  rmSync(tree, {recursive: true, force: true}); mkdirSync(tree, {recursive: true})
  for (const f of it.files) { mkdirSync(dirname(join(tree, f)), {recursive: true}); cpSync(join(from, f), join(tree, f)) }
  for (const [to, s] of Object.entries(it.overlays ?? {})) { mkdirSync(dirname(join(tree, to)), {recursive: true}); cpSync(join(shim, s), join(tree, to)) }
  for (const [to, d] of Object.entries(it.derive ?? {})) { mkdirSync(dirname(join(tree, to)), {recursive: true}); writeFileSync(join(tree, to), readFileSync(join(tree, d.from), 'utf8').replace(d.drop, '')) }
  const byFile = new Map<string, Item['laws']>()
  for (const l of it.laws) (byFile.get(l.file) ?? byFile.set(l.file, []).get(l.file)!).push(l)
  for (const [f, ls] of byFile) {
    let text = readFileSync(join(tree, f), 'utf8')
    for (const l of ls) {
      const at = text.indexOf(l.before)
      if (at < 0) throw new Error(`${it.id}: no ${JSON.stringify(l.before)} in ${f}`)
      text = `${text.slice(0, at)}// gdp: law ${l.law}\n${text.slice(at)}`
    }
    writeFileSync(join(tree, f), text)
  }
  const target = join(tree, it.target)
  writeFileSync(join(dirname(target), 'gdp.toml'), `${it.toml.replaceAll('{repo}', tree).replaceAll('{shim}', shim)}\n`)
  return {tree, target}
}

function runItem(it: Item): ItemResult {
  const t0 = performance.now(), {target} = prepare(it)
  const r = spawnSync('bun', [join(ROOT, 'core/cli.ts'), 'check', target, '--json', '--no-propose', '--ms', String(ms)], {cwd: dirname(target), encoding: 'utf8', maxBuffer: 1 << 28})
  const seconds = Math.round((performance.now() - t0) / 100) / 10
  let out: {rules: {ok: boolean, refusals: {where: string, what: string}[], checked?: string, laws: {name: string, verdict: string, ms: number, why?: string, run?: string[]}[]}[]}
  try { out = JSON.parse(r.stdout.slice(r.stdout.indexOf('{'))) } catch { return {id: it.id, project: it.project, domain: it.domain, ok: false, refusals: [{where: it.target, what: `the CLI's output isn't JSON: ${(r.stderr || r.stdout).slice(0, 400)}`}], laws: it.laws.map(l => law(it, l, {verdict: 'not read', ms: 0})), seconds} }
  const laws = out.rules.flatMap(x => x.laws), name = (l: Item['laws'][number]) => l.law.slice(0, l.law.indexOf(':')).trim()
  return {id: it.id, project: it.project, domain: it.domain, ok: out.rules.every(x => x.ok), refusals: out.rules.flatMap(x => x.refusals), checked: out.rules.find(x => x.checked)?.checked,
    laws: it.laws.map(l => law(it, l, laws.find(x => x.name === name(l)) ?? {verdict: 'not read', ms: 0, why: 'not in the output'})), seconds}
}
const law = (it: Item, l: Item['laws'][number], v: {verdict: string, ms: number, why?: string, run?: string[]}): LawResult =>
  ({item: it.id, name: l.law.slice(0, l.law.indexOf(':')).trim(), expect: l.expect, verdict: v.verdict, ms: v.ms, ...(v.why ? {why: v.why} : {}), ...(v.run ? {run: v.run} : {}), ...(l.note ? {note: l.note} : {})})

export function score(rs: ItemResult[]): string {
  const all = rs.flatMap(r => r.laws), n = (v: string) => all.filter(l => l.verdict === v).length
  const wrong = all.filter(l => (l.verdict === 'proven' && l.expect === 'broken') || (l.verdict === 'broken' && l.expect === 'proven'))
  const lines = [`${all.length} laws on ${rs.length} files of ${new Set(rs.map(r => r.project.replace(/ v[\d.]+$/, ''))).size} projects: ${n('proven')} proven, ${n('broken')} broken, ${n('unknown')} unknown, ${n('not read')} not read; wrong ${wrong.length}`, '',
    '| Item | Domain | Law | Expected | Verdict | Time |', '| --- | --- | --- | --- | --- | --- |']
  for (const l of all) lines.push(`| ${l.item} | ${rs.find(r => r.id === l.item)!.domain} | ${l.name} | ${l.expect} | ${l.verdict} | ${(l.ms / 1000).toFixed(1)} s |`)
  const refused = rs.filter(r => !r.ok)
  if (refused.length) lines.push('', ...refused.map(r => `- ${r.id} refused: ${r.refusals.map(x => `${x.where}: ${x.what}`).join('; ')}`))
  return lines.join('\n')
}

if (!import.meta.main) { /* imported: fetchItem and score only */ } else if (argv.includes('--jobs')) {
  process.stdout.write(`${JSON.stringify(ITEMS.map(it => ({name: it.id, cmd: `. research/langs/c/clang-setup.sh >/dev/null && bun install --frozen-lockfile >/dev/null 2>&1 && bun research/embedded/corpus/run.ts --only ${it.id} --ms ${ms} --json /tmp/r.json >/dev/null; cat /tmp/r.json`, timeout: 3600, cpu: 2})), null, 1)}\n`)
} else if (opt('score')) {
  const dir = resolve(opt('score')), rs: ItemResult[] = ITEMS.flatMap(it => { const f = join(dir, `${it.id}.log`); if (!existsSync(f)) return []; const t = readFileSync(f, 'utf8').split('\n--- stderr')[0]!; const i = t.indexOf('['); try { return JSON.parse(t.slice(i)) as ItemResult[] } catch { return [] } })
  if (opt('json')) writeFileSync(opt('json'), `${JSON.stringify(rs, null, 1)}\n`)
  const md = score(rs)
  if (opt('md')) writeFileSync(opt('md'), `${md}\n`)
  process.stdout.write(`${md}\n`)
} else {
  const rs = ITEMS.filter(it => !opt('only') || it.id === opt('only')).map(it => { const r = runItem(it); process.stderr.write(`${it.id}: ${r.laws.map(l => `${l.name} ${l.verdict}`).join(', ')} (${r.seconds} s)\n`); return r })
  if (opt('json')) writeFileSync(opt('json'), `${JSON.stringify(rs, null, 1)}\n`)
  if (opt('md')) writeFileSync(opt('md'), `${score(rs)}\n`)
}

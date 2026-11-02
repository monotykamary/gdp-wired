// A batch's records (each job's `RECORD <json>` line, run.ts) into results.json and the table in results.md.
//   bun research/regulated/corpus/collect.ts runs/regulated/<name> [--write]
import {existsSync, readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'

type Law = {name: string, expr: string, where?: string, kind?: string, verdict: string, ms: number, cites?: string[], run?: string[], replayed?: string, why?: string}
type Rec = {item: string, repo: string, commit: string, licence: string, language: string, domain: string, target: string, writes: {comments: number, laws: number, cites: number, toml: number},
  exit: number, wall: number, rules: {entry?: string, ok: boolean, refusals: {where: string, what: string}[], checked?: string, laws: Law[]}[], crash?: string}
const dir = process.argv[2]!, here = import.meta.dir
const recs: Rec[] = readdirSync(dir).filter(f => f.endsWith('.log')).sort().flatMap(f => readFileSync(join(dir, f), 'utf8').split('\n').filter(l => l.startsWith('RECORD ')).map(l => JSON.parse(l.slice(7)) as Rec))
// (a law not read carries no citation in the CLI's output: its citations as the item's patch states them)
for (const r of recs) {
  const patch = join(here, 'items', r.item, 'laws.patch'), cites = existsSync(patch) ? readFileSync(patch, 'utf8').split('\n').flatMap(l => { const m = /^\+.*gdp:\s*cite\s+([^:]+?)\s*:\s*(.+?)\s*$/.exec(l); return m ? [[m[1]!, m[2]!] as const] : [] }) : []
  for (const u of r.rules) for (const l of u.laws) if (!l.cites?.length) { const cs = cites.filter(([n]) => n === l.name).map(([, t]) => t); if (cs.length) l.cites = cs }
}
const laws = recs.flatMap(r => r.rules.flatMap(u => u.laws.map(l => ({r, u, l}))))
const n = (v: string) => laws.filter(x => x.l.verdict === v).length
const md = [`${recs.length} codebases, ${laws.length} laws: ${n('proven')} proven, ${n('broken')} broken, ${n('unknown')} unknown, ${n('not read')} not read.`, '',
  '| Item | Language | Rule | Law | Verdict | Time | Cites |', '| --- | --- | --- | --- | --- | --- | --- |',
  ...laws.map(({r, u, l}) => `| ${r.item} | ${r.language} | ${u.entry ?? ''}${u.ok ? '' : ' (refused)'} | ${l.name} | ${l.verdict} | ${(l.ms / 1000).toFixed(1)} s | ${(l.cites ?? []).map(c => c.replace(/\|/g, '/').replace(/"[^"]*"/, '"…"')).join('; ')} |`), '',
  '| Item | Rule | Refused where | Why |', '| --- | --- | --- | --- |',
  ...recs.flatMap(r => r.rules.filter(u => !u.ok).map(u => `| ${r.item} | ${u.entry ?? ''} | ${(u.refusals[0]?.where ?? '').split('/').pop()} | ${(u.refusals[0]?.what ?? '').replace(/\|/g, '/').replace(/\s+/g, ' ').slice(0, 160)} |`)), '',
  '| Item | Repository | Commit | Licence | Written (comments, laws, cites, gdp.toml lines) | Wall |', '| --- | --- | --- | --- | --- | --- |',
  ...recs.map(r => `| ${r.item} | ${r.repo} | ${r.commit.slice(0, 10)} | ${r.licence} | ${r.writes.comments}, ${r.writes.laws}, ${r.writes.cites}, ${r.writes.toml} | ${(r.wall / 1000).toFixed(1)} s |`)].join('\n')
console.log(md)
if (process.argv.includes('--write')) {
  writeFileSync(join(here, 'results.json'), `${JSON.stringify(recs, null, 1)}\n`)
  writeFileSync(join(here, 'results.md'), `# The regulated corpus: verdicts (${dir.split('/').pop()})\n\n${md}\n`)
}

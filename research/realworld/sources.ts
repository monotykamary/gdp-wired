// sources.json, the corpus's source code as a machine-readable list (for gen/extract, a TypeScript-to-rule extractor
// that measures itself on it): one entry per file an item mirrors, with the repo, the pinned commit, the path, the
// lines, the function or export, the licence and the author. `bun research/realworld/sources.ts > research/realworld/sources.json`.
// Items still being written list their sources in sources/*.json (the same entries); the corpus's own win.
import {readFileSync, readdirSync} from 'node:fs'
import {corpus} from './corpus.ts'
import type {Source} from './lib.ts'

type Entry = Source & {item: string, domain: string, role: 'rule' | 'also', url: string}
const url = (s: Source) => (s.repo.startsWith('http') ? s.repo : `https://github.com/${s.repo}/blob/${s.commit}/${s.path}${/^\d+(-\d+)?$/.test(s.lines) ? `#L${s.lines.replace('-', '-L')}` : ''}`)
const entries: Entry[] = corpus.flatMap(it => [it.source, ...(it.also ?? [])].map((s, i) => ({item: it.id, domain: it.domain, role: i ? 'also' as const : 'rule' as const, ...s, url: url(s)})))
const dir = new URL('./sources/', import.meta.url)
for (const f of readdirSync(dir).filter(f => f.endsWith('.json')).sort())
  for (const e of JSON.parse(readFileSync(new URL(f, dir), 'utf8')) as Entry[])
    if (!entries.some(x => x.item === e.item)) entries.push({...e, url: e.url ?? url(e)})
console.log(JSON.stringify(entries, null, 1))

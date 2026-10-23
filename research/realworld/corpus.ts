// The real-world corpus (README.md): every items/*.ts file's `items`, in the order of the files' names. Each item is
// one piece of open-source code (a rate limiter, an escrow, a session store, ...) written as a gdp-wired rule, with
// the laws a reviewer would ask about (lib.ts has the format).
import {readdirSync} from 'node:fs'
import type {RealItem} from './lib.ts'

const dir = new URL('./items/', import.meta.url)
const files = readdirSync(dir).filter(f => f.endsWith('.ts')).sort()
export const corpus: RealItem[] = []
for (const f of files) corpus.push(...((await import(new URL(f, dir).href)) as {items: RealItem[]}).items)
const ids = new Set<string>()
for (const it of corpus) {
  if (ids.has(it.id)) throw new Error(`two items named ${it.id}`)
  ids.add(it.id)
  const names = new Set<string>()
  for (const l of it.laws) { if (names.has(l.name)) throw new Error(`${it.id}: two laws named ${l.name}`); names.add(l.name) }
}

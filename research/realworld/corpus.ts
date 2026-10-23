// The real-world corpus (README.md): every items/*.ts file's `items`, in the order of the files' names. Each item is
// one piece of open-source code (a rate limiter, an escrow, a session store, ...) written as a gdp-wired rule, with
// the laws a reviewer would ask about (lib.ts has the format).
import {readdirSync} from 'node:fs'
import type {RealItem} from './lib.ts'

const dir = new URL('./items/', import.meta.url)
const files = readdirSync(dir).filter(f => f.endsWith('.ts')).sort()
export const corpus: RealItem[] = []
// A file that fails to load is named on stderr and left out (another file's items still load); `broken` lists them.
export const broken: {file: string, error: string}[] = []
for (const f of files) {
  try { corpus.push(...((await import(new URL(f, dir).href)) as {items?: RealItem[]}).items ?? []) } catch (e) { broken.push({file: f, error: String(e)}); console.error(`corpus: items/${f} left out: ${String(e).slice(0, 300)}`) }
}
const ids = new Set<string>()
for (const it of corpus) {
  if (ids.has(it.id)) throw new Error(`two items named ${it.id}`)
  ids.add(it.id)
  const names = new Set<string>()
  for (const l of it.laws) { if (names.has(l.name)) throw new Error(`${it.id}: two laws named ${l.name}`); names.add(l.name) }
}

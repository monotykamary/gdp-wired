// Each item's files at its pinned commit, fetched from GitHub into .cache/<item>/ (not committed: the code is its
// authors'), as the repository lays them out.
//   bun research/regulated/corpus/fetch.ts [<items dir>] [--only a,b]
import {existsSync, mkdirSync, readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {dirname, join} from 'node:path'

export type Item = {name: string, repo: string, commit: string, licence: string, language: string, domain: string, files: string[], target: string,
  args?: string[], what?: string}
const here = import.meta.dir
export const itemsIn = (dir = join(here, 'items')): Item[] => readdirSync(dir).filter(d => existsSync(join(dir, d, 'item.json'))).sort()
  .map(d => ({...JSON.parse(readFileSync(join(dir, d, 'item.json'), 'utf8')) as Item, name: d}))
export const cacheOf = (it: Item) => join(here, '.cache', it.name)
export async function fetchItem(it: Item): Promise<void> {
  const slug = it.repo.replace(/^https:\/\/github\.com\//, '')
  for (const f of it.files) {
    const to = join(cacheOf(it), f)
    if (existsSync(to)) continue
    const res = await fetch(`https://raw.githubusercontent.com/${slug}/${it.commit}/${f}`)
    if (!res.ok) throw new Error(`${it.name}: ${slug}@${it.commit}:${f}: ${res.status}`)
    mkdirSync(dirname(to), {recursive: true})
    writeFileSync(to, await res.text())
  }
}
if (import.meta.main) {
  const args = process.argv.slice(2), only = args.includes('--only') ? args[args.indexOf('--only') + 1]!.split(',') : undefined
  const dir = args[0] && !args[0].startsWith('--') ? args[0] : undefined
  for (const it of itemsIn(dir)) if (!only || only.includes(it.name)) { await fetchItem(it); console.log(`${it.name}: ${it.files.length} files at ${it.commit.slice(0, 10)}`) }
}

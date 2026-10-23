// The corpus's files at their pinned commits (research/extract/run.ts, verdicts.ts): fetched from GitHub once and
// cached under .cache/ (not committed: the code is its authors').
import {mkdirSync, readFileSync, writeFileSync, existsSync} from 'node:fs'
import {dirname, join} from 'node:path'

const here = import.meta.dir
export type At = {repo: string, commit: string, path: string}
export async function fetchSource(j: At): Promise<string> {
  const cache = join(here, '.cache', j.repo, j.commit, j.path)
  if (existsSync(cache)) return readFileSync(cache, 'utf8')
  const res = await fetch(`https://raw.githubusercontent.com/${j.repo}/${j.commit}/${j.path}`)
  if (!res.ok) throw new Error(`fetch ${j.repo}@${j.commit}:${j.path}: ${res.status}`)
  const text = await res.text()
  mkdirSync(dirname(cache), {recursive: true})
  writeFileSync(cache, text)
  return text
}
// The files the entry's relative imports name, fetched from the same commit (to depth 2, at most 12): keyed by their
// path beside the entry's. A name a file can't be found for stays unread (the extractor refuses it where it is read).
const dirOf = (p: string) => p.split('/').slice(0, -1).join('/')
const norm = (p: string) => { const out: string[] = []; for (const x of p.split('/')) { if (x === '..') out.pop(); else if (x && x !== '.') out.push(x) } return out.join('/') }
const rel = (fromDir: string, to: string) => { const a = fromDir ? fromDir.split('/') : [], b = to.split('/'); let i = 0; while (i < a.length && i < b.length - 1 && a[i] === b[i]) i++; return `${a.length - i ? '../'.repeat(a.length - i) : './'}${b.slice(i).join('/')}` }
export async function importsOf(j: At, code: string): Promise<Record<string, string>> {
  const files: Record<string, string> = {}, seen = new Set<string>([j.path])
  const queue: [string, string, number][] = []
  const specs = (text: string) => [...text.matchAll(/(?:from\s+|require\(\s*|import\s*\(\s*)['"](\.[^'"]+)['"]/g)].map(m => m[1]!)
  for (const sp of specs(code)) queue.push([j.path, sp, 1])
  while (queue.length && Object.keys(files).length < 12) {
    const [from, spec, depth] = queue.shift()!, base = norm(`${dirOf(from)}/${spec}`), bare = base.replace(/\.(js|jsx|mjs)$/, '')
    for (const cand of [base, `${bare}.ts`, `${bare}.tsx`, `${bare}.js`, `${bare}.jsx`, `${base}/index.ts`, `${base}/index.js`]) {
      if (seen.has(cand)) break
      let text: string | undefined
      try { text = await fetchSource({...j, path: cand}) } catch { continue }
      seen.add(cand)
      files[rel(dirOf(j.path), cand)] = text
      if (depth < 2) for (const sp of specs(text)) queue.push([cand, sp, depth + 1])
      break
    }
  }
  return files
}

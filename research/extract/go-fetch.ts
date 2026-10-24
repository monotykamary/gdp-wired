// A Go package at its pinned commit (research/extract/go-run.ts, go-verdicts.ts): a sparse checkout of the package's
// directory (and the files of the directories above it, so its go.mod), cached in .cache/git/ (not committed: the
// code is its authors').
import {existsSync, mkdirSync, readFileSync} from 'node:fs'
import {execFileSync} from 'node:child_process'
import {join, relative} from 'node:path'

const here = import.meta.dir
export function checkout(repo: string, commit: string, dir: string): string {
  const root = join(here, '.cache', 'git', repo, commit)
  const git = (...a: string[]) => execFileSync('git', a, {cwd: root, stdio: ['ignore', 'pipe', 'pipe'], timeout: 600_000, encoding: 'utf8'})
  if (!existsSync(join(root, '.git'))) {
    mkdirSync(root, {recursive: true})
    git('init', '-q'); git('remote', 'add', 'origin', `https://github.com/${repo}`)
    git('config', 'core.sparseCheckout', 'true')
    git('sparse-checkout', 'set', '--cone', dir || '.')
    git('fetch', '-q', '--depth', '1', '--filter=blob:none', 'origin', commit)
    git('checkout', '-q', 'FETCH_HEAD')
  } else {
    const have = git('sparse-checkout', 'list').split('\n').filter(Boolean)
    if (dir && !have.includes(dir)) { git('sparse-checkout', 'add', dir); git('checkout', '-q', 'FETCH_HEAD') }
  }
  return join(root, dir)
}

// The directories of the repo a package's imports live in (its module's own packages, and those of a module its go.mod
// replaces with a local path: Kubernetes's staging), added to the sparse checkout, so the reader reads their types
// (core/go/reader.go's foreignPackage, one level deep). True when any was added (read the package again then).
export function withImports(repo: string, commit: string, pkgDir: string, imports: string[]): boolean {
  const root = join(here, '.cache', 'git', repo, commit), git = (...a: string[]) => execFileSync('git', a, {cwd: root, stdio: ['ignore', 'pipe', 'pipe'], timeout: 600_000, encoding: 'utf8'})
  let mod = pkgDir
  while (!existsSync(join(mod, 'go.mod'))) { const up = join(mod, '..'); if (up === mod || !up.startsWith(root)) return false; mod = up }
  const text = readFileSync(join(mod, 'go.mod'), 'utf8'), rel = (d: string) => relative(root, d)
  const bases: [string, string][] = []
  const m = /^module\s+(\S+)/m.exec(text)
  if (m) bases.push([m[1]!.replace(/"/g, ''), mod])
  for (const r of text.matchAll(/^[ \t]*(?:replace[ \t]+)?([^\s(]\S*)(?:[ \t]+\S+)?[ \t]+=>[ \t]+(\.\.?\/\S+)/gm)) bases.push([r[1]!, join(mod, r[2]!)])
  const want = new Set<string>()
  for (const p of imports) for (const [b, d] of bases) if (p === b || p.startsWith(`${b}/`)) { want.add(rel(join(d, p.slice(b.length)))); break }
  const have = new Set(git('sparse-checkout', 'list').split('\n').filter(Boolean))
  const add = [...want].filter(d => d && !d.startsWith('..') && !have.has(d) && !existsSync(join(root, d)))
  if (!add.length) return false
  git('sparse-checkout', 'add', ...add); git('checkout', '-q', 'FETCH_HEAD')
  return true
}

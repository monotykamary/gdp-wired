// A Go package at its pinned commit (research/extract/go-run.ts, go-verdicts.ts): a sparse checkout of the package's
// directory (and the files of the directories above it, so its go.mod), cached in .cache/git/ (not committed: the
// code is its authors').
import {existsSync, mkdirSync} from 'node:fs'
import {execFileSync} from 'node:child_process'
import {join} from 'node:path'

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

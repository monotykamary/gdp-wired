import {expect, test} from 'bun:test'
import {createHash} from 'node:crypto'
import {execFileSync} from 'node:child_process'
import {copyFileSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {prepare} from './full-gate-runner'
import {worker} from './full-gate-worker'

const digest = (bytes: Buffer) => createHash('sha256').update(bytes).digest('hex')
async function refuses(promise: Promise<number>, message: string): Promise<void> {
  try { await promise } catch (error) {
    expect(error).toBeInstanceOf(Error)
    if (error instanceof Error) expect(error.message).toContain(message)
    return
  }
  throw Error('worker unexpectedly accepted invalid input')
}

test('opaque Git packs retain C sources and pinned submodules; tampering fails closed', async () => {
  const base = mkdtempSync(join(tmpdir(), 'full-gate-roundtrip-'))
  const previousOutput = process.env.SUPERCOMPUTER_OUTPUT_DIR
  const git = (cwd: string, ...args: string[]) => execFileSync('git', args, {
    cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'],
    env: {...process.env, GIT_CONFIG_NOSYSTEM: '1', GIT_CONFIG_GLOBAL: '/dev/null',
      GIT_AUTHOR_NAME: 'Gate fixture', GIT_AUTHOR_EMAIL: 'fixture@example.invalid',
      GIT_COMMITTER_NAME: 'Gate fixture', GIT_COMMITTER_EMAIL: 'fixture@example.invalid'},
  }).trim()
  try {
    const root = join(base, 'source'), vendor = join(base, 'vendor-source'), input = join(base, 'input')
    const commitMessage = join(base, 'commit-message.txt')
    writeFileSync(commitMessage, 'test: full gate fixture\n')
    mkdirSync(root); mkdirSync(vendor)
    git(vendor, 'init', '-q')
    writeFileSync(join(vendor, 'retained.c'), 'vendor source\n')
    git(vendor, 'add', '.'); git(vendor, '-c', 'core.hooksPath=/dev/null', 'commit', '-q', '-F', commitMessage)
    const vendorCommit = git(vendor, 'rev-parse', 'HEAD')
    git(root, 'init', '-q')
    mkdirSync(join(root, 'scripts/release-ci'), {recursive: true}); mkdirSync(join(root, 'supercomputer'))
    copyFileSync(join(import.meta.dir, 'full-gate-contract.ts'), join(root, 'scripts/release-ci/full-gate-contract.ts'))
    writeFileSync(join(root, '.gitignore'), 'node_modules\n')
    writeFileSync(join(root, 'package.json'), JSON.stringify({name: 'full-gate-fixture', version: '0.0.0', private: true}))
    writeFileSync(join(root, 'retained.c'), 'root source\n')
    writeFileSync(join(root, 'verify.ts'), `import {readFileSync} from 'node:fs'\nif(readFileSync('retained.c','utf8')!=='root source\\n'||readFileSync('vendor/pinned/retained.c','utf8')!=='vendor source\\n')throw Error('source missing or changed');console.log('canonical-source-ok')\n`)
    writeFileSync(join(root, 'supercomputer/suite.json'), JSON.stringify([{name: 'roundtrip', cmd: 'bun verify.ts', cwd: '.', timeout: 30}]))
    git(root, '-c', 'protocol.file.allow=always', 'submodule', 'add', '-q', vendor, 'vendor/pinned')
    git(root, 'add', '.'); git(root, '-c', 'core.hooksPath=/dev/null', 'commit', '-q', '-F', commitMessage)
    await prepare(root, input)
    const manifestBytes = readFileSync(join(input, 'manifest.json'))
    const manifest = JSON.parse(manifestBytes.toString('utf8'))
    const output = join(base, 'output'); mkdirSync(output)
    process.env.SUPERCOMPUTER_OUTPUT_DIR = output
    expect(await worker(input, digest(manifestBytes), 'roundtrip')).toBe(0)
    const provisioned = JSON.parse(readFileSync(join(output, 'PROVISIONED.json'), 'utf8'))
    expect(provisioned.commit).toBe(git(root, 'rev-parse', 'HEAD'))
    expect(provisioned.vendorPins).toEqual({'vendor/pinned': vendorCommit})
    expect(readFileSync(join(output, 'stdout.log'), 'utf8')).toContain('canonical-source-ok')

    const second = join(base, 'tampered-output'); mkdirSync(second)
    process.env.SUPERCOMPUTER_OUTPUT_DIR = second
    const archive = join(input, manifest.repositories[1].archive)
    const corrupt = Buffer.from(readFileSync(archive)); corrupt[512] = (corrupt[512] ?? 0) ^ 1
    writeFileSync(archive, corrupt)
    await refuses(worker(input, digest(manifestBytes), 'roundtrip'), 'archive mismatch')
    await refuses(worker(input, '0'.repeat(64), 'roundtrip'), 'manifest hash mismatch')
    await refuses(worker(input, digest(manifestBytes), 'omitted'), 'invalid manifest')
  } finally {
    if (previousOutput === undefined) delete process.env.SUPERCOMPUTER_OUTPUT_DIR
    else process.env.SUPERCOMPUTER_OUTPUT_DIR = previousOutput
    rmSync(base, {recursive: true, force: true})
  }
}, 90_000)

import {execFile} from 'node:child_process'
import {createHash} from 'node:crypto'
import {mkdtempSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {basename, join} from 'node:path'
import {leanLibraries, type AggregateMechanism} from './assets.ts'
import {exactAxioms, axiomCommand, theorem} from './audit.ts'

export const sha256 = (text: string | Uint8Array): string => createHash('sha256').update(text).digest('hex')
const release = '4.34.0', toolchain = `leanprover/lean4:v${release}`
// Official 4.34.0 release, not an RC or a toolchain with the same version prefix.
const pinned = /^Lean \(version 4\.34\.0, [\w.-]+, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b, Release\)$/

export type AggregateLeanReceipt = Readonly<{
  schema: 'gdp-wired/lean-aggregate/v1'
  inputSha256: string
  sourceSha256: string
  source: string
  libraries: Readonly<Record<string, string>>
  version: string
  theorem: typeof theorem
  axioms: readonly string[]
  log: string
}>

// Internal only: the public entry never accepts a Lean program, a log, an
// olean file, or a success marker from the caller.
export async function runExactLean(mechanism: AggregateMechanism, generated: string, inputSha256: string, ms: number): Promise<AggregateLeanReceipt> {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-aggregate-'))
  try {
    const until = performance.now() + ms
    const run = (args: string[]) => new Promise<string>((resolve, reject) => {
      const timeout = Math.floor(until - performance.now())
      if (timeout <= 0) { reject(new Error('Lean replay deadline expired.')); return }
      execFile('lean', args, {cwd: dir, env: {...process.env, ELAN_TOOLCHAIN: toolchain, LEAN_PATH: dir, LEAN_SRC_PATH: dir},
        encoding: 'utf8', timeout, killSignal: 'SIGKILL', maxBuffer: 4 * 1024 * 1024}, (error, stdout, stderr) => {
        const log = `${stdout}\n${stderr}`.trim()
        if (error || /\berror:|declaration uses 'sorry'/i.test(log))
          reject(new Error(`Lean ${args.join(' ')} refused: ${log.slice(0, 2400) || error?.message}.`))
        else resolve(log)
      })
    })
    const version = await run(['--version'])
    if (!pinned.test(version)) throw new Error(`Expected exact Lean ${release}; got ${version.slice(0, 240)}.`)
    const libraries: Record<string, string> = {}
    for (const path of leanLibraries[mechanism]) {
      const file = basename(path), body = readFileSync(new URL(path, import.meta.url))
      libraries[file] = sha256(body)
      writeFileSync(join(dir, file), body, {flag: 'wx'})
      await run(['-o', file.replace(/\.lean$/, '.olean'), file])
    }
    const source = `-- gdp-wired/lean-aggregate input sha256: ${inputSha256}\n${generated}${axiomCommand}`, file = 'Aggregate.lean'
    writeFileSync(join(dir, file), source, {flag: 'wx'})
    const log = await run([file]), axioms = exactAxioms(log)
    return {schema: 'gdp-wired/lean-aggregate/v1', inputSha256, source, sourceSha256: sha256(source), libraries, version, theorem, axioms, log}
  } finally { rmSync(dir, {recursive: true, force: true}) }
}

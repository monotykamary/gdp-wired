// Node-only command adapter. The capsule is data, never an executable module.
import {createHash} from 'node:crypto'
import {spawnSync} from 'node:child_process'
import {readFileSync, writeFileSync, lstatSync, realpathSync} from 'node:fs'
import {basename, isAbsolute, join, resolve, sep} from 'node:path'
import {lift} from '../lean-kernel/lift.ts'
import {auditLiftLog, gate} from '../lean-kernel/axiom-audit.ts'

export interface LiftArguments {capsule: string; source: string; out?: string; sha256?: string; emitOnly: boolean; json: boolean; timeoutMs: number}
export function parseLiftArguments(argv: string[]): LiftArguments {
  const positional: string[] = [], seen = new Set<string>()
  const options: LiftArguments = {capsule: '', source: '', emitOnly: false, json: false, timeoutMs: 1_800_000}
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i]!
    if (!a.startsWith('--')) {positional.push(a); continue}
    if (seen.has(a)) throw Error('duplicate lift option: ' + a)
    seen.add(a)
    if (a === '--emit-only') options.emitOnly = true
    else if (a === '--json') options.json = true
    else if (a === '--out' || a === '--sha256' || a === '--timeout-ms') {
      const value = argv[++i]
      if (!value || value.startsWith('--')) throw Error('missing value for ' + a)
      if (a === '--out') options.out = value
      else if (a === '--sha256') {if (!/^[a-f0-9]{64}$/.test(value)) throw Error('invalid capsule SHA-256'); options.sha256 = value}
      else {const n = Number(value); if (!Number.isSafeInteger(n) || n < 1 || n > 7_200_000) throw Error('invalid lift timeout'); options.timeoutMs = n}
    } else throw Error('unknown lift option: ' + a)
  }
  if (positional.length !== 2) throw Error('usage: gdp-wired lift <capsule> <source.json> [--out DIR] [--emit-only] [--sha256 HASH] [--timeout-ms N] [--json]')
  options.capsule = positional[0]!; options.source = positional[1]!
  return options
}
const sha = (data: string | Uint8Array) => createHash('sha256').update(data).digest('hex')
function verifyFiles(directory: string, files: Record<string, string>): void {
  if (!files || typeof files !== 'object' || !Object.keys(files).length) throw Error('missing emitted file hashes')
  const realRoot = realpathSync(directory)
  for (const [name, digest] of Object.entries(files)) {
    const path = resolve(directory, name)
    if (isAbsolute(name) || !path.startsWith(directory + sep) || !/^[a-f0-9]{64}$/.test(digest)) throw Error('invalid emitted path/hash: ' + name)
    const stat = lstatSync(path)
    if (!stat.isFile() || stat.isSymbolicLink() || !realpathSync(path).startsWith(realRoot + sep) || sha(readFileSync(path)) !== digest) throw Error('emitted file changed: ' + name)
  }
}
export async function liftMain(argv: string[]): Promise<number> {
  let output: string | undefined
  try {
    const args = parseLiftArguments(argv)
    output = resolve(args.out ?? basename(args.source).replace(/\.json$/, '') + '.lift')
    const manifest = lift(resolve(args.capsule), resolve(args.source), output, {expectedManifestSha256: args.sha256})
    if (args.emitOnly) {console.log(args.json ? JSON.stringify(manifest) : `EMITTED_NOT_CHECKED: ${output}`); return 0}
    const emission = readFileSync(join(output, 'EMITTED.json'))
    verifyFiles(output, manifest.files)
    const commands: {command: string[]; exitCode: number; stdoutSha256: string; stderrSha256: string}[] = []
    const run = (label: string, command: string[]) => {
      const result = spawnSync(command[0]!, command.slice(1), {cwd: output, env: {...process.env, GDP_LEAN_NATIVE: '0'}, encoding: 'utf8', timeout: args.timeoutMs, maxBuffer: 32 * 1024 * 1024, killSignal: 'SIGKILL'})
      const stdout = result.stdout ?? '', stderr = result.stderr ?? ''
      writeFileSync(join(output!, label + '.stdout.log'), stdout, {flag: 'wx'})
      writeFileSync(join(output!, label + '.stderr.log'), stderr, {flag: 'wx'})
      if (result.error || result.signal || result.status !== 0) throw Error(`${label} failed: ${result.error?.message ?? result.signal ?? result.status}`)
      commands.push({command, exitCode: result.status, stdoutSha256: sha(stdout), stderrSha256: sha(stderr)})
      return stdout + '\n' + stderr
    }
    const build = run('lift-build', ['lake', 'build'])
    const buildErrors = gate(build, [], false)
    if (buildErrors.length || /\berror:/.test(build)) throw Error(buildErrors.join('; ') || 'Lean build reported an error')
    const log = run('lift-root', ['lake', 'env', 'lean', 'BapaProof.lean'])
    const declarations = manifest as unknown as {familyTheorem?: string; requiredTheorems?: string[]; sourceProjection?: {sourceTheorems?: string[]}}
    const sourceTheorems = declarations.sourceProjection?.sourceTheorems
    if (!sourceTheorems?.length) throw Error('missing original source theorem coverage')
    const required = declarations.requiredTheorems ?? [declarations.familyTheorem!, ...sourceTheorems]
    const axioms = auditLiftLog(log, [readFileSync(join(output, 'BapaProof.lean'), 'utf8')], required)
    verifyFiles(output, manifest.files)
    if (sha(readFileSync(join(output, 'EMITTED.json'))) !== sha(emission)) throw Error('emission manifest changed during Lean execution')
    const receipt = {schema: 'gdp-lift-check/v1', status: 'SOURCE_CHECKED', scope: 'provided source machine and laws', emissionSha256: sha(emission), files: manifest.files, commands, checkedTheorems: axioms}
    writeFileSync(join(output, 'LIFT-CHECKED.json'), JSON.stringify(receipt, null, 2) + '\n', {flag: 'wx'})
    console.log(args.json ? JSON.stringify(receipt) : `SOURCE_CHECKED: ${sourceTheorems.join(', ')}\n${output}`)
    return 0
  } catch (error) {
    console.error(`gdp-wired lift: ${error instanceof Error ? error.message : String(error)}`)
    if (output) console.error(`No source acceptance. Any partial output is retained at ${output}.`)
    return 2
  }
}

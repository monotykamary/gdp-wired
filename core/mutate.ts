// Source mutation checks are tests, not proofs. Commands are argv arrays (never shell source).
// Only run a mutation configuration you trust, in a disposable checkout.
export type SourceEdit = {file: string, from: string, to: string, bug: string, name?: string}
export type MutationSuite = {name: string, command: string[]}
export type MutationConfig = {mutants: SourceEdit[], suites: MutationSuite[], lawSuite: string, cwd?: string, timeoutMs?: number}
export type SuiteReceipt = {status: 'caught' | 'missed' | 'error', exit: number | null, output: string, error?: string}
export type MutationRow = {mutant: string, bug: string, suites: Record<string, SuiteReceipt>}
export type MutationResult = {passed: boolean, rows: MutationRow[], markdown: string}

type FS = {
  readFileSync(path: string): Uint8Array,
  writeFileSync(path: string, data: string | Uint8Array): void,
  lstatSync(path: string): {isFile(): boolean, isSymbolicLink(): boolean},
}
type Process = {cwd(): string, getBuiltinModule(name: string): unknown}
type SpawnResult = {status: number | null, signal?: string | null, error?: Error, stdout?: string, stderr?: string}
type Spawn = (command: string, args: string[], options: {cwd: string, encoding: 'utf8', timeout: number, maxBuffer: number, killSignal: string, windowsHide: boolean}) => SpawnResult
const cell = (text: string) => text.replace(/\|/g, '\\|').replace(/[\r\n]+/g, ' ')
const sameBytes = (a: Uint8Array, b: Uint8Array) => a.length === b.length && a.every((v, i) => b[i] === v)

/** Compare each trusted source edit against each suite, restoring exact original bytes in finally.
 * Infrastructure errors (including timeout/signal/output overflow) never count as a killed mutant.
 * No process can restore after SIGKILL or power loss: use a disposable working tree.
 */
export function checkMutations(config: MutationConfig): MutationResult {
  if (!config || !Array.isArray(config.mutants) || !config.mutants.length || !Array.isArray(config.suites) || !config.suites.length) throw new Error('mutate needs nonempty mutants and suites')
  const names = config.suites.map(s => s.name)
  if (names.some(n => typeof n !== 'string' || !n.trim()) || new Set(names).size !== names.length || !names.includes(config.lawSuite)) throw new Error('mutate needs unique suite names and a designated lawSuite')
  for (const suite of config.suites) if (!Array.isArray(suite.command) || !suite.command.length || suite.command.some(s => typeof s !== 'string' || !s)) throw new Error(`suite ${suite.name}: command must be a nonempty argv array`)
  const timeout = config.timeoutMs ?? 120_000
  if (!Number.isSafeInteger(timeout) || timeout <= 0 || timeout > 2_147_483_647) throw new Error('timeoutMs must be a positive safe integer at most 2147483647')
  const proc = (globalThis as unknown as {process?: Process}).process
  if (!proc?.getBuiltinModule) throw new Error('mutation checks need Node.js 20.16+ or Bun')
  const fs = proc.getBuiltinModule('node:fs') as FS
  const path = proc.getBuiltinModule('node:path') as {resolve(...parts: string[]): string}
  const {spawnSync} = proc.getBuiltinModule('node:child_process') as {spawnSync: Spawn}
  const cwd = path.resolve(config.cwd ?? proc.cwd())
  const snapshots = new Map<string, {bytes: Uint8Array, text: string}>()
  const edits = config.mutants.map((edit, index) => {
    if (!edit || typeof edit.file !== 'string' || !edit.file || typeof edit.from !== 'string' || !edit.from || typeof edit.to !== 'string' || edit.to === edit.from || typeof edit.bug !== 'string' || !edit.bug.trim()) throw new Error(`mutant ${index + 1}: file, nonempty from, different to, and bug are required`)
    if (edit.name !== undefined && (typeof edit.name !== 'string' || !edit.name.trim())) throw new Error(`mutant ${index + 1}: name must be a nonempty string`)
    const file = path.resolve(cwd, edit.file), stat = fs.lstatSync(file)
    if (!stat.isFile() || stat.isSymbolicLink()) throw new Error(`mutant ${index + 1}: source must be a regular, non-symlink file`)
    let original = snapshots.get(file)
    if (!original) {
      const bytes = fs.readFileSync(file)
      original = {bytes, text: new TextDecoder('utf-8', {fatal: true, ignoreBOM: true}).decode(bytes)}
      snapshots.set(file, original)
    }
    const first = original.text.indexOf(edit.from)
    if (first < 0) throw new Error(`mutant ${index + 1}: from text not found in ${edit.file}`)
    if (original.text.indexOf(edit.from, first + 1) >= 0) throw new Error(`mutant ${index + 1}: from text is ambiguous in ${edit.file}`)
    return {edit, file, original, mutant: edit.name ?? String(index + 1)}
  })
  const run = (suite: MutationSuite): SuiteReceipt => {
    const p = spawnSync(suite.command[0]!, suite.command.slice(1), {cwd, encoding: 'utf8', timeout, maxBuffer: 1024 * 1024, killSignal: 'SIGKILL', windowsHide: true})
    const error = p.error?.message ?? (p.signal ? `terminated by ${p.signal}` : p.status === null ? 'no exit status' : undefined)
    return {status: error ? 'error' : p.status === 0 ? 'missed' : 'caught', exit: p.status, output: `${p.stdout ?? ''}${p.stderr ?? ''}`.slice(-65536), ...(error ? {error} : {})}
  }
  for (const suite of config.suites) {
    const result = run(suite)
    if (result.status !== 'missed') throw new Error(`suite ${suite.name} fails unmutated: ${result.error ?? `exit ${result.exit}`}\n${result.output}`)
  }
  const rows: MutationRow[] = []
  for (const {edit, file, original, mutant} of edits) {
    if (!sameBytes(fs.readFileSync(file), original.bytes)) throw new Error(`mutant ${mutant}: source changed since preflight; refusing to overwrite it`)
    const text = original.text.replace(edit.from, edit.to)
    try {
      fs.writeFileSync(file, text)
      const suites = Object.fromEntries(config.suites.map(suite => [suite.name, run(suite)]))
      rows.push({mutant, bug: edit.bug, suites})
    } finally {
      fs.writeFileSync(file, original.bytes)
    }
  }
  const header = ['Mutant', 'Bug', ...names]
  const table = [header, header.map(() => '---'), ...rows.map(row => [row.mutant, row.bug, ...names.map(n => row.suites[n]!.status)])]
  const markdown = table.map(row => `| ${row.map(cell).join(' | ')} |`).join('\n')
  const passed = rows.every(row => row.suites[config.lawSuite]!.status === 'caught' && Object.values(row.suites).every(r => r.status !== 'error'))
  return {passed, rows, markdown}
}

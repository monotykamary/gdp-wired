import type {C, E, Machine} from './machine.ts'

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
type Process = {cwd(): string, platform: string, kill(pid: number, signal: string): void, getBuiltinModule(name: string): unknown}
type SpawnResult = {pid?: number, status: number | null, signal?: string | null, error?: Error, stdout?: string, stderr?: string}
type Spawn = (command: string, args: string[], options: {cwd: string, encoding: 'utf8', timeout: number, maxBuffer: number, killSignal: string, windowsHide: boolean, detached: boolean}) => SpawnResult
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
  if (proc.platform === 'win32') throw new Error('mutation checks require POSIX process-group supervision')
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
  // Each suite owns a fresh POSIX process group. After the leader exits (including timeout), enumerate that
  // exact group's remaining PIDs, kill each exact PID, and await quiescence before touching source bytes.
  // A deliberately detached session or external writer is outside this trusted-command boundary.
  const supervise = (group: number | undefined): string | undefined => {
    if (!group || group <= 0) return undefined
    const until = Date.now() + 3000, pause = new Int32Array(new SharedArrayBuffer(4))
    do {
      const scan = spawnSync('ps', ['-eo', 'pid=,pgid=,stat='], {cwd, encoding: 'utf8', timeout: 2000, maxBuffer: 1024 * 1024, killSignal: 'SIGKILL', windowsHide: true, detached: false})
      if (scan.error || scan.status !== 0) return `cannot verify suite descendants: ${scan.error?.message ?? `ps exited ${scan.status}`}`
      const live = (scan.stdout ?? '').split('\n').map(line => line.trim().split(/\s+/)).filter(parts => Number(parts[1]) === group && !parts[2]?.startsWith('Z')).map(parts => Number(parts[0]))
      if (!live.length) return undefined
      for (const pid of live) {
        try { proc.kill(pid, 'SIGKILL') } catch (error) {
          if ((error as {code?: string}).code !== 'ESRCH') return `cannot stop suite descendant ${pid}: ${String(error)}`
        }
      }
      Atomics.wait(pause, 0, 0, 10)
    } while (Date.now() < until)
    return 'suite descendants did not stop before the cleanup deadline'
  }

  const run = (suite: MutationSuite): SuiteReceipt => {
    const p = spawnSync(suite.command[0]!, suite.command.slice(1), {cwd, encoding: 'utf8', timeout, maxBuffer: 1024 * 1024, killSignal: 'SIGKILL', windowsHide: true, detached: true})
    const cleanup = supervise(p.pid)
    const error = cleanup ?? p.error?.message ?? (p.signal ? `terminated by ${p.signal}` : p.status === null ? 'no exit status' : undefined)
    return {status: error ? 'error' : p.status === 0 ? 'missed' : 'caught', exit: p.status, output: `${p.stdout ?? ''}${p.stderr ?? ''}`.slice(-65536), ...(error ? {error} : {})}
  }
  for (const suite of config.suites) {
    const result = run(suite)
    if (result.status !== 'missed') throw new Error(`suite ${suite.name} fails unmutated: ${result.error ?? `exit ${result.exit}`}\n${result.output}`)
  }
  const rows: MutationRow[] = []
  for (const {edit, file, original, mutant} of edits) {
    if (!sameBytes(fs.readFileSync(file), original.bytes)) throw new Error(`mutant ${mutant}: source changed since preflight; refusing to overwrite it`)
    const text = original.text.replace(edit.from, () => edit.to)
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

export type DecisionMutationOptions = {
  /** File containing exactly one copy of render(machine); the runner verifies that match. */
  file: string
  /** Trusted, deterministic source/JSON printer. The same printer handles original and mutated terms. */
  render: (machine: Machine) => string
  /** Legal numeric encodings of input/parameter choices; never inferred from comparison literals. */
  choices?: Record<string, readonly number[]>
  maxCandidates?: number
}

/** Derive single-occurrence implementation mutations, not weakened laws or assumptions.
 * Pure scalar decisions only. The explicit printer bridges machine terms to the source artifact under test;
 * this does not claim an automatic inverse mapping from terms to arbitrary hand-written TypeScript.
 * Candidates may be equivalent: only the suites determine which laws kill them.
 */
export function deriveDecisionMutants(machine: Machine, options: DecisionMutationOptions): SourceEdit[] {
  const cap = options.maxCandidates ?? 64
  if (!Number.isSafeInteger(cap) || cap < 1 || cap > 1000) throw new Error('maxCandidates must be an integer from 1 to 1000')
  if (typeof options.file !== 'string' || !options.file || typeof options.render !== 'function') throw new Error('decision mutations need a file and deterministic render function')
  if (machine.history || [machine.maps, machine.step.maps, machine.fns, machine.sums, machine.counts, machine.leasts, machine.relations].some(x => x && Object.keys(x).length) || machine.inputMaps?.length) throw new Error('decision mutations require a pure scalar decision')
  const names = new Set([...machine.inputs, ...machine.params])
  for (const [name, values] of Object.entries(options.choices ?? {})) {
    if (!names.has(name) || !Array.isArray(values) || values.length < 2 || values.length > 1000 || values.some(x => !Number.isSafeInteger(x) || x < 0) || new Set(values).size !== values.length) throw new Error(`invalid choice encodings for ${name}`)
  }
  type Path = (string | number)[]
  const baseline = options.render(machine)
  if (typeof baseline !== 'string' || !baseline) throw new Error('render must return nonempty source text')
  // JSON terms have no object-identity semantics; break sharing so each path really is one occurrence.
  const serialized = JSON.stringify(machine)
  const result: SourceEdit[] = [], seen = new Set([baseline])
  let visited = 0
  const add = (kind: string, path: Path, replacement: E | C) => {
    if (result.length >= cap) return
    const variant = JSON.parse(serialized) as Machine
    let parent = variant as unknown as Record<string | number, unknown>
    for (const part of path.slice(0, -1)) parent = parent[part] as Record<string | number, unknown>
    parent[path[path.length - 1]!] = replacement
    const to = options.render(variant)
    if (typeof to !== 'string' || !to) throw new Error('render must return nonempty source text')
    if (seen.has(to)) return
    seen.add(to)
    result.push({file: options.file, from: baseline, to, name: `${kind}-${String(result.length + 1).padStart(3, '0')}`, bug: `${kind} at ${path.join('.')}`})
  }
  const visit = () => { if (++visited > 10000) throw new Error('decision has too many term occurrences') }
  const expr = (e: E, path: Path): void => {
    visit()
    if (e.op === 'var') { if (!names.has(e.name)) throw new Error(`decision reads non-input state ${e.name}`); return }
    if (e.op === 'const') return
    if (e.op === 'get') throw new Error('decision mutations do not support map or helper reads')
    if (e.op === 'if') {
      add('negate-guard', [...path, 'c'], {op: 'not', x: e.c})
      cond(e.c, [...path, 'c']); expr(e.then, [...path, 'then']); expr(e.else, [...path, 'else']); return
    }
    expr(e.a, [...path, 'a'])
    if ('b' in e) expr(e.b, [...path, 'b'])
  }
  const cond = (c: C, path: Path): void => {
    visit()
    if (c.op === 'all') throw new Error('decision mutations do not support quantified guards')
    if (c.op === 'flag') { if (!machine.step.flags?.[c.name]) throw new Error(`unknown decision flag ${c.name}`); return }
    if (c.op === 'not') { cond(c.x, [...path, 'x']); return }
    if (c.op === 'and' || c.op === 'or') {
      if (c.op === 'and') c.xs.forEach((_, i) => add('drop-conjunct', path, {...c, xs: c.xs.filter((_, j) => i !== j)}))
      c.xs.forEach((x, i) => cond(x, [...path, 'xs', i])); return
    }
    add('flip-comparison', path, c.op === '=' ? {op: 'not', x: c} : {...c, op: c.op === '<' ? '<=' : '<'})
    if (c.op === '=') {
      const pair = c.a.op === 'var' && c.b.op === 'const' ? [c.a, c.b] as const : c.b.op === 'var' && c.a.op === 'const' ? [c.b, c.a] as const : undefined
      if (pair) for (const value of options.choices?.[pair[0].name] ?? []) {
        if (value !== pair[1].value) add('widen-choice', path, {op: 'or', xs: [c, {op: '=', a: pair[0], b: {op: 'const', value}}]})
      }
    }
    expr(c.a, [...path, 'a']); expr(c.b, [...path, 'b'])
  }
  // Do not mutate preconditions, input-domain assumptions, initial state, or law/fact terms.
  for (const [name, flag] of Object.entries(machine.step.flags ?? {})) cond(flag, ['step', 'flags', name])
  for (const [name, value] of Object.entries(machine.step.state ?? {})) expr(value, ['step', 'state', name])
  return result
}

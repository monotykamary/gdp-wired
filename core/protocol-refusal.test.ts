// The original consensus_wo_decide positive proof job remains required and
// unresolved. These are producer-boundary controls, not a protocol proof run:
// inject incomplete verdicts into the real lean10 entrypoint in isolated child
// processes and require that no proof is claimed or export even attempted.
import {expect, test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join, resolve} from 'node:path'

const root = resolve(import.meta.dir, '..')
const entry = join(root, 'research/protocols/lean10.ts')
const dsl = join(root, 'core/dsl.ts')
const emitter = join(root, 'lean-kernel/emit.ts')
const cases = [
  {name: 'unresolved search', proven: false, checked: false},
  {name: 'unchecked prover claim', proven: true, checked: false},
  {name: 'checked flag without a proof', proven: false, checked: true},
  {name: 'partial unverified candidate laws', proven: false, checked: false, found: {laws: [{text: 'not a checked invariant', law: {name: 'unverified candidate', holds: {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 1}}}}]}},
]

for (const state of cases) test(`protocol export refuses ${state.name} without claiming consensus proved`, () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-protocol-refusal-'))
  const output = join(dir, 'consensus.lean'), calls = join(dir, 'calls'), exported = join(dir, 'export-called')
  const preload = join(dir, 'refusal-preload.ts')
  const verdict = {...state, stuck: 'unknown', why: 'controlled unresolved search; no protocol proof exists'}
  writeFileSync(preload, [
    "import {mock} from 'bun:test'",
    "import {appendFileSync,writeFileSync} from 'node:fs'",
    `const dsl = await import(${JSON.stringify(dsl)})`,
    `mock.module(${JSON.stringify(dsl)},()=>({...dsl,proveRule:()=>{appendFileSync(${JSON.stringify(calls)},'x');return ${JSON.stringify(verdict)}}}))`,
    `mock.module(${JSON.stringify(emitter)},()=>({certReport:{cyclic:[],fast:[],usual:[]},toLean:()=>{writeFileSync(${JSON.stringify(exported)},'attempted');throw new Error('unresolved protocol export attempted')}}))`,
  ].join('\n') + '\n')
  try {
    const env: Record<string, string | undefined> = {...process.env, LEAN10_TRIES: '2'}
    for (const key of ['LEAN10_FROM', 'LEAN10_SAVE', 'LEAN10_SOME', 'LEAN10_REPROVE', 'LEAN10_REPROVE_MS']) delete env[key]
    const child = spawnSync(process.execPath, ['--preload', preload, entry, 'consensus_wo_decide', '1', output], {
      cwd: root, env, encoding: 'utf8', timeout: 30_000, maxBuffer: 4 * 1024 * 1024,
    })
    expect(child.error).toBeUndefined()
    expect(child.signal).toBeNull()
    expect(child.status).toBe(0) // lean10 reports its refusal as data, never as a proof.
    const lines = child.stdout.trim().split('\n')
    expect(lines).toHaveLength(1)
    const report = JSON.parse(lines[0]!)
    expect(report.id).toBe('consensus_wo_decide')
    expect(report.tries).toBe(2)
    expect(report.search.verdict).toBe('unknown')
    expect(report.search.found).toBe(state.found?.laws.length ?? 0)
    expect(Object.hasOwn(report, 'export')).toBe(false)
    expect(readFileSync(calls, 'utf8')).toBe('xx')
    expect(existsSync(exported)).toBe(false)
    expect(existsSync(output)).toBe(false)
  } finally { rmSync(dir, {recursive: true, force: true}) }
}, 45_000)

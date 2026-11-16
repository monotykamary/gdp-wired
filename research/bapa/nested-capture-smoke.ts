// Run each mode in a fresh process: bun nested-capture-smoke.ts on|off.
// The optional compare mode consumes the two receipts; it never runs a prover.
import {createHash, randomUUID} from 'node:crypto'
import {readFileSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {fileURLToPath} from 'node:url'
import {installProfile, profile049} from './proof-worker.ts'

const mode = process.argv[2]
const out = process.env.SUPERCOMPUTER_OUTPUT_DIR
if (!out || !['on', 'off', 'compare'].includes(mode ?? '')) throw Error('usage: SUPERCOMPUTER_OUTPUT_DIR=... bun nested-capture-smoke.ts on|off|compare')
const json = (value: unknown) => JSON.stringify(value, (_key, v) => typeof v === 'bigint' ? v.toString() : v, 2) + '\n'
const read = (name: string) => JSON.parse(readFileSync(join(out, name), 'utf8'))
if (mode === 'compare') {
  const on = read('on.json'), off = read('off.json')
  if (on.status !== 'ok' || off.status !== 'ok' || on.publicCalls !== 1 || off.publicCalls !== 1 ||
      JSON.stringify(on.counterDeltas) !== JSON.stringify(off.counterDeltas) ||
      JSON.stringify(on.verdict) !== JSON.stringify(off.verdict) ||
      JSON.stringify(on.flags) !== JSON.stringify(off.flags)) throw Error('ON/OFF native parity failed')
  console.log(json({status: 'ok', counterParity: true, nativeVerdictParity: true, skolem: on.skolem, retention: on.retention}))
} else {
  // Nothing in core, the fixture, capture, or codec may load before this.
  const cleared = installProfile(process.env)
  const hash = (x: string | Uint8Array) => createHash('sha256').update(x).digest('hex')
  const sourceRef = (key: string) => {
    const value = process.env[key]
    if (value !== undefined && !/^[0-9a-f]{40}$/.test(value)) throw Error(`invalid ${key}`)
    return value ?? '0'.repeat(40)
  }
  let publicCalls = 0
  let report: Record<string, unknown> = {status: 'not-verified', mode, publicCalls}
  try {
    const commit = sourceRef('BAPA_SOURCE_COMMIT'), tree = sourceRef('BAPA_SOURCE_TREE')
    const fixturePath = fileURLToPath(new URL('./proof-skolem-fixture.ts', import.meta.url))
    const identity = {
      protocol: 'nested_skolem_capture', invocation: randomUUID(), sourceCommit: commit, sourceTree: tree,
      driverSha256: hash(readFileSync(fileURLToPath(import.meta.url))), inputSha256: hash(readFileSync(fixturePath)),
      runtimeSha256: hash(readFileSync(process.execPath)), profileSha256: hash(readFileSync(fileURLToPath(new URL('./profile-049.json', import.meta.url)))),
      workBudget: '24000000000', flags: {...profile049},
    }
    report = {...report, identity, identityAssurance: commit === '0'.repeat(40) || tree === '0'.repeat(40) ? 'test zero identity for missing source refs; not a proof identity claim' : 'process environment source refs, not independently verified', flags: {...profile049}, clearedFlagNames: cleared}
    const [{pipeline, safety}, {proveRule}, {workAdmissionSnapshot}] = await Promise.all([
      import('./proof-skolem-fixture.ts'), import('../../core/dsl.ts'), import('../../core/work-admission.ts'),
    ])
    const r = pipeline(), laws = [safety(r)]
    // Import the observer only for ON. Never read r.machine before proveRule.
    const capture = mode === 'on' ? (await import('./proof-capture-native.ts')).captureFinalInvocation : undefined
    const before = workAdmissionSnapshot()
    const invoke = () => { publicCalls++; return proveRule(r, laws, {search: {work: 24000000000}}) }
    const captured = capture ? capture(join(out, 'nested-capture-closure'), identity, {laws}, invoke) : undefined
    const verdict = captured ? captured.verdict : invoke()
    const after = workAdmissionSnapshot()
    const counterDeltas = Object.fromEntries(Object.entries(after.counters).map(([key, value]) => [key, String(BigInt(value) - BigInt(before.counters[key as keyof typeof before.counters]))]))
    report = {...report, publicCalls, verdict, counterDeltas, ...(captured ? {retention: captured.retention} : {})}
    if (!verdict.proven || !verdict.checked) throw Error('native verdict not proven and checked')
    if (captured) {
      if (!captured.retention.complete) throw Error('capture incomplete: ' + captured.retention.error)
      const {readFamilyCapsule} = await import('./proof-codec.ts')
      const {data} = readFamilyCapsule(join(out, 'nested-capture-closure'), captured.retention.manifestSha256,
        {maxBytes: 256 * 1024 * 1024, maxNodes: 2_000_000, maxStrings: 100_000, maxArrayLength: 2_000_000, maxShards: 1024}, () => {})
      const bundle = data as {route: string, verdict: {proven: boolean, checked: boolean}, proof?: unknown}
      if (!bundle.verdict.proven || !bundle.verdict.checked || !bundle.proof) throw Error('readback lacks checked provenance')
      const stack: unknown[] = [bundle.proof], seen = new Set<object>()
      let skolem = 0
      while (stack.length) {
        const node = stack.pop() as {kind?: string, context?: {kind?: string}, parents?: unknown[]} | undefined
        if (!node || typeof node !== 'object' || seen.has(node)) continue
        seen.add(node)
        if (node.kind === 'derived') {
          if (node.context?.kind === 'skolem') skolem++
          if (!Array.isArray(node.parents)) throw Error('invalid derived parents')
          stack.push(...node.parents)
        }
      }
      if (!skolem) throw Error('retained provenance has no actual Skolem derivation')
      report = {...report, skolem, capsuleRead: true, oneOuterEvent: true}
    }
    report = {...report, status: 'ok'}
  } catch (error) {
    report = {...report, publicCalls, error: error instanceof Error ? error.message : String(error)}
    process.exitCode = 1
  }
  writeFileSync(join(out, mode + '.json'), json(report))
  console.log(json(report))
}

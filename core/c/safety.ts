// C memory & UB safety (Stage 1): first-fault monitor over the checked C subset,
// independent kernel proof checking (checkLaws / checkKInduction), and native
// ASan/UBSan replay of every broken obligation.
import {checkKInduction, checkLaws, type Instances, type KInduction, type Tree} from '../../kernel/kernel.ts'
import {clock, proveLaw, proveLaws, withDeadline} from '../../kernel/prove.ts'
import {proveRule, type Rule} from '../dsl.ts'
import {quietly} from '../cyclic.ts'
import type {GoRead, TT} from '../extract-go.ts'
import * as I from '../extract-ir.ts'
import {Refusal, type Model, type Term, type Var} from '../extract-read.ts'
import {iteTerm, varTerm} from '../extract-step.ts'
import {fromSafetyModel} from '../extract.ts'
import {conjunction, proveKInduction, type KindProof} from '../kind.ts'
import {evalC, interpret, walk, type C, type E, type Law, type Machine} from '../machine.ts'
import {proofOutput, type ProofOutputNode, type PublicProofOutput} from '../proof-output.ts'
import {allowed} from '../watch.ts'
import {node, scrubbedClangEnv, type CRead, type CSafetyMacroConfig} from './reader.ts'
export type {CSafetyMacroConfig} from './reader.ts'

export type CSafetyKind = 'bounds' | 'overflow' | 'division'
export type CSafetySite = {where: string, kind: CSafetyKind, condition: I.B}
export type CSafetyStatus = 'proven' | 'broken' | 'unproven' | 'unchecked'
export type CSafetyRun = {params: Record<string, number>, trace: Record<string, unknown>[]}
export type CSafetyReplay = {built: boolean, requests: string[], reports: string[], states: string[], stderr: string, matchedSite: boolean}
export type CSafetyIssue = {where: string, kind: CSafetyKind, status: CSafetyStatus, replay?: CSafetyReplay, why?: string}
export type CSafetyResult = {
  status: CSafetyStatus,
  issues: CSafetyIssue[],
  assumptions: readonly string[],
  coveredFunctions: readonly string[],
  coveredHelpers?: readonly string[],
  uncheckedFunctions?: readonly string[],
  macroConfig?: CSafetyMacroConfig,
}

export type CSafetyProofBundle =
  | {kind: 'usual', machine: Machine, laws: Law[], proof: {instances: Record<string, Instances>, trees: Record<string, Tree>}}
  | {kind: 'kind', machine: Machine, assumed: Law[], kl: KInduction, kproof: KindProof}

export type CSafetyArtifact = {
  rule: Rule,
  machine: Machine,
  source: string,
  baseLaws: Law[],
  targetLaws: Law[],
  jointProof?: CSafetyProofBundle,
  siteProofs: (CSafetyProofBundle | undefined)[],
}

const safetyArtifacts = new WeakMap<CSafetyResult, CSafetyArtifact>()
export const cSafetyArtifactOf = (result: CSafetyResult): CSafetyArtifact | undefined => safetyArtifacts.get(result)

const assumptions = [
  'ABI, types & macro configuration (assumption): Clang runs in a scrubbed environment (CPATH, C_INCLUDE_PATH, CPLUS_INCLUDE_PATH, OBJC_INCLUDE_PATH, CCC_OVERRIDE_OPTIONS, etc. unset) with 8-bit char, 16-bit short, 32-bit int, and two’s-complement signed integers under the reported target triple, compiler, C standard (__STDC_VERSION__/std), -I/-D flags, and preprocessor/macro configuration (macroConfig; only covered scalar types up to 32 bits, constant lookup tables, and fixed arrays of known extent are modeled).',
  'Ownership, zeroed start & aliasing (assumption): Selected methods execute sequentially on one live, zero-initialized receiver (or single-declaration file-local static globals from their C initialization) with non-aliasing receiver and scalar out-parameters, no concurrency, and no external mutation from other translation units.',
  'Checked TU closure & failure paths (checked): System headers are classified strictly by resolved path under Clang’s built-in or -isystem search directories (in a scrubbed environment, never by linemarker flag 3), and an AST node is system only if both its spelling and expansion locations are system files. Any user-defined or -D macro expanded inside a system header, #pragma/_Pragma GCC/clang system_header, and #line/linemarker directives in user files are refused in all spellings. Every function with a body in any non-system file of the translation unit must be covered as a selected method or an inlined file-local static helper, or is refused as unchecked and named. Symbol aliases/weak/#pragma weak/file-scope __asm__/attributed or post-definition function declarations, non-system globals with pointers/fn-ptrs (including struct/array fields) or function-referencing initializers, bodyless prototypes taking the entry type or pointers, user-code preprocessing divergence across NDEBUG (undef/0/1), -O0/-O2/-Os (__OPTIMIZE__/__OPTIMIZE_SIZE__), -fsanitize=address,undefined (__SANITIZE_*), or DEBUG (undef/0/1/2), and configured failure returns (fails) after state writes are also refused.',
  'First-fault & replay scope: Only the first tracked array/table-bounds, signed-overflow, or division/remainder fault is checked. Broken obligations require site-matched ASan/UBSan replay (matchedSite); unproven sites are never claimed proven or broken. Abstract stutter on fault is a monitor convention, not native rollback.',
] as const
export const uncheckedCSafety = (
  issues: CSafetyIssue[] = [],
  coverage?: {coveredFunctions?: readonly string[], coveredHelpers?: readonly string[], uncheckedFunctions?: readonly string[], macroConfig?: CSafetyMacroConfig},
): CSafetyResult => ({
  status: 'unchecked',
  issues,
  assumptions,
  coveredFunctions: coverage?.coveredFunctions ?? [],
  ...(coverage?.coveredHelpers?.length ? {coveredHelpers: coverage.coveredHelpers} : {}),
  ...(coverage?.uncheckedFunctions?.length ? {uncheckedFunctions: coverage.uncheckedFunctions} : {}),
  ...(coverage?.macroConfig ? {macroConfig: coverage.macroConfig} : {}),
})

const limits = ({bits, signed}: {bits: number, signed: boolean}): [number, number] => signed ? [-(2 ** (bits - 1)), 2 ** (bits - 1) - 1] : [0, 2 ** bits - 1]

// Bind the alarm conditions to the real C input domain independently of the
// backend's accumulated refusals. A hit must never override a type restriction.
function inputDomain(read: GoRead, c: CRead): {domain: I.B, sorts: Record<string, 'nat' | 'int'>} {
  const m = read.model, event = m.inputs.find(v => v.name === m.event)
  const sorts: Record<string, 'nat' | 'int'> = {}
  if (!event || event.sort.k !== 'choice') throw new Refusal(m.file, 'C safety needs explicit event selectors')
  const selector: I.L = {op: 'var', name: event.name, values: event.sort.values}
  const seen = new Set([event.name])
  const boundScalar = (name: string, ty: TT | undefined): I.B => {
    if (!ty) throw new Refusal(m.file, 'C safety needs scalar inputs with a covered C type')
    seen.add(name)
    if (ty.k === 'bool') return I.T
    if (ty.k !== 'int' || !Number.isInteger(ty.bits) || ty.bits! < 1 || ty.bits! > 32 || typeof ty.signed !== 'boolean')
      throw new Refusal(m.file, 'C safety needs supported fixed-width integer inputs')
    sorts[name] = ty.signed ? 'int' : 'nat'
    const [lo, hi] = limits({bits: ty.bits!, signed: ty.signed}), e = I.nvar(name)
    return I.and(I.cmp('<=', I.num(lo), e), I.cmp('<=', e, I.num(hi)))
  }
  const domain = I.and(...read.methods.map(method => {
    const sel = I.is(selector, method.name)
    return I.or(I.not(sel), I.and(...method.params.map(({arg, t}) => {
      const ty = c.pkg.ttab[t]
      if (arg.k === 'input') return boundScalar(arg.name, ty)
      if (arg.k === 'rec' && ty?.k === 'ptr') {
        const box = c.pkg.ttab[ty.elem!]
        if (box?.box && box.fields?.length === 1) {
          const elem = c.pkg.ttab[box.fields[0]!.t]
          const val = arg.fields.find(([f]) => f === 'value')?.[1]
          if (!val) return I.T
          if (val.k === 'input') return boundScalar(val.name, elem)
        }
      }
      throw new Refusal(m.file, 'C safety needs scalar inputs or boxed scalar out-parameters with a covered C type')
    })))
  }))
  if (m.inputs.some(v => !seen.has(v.name)) || m.params.length) throw new Refusal(m.file, 'C safety does not admit inferred inputs or constructor parameters')
  return {domain, sorts}
}

export function monitorCSafety(m: Model, sites: readonly CSafetySite[], domain: I.B): {model: Model, alarmLaws: string[], alarmNames: (string | undefined)[]} {
  if (m.maps.length || Object.keys(m.mapWrites).length || m.seqs?.length || m.folds?.length || m.leasts?.length || m.lists?.some(d => d.len === undefined) || Object.values(m.listWrites ?? {}).some(ops => ops.some(o => o.op !== 'set')))
    throw new Refusal(m.file, 'C safety cannot frame maps, dynamic lists or collection folds at a fault')
  const names = new Set([...m.params, ...m.inputs, ...m.state].map(v => v.name))
  const lists = new Set((m.lists ?? []).map(d => d.name))
  const lengths = new Set([...lists].map(n => `${n}_len`))
  for (const site of sites) {
    const refs = I.varsOf(site.condition)
    if ([...refs.vars].some(n => !names.has(n) && !lengths.has(n)) || [...refs.maps].some(n => !lists.has(n))) throw new Refusal(site.where, 'a C safety site refers to missing or unsupported model state')
  }
  const reserved = new Set([...names, ...lists, ...lengths])
  let nextId = 0
  const alarms: Var[] = []
  const alarmNames = sites.map((s): string | undefined => {
    if (s.condition.op === 'const' && !s.condition.v) return undefined
    let name: string
    do { name = `cSafetyAlarm${++nextId}` } while (reserved.has(name))
    reserved.add(name)
    alarms.push({name, sort: {k: 'bool'}, role: 'state'})
    return name
  })
  const already = alarms.length ? I.or(...alarms.map(a => I.bvar(a.name))) : I.F
  // Do not infer an order from the site list: each condition is already
  // guarded by the backend's source-specific defined prefix.
  const hits = sites.map((s, j) => (alarmNames[j] ? I.and(I.not(already), domain, s.condition) : I.F))
  const liveHits = hits.filter((_, j) => alarmNames[j] !== undefined)
  const stutter = alarms.length ? I.or(already, ...liveHits) : I.F
  const init = {...m.init}, writes: Record<string, Term> = {...m.writes}
  if (alarms.length) for (const v of m.state) if (writes[v.name]) writes[v.name] = iteTerm(stutter, varTerm(v), writes[v.name]!)
  const listWrites = Object.fromEntries(Object.entries(m.listWrites ?? {}).map(([n, ops]) => [n, ops.map(o => ({...o, when: alarms.length ? I.and(I.not(stutter), o.when) : o.when}))]))
  const alarmLaws = sites.map((site, j) => {
    const name = alarmNames[j]
    if (!name) return `r.law(${JSON.stringify(`no first C ${site.kind} fault (static #${j + 1})`)}, () => all())`
    init[name] = {s: 'bool', e: I.F}
    writes[name] = {s: 'bool', e: I.or(I.bvar(name), hits[j]!)}
    return `r.law(${JSON.stringify(`no first C ${site.kind} fault (${name})`)}, ({${name}}) => ${name}.not())`
  })
  return {model: {...m, state: [...m.state, ...alarms], init, writes, listWrites,
    refuse: I.or(I.not(domain), alarms.length ? I.and(I.not(stutter), m.refuse) : m.refuse), laws: [...(m.laws ?? []), ...alarmLaws]}, alarmLaws, alarmNames}
}

const isArithFn = (name: string) => /^(?:div|mod)\$\d+$/.test(name)
function sameSafetyMachine(candidate: Machine, expected: Machine): boolean {
  const core = (m: Machine) => JSON.stringify({
    primitiveFailure: m.primitiveFailure,
    params: m.params, inputs: m.inputs, state: m.state, maps: m.maps,
    pre: m.pre, assume: m.assume, step: m.step, history: m.history, sums: m.sums,
    inputMaps: m.inputMaps, counts: m.counts, leasts: m.leasts,
  })
  if (core(candidate) !== core(expected)) return false
  const efns = expected.fns ?? {}, cfns = candidate.fns ?? {}
  for (const [k, v] of Object.entries(efns)) if (JSON.stringify(cfns[k]) !== JSON.stringify(v)) return false
  for (const k of Object.keys(cfns)) if (!(k in efns) && !isArithFn(k)) return false
  const efacts = new Set((expected.facts ?? []).map(f => JSON.stringify(f)))
  for (const f of expected.facts ?? []) {
    if (!(candidate.facts ?? []).some(cf => JSON.stringify(cf) === JSON.stringify(f))) return false
  }
  for (const cf of candidate.facts ?? []) {
    if (!efacts.has(JSON.stringify(cf)) && !isArithFn(cf.name.slice(0, cf.name.indexOf(':')))) return false
  }
  return true
}

const hasAllTargets = (provenLaws: readonly Law[], targets: readonly Law[]): boolean =>
  targets.every(t => provenLaws.some(l => JSON.stringify(l.holds) === JSON.stringify(t.holds) && !l.forall && !l.keys?.length && !l.some?.length))

// Independent kernel proof verification bound to the exact safety machine and target laws.
// Rejects missing, tampered, or mismatched proofs.
export function verifyCSafetyProof(machine: Machine, targets: readonly Law[], bundle: CSafetyProofBundle | undefined): boolean {
  if (!bundle || !targets.length) return false
  if (!sameSafetyMachine(bundle.machine, machine)) return false
  try {
    if (bundle.kind === 'usual') {
      if (!bundle.proof || !hasAllTargets(bundle.laws, targets)) return false
      return checkLaws(bundle.machine, bundle.laws, bundle.proof)
    }
    if (!bundle.kproof || !bundle.kl) return false
    const expectedGoal = conjunction([...targets]).holds
    if (JSON.stringify(bundle.kl.law.holds) !== JSON.stringify(expectedGoal)) return false
    return checkKInduction(bundle.machine, bundle.assumed, bundle.kl, bundle.kproof)
  } catch {
    return false
  }
}

function findVerifiedBundle(node: ProofOutputNode | undefined, machine: Machine, targets: readonly Law[]): CSafetyProofBundle | undefined {
  if (!node) return undefined
  if (node.kind === 'usual') {
    const bundle: CSafetyProofBundle = {kind: 'usual', machine: node.machine, laws: node.laws, proof: node.proof}
    return verifyCSafetyProof(machine, targets, bundle) ? bundle : undefined
  }
  if (node.kind === 'derived') {
    for (const parent of node.parents) {
      const found = findVerifiedBundle(parent, machine, targets)
      if (found) return found
    }
  }
  return undefined
}

type ProveOutcome =
  | {proven: true, bundle: CSafetyProofBundle}
  | {proven: false, run?: CSafetyRun, goal?: string, why?: string}

// Fast generic Houdini pass over scalar state bounds directly mentioned by the
// machine's own transitions and safety guards. Every surviving bound is verified
// from init and step by the kernel and checked jointly via verifyCSafetyProof.
function tryScalarBoundsProof(rule: Rule, machine: Machine, base: Law[], targets: Law[], budgetMs: number): CSafetyProofBundle | undefined {
  const stateKeys = Object.keys(machine.state)
  const scalars = stateKeys.filter(k => !k.startsWith('cSafetyAlarm') && !k.endsWith('$neg') && !k.endsWith('_len') && !k.endsWith('_result'))
  if (!scalars.length) return undefined
  const scalarSet = new Set(scalars)
  const boundsByVar = new Map<string, Set<number>>()
  const addBound = (v: string, k: number) => {
    if (!scalarSet.has(v) || !Number.isInteger(k) || k < 0 || k > 65536) return
    let s = boundsByVar.get(v)
    if (!s) { s = new Set(); boundsByVar.set(v, s) }
    s.add(k)
  }
  const varNameOf = (e: unknown): {v: string, shift: number} | undefined => {
    if (!e || typeof e !== 'object') return undefined
    const o = e as Partial<E>
    if (o.op === 'var' && typeof o.name === 'string' && scalarSet.has(o.name)) return {v: o.name, shift: 0}
    if (o.op === 'add') {
      const a = o.a as Partial<E> | undefined, b = o.b as Partial<E> | undefined
      if (a?.op === 'var' && typeof a.name === 'string' && scalarSet.has(a.name) && b?.op === 'const' && typeof b.value === 'number')
        return {v: a.name, shift: b.value}
      if (b?.op === 'var' && typeof b.name === 'string' && scalarSet.has(b.name) && a?.op === 'const' && typeof a.value === 'number')
        return {v: b.name, shift: a.value}
    }
    return undefined
  }
  for (const v of scalars) {
    walk(machine.step.state?.[v], o => {
      if (o.op === 'get' && typeof o.map === 'string' && /^mod\$\d+$/.test(o.map)) {
        const mod = Number(o.map.slice(4))
        if (mod >= 2 && mod <= 65536) addBound(v, mod - 1)
      }
    })
  }
  walk([machine.step.state, machine.assume], o => {
    if (o.op !== '<' && o.op !== '<=' && o.op !== '=') return
    const check = (lhs: unknown, rhs: unknown) => {
      const vr = varNameOf(lhs), r = rhs as Partial<E> | undefined
      if (!vr || r?.op !== 'const' || typeof r.value !== 'number') return
      const k = r.value - vr.shift
      if (k >= 1 && k <= 65536) addBound(vr.v, k - 1)
      if (k >= 0 && k <= 65536) addBound(vr.v, k)
    }
    check(o.a, o.b)
    check(o.b, o.a)
  })
  const run = interpret(machine), g = rule.compiled(), p = rule.encodeParams({})
  const initSt = run.init(p)
  const rawCands: Law[] = []
  for (const v of scalars) {
    const negName = `${v}$neg`
    if (negName in machine.state) {
      const holds: C = {op: '<=', a: {op: 'var', name: negName}, b: {op: 'const', value: 0}}
      if (evalC(holds, p, initSt, machine)) rawCands.push({name: `c safety bound: ${v} >= 0`, holds})
    }
    const ks = [...(boundsByVar.get(v) ?? [])].sort((a, b) => a - b).slice(0, 4)
    for (const k of ks) {
      const holds: C = {op: '<=', a: {op: 'var', name: v}, b: {op: 'const', value: k}}
      if (evalC(holds, p, initSt, machine)) rawCands.push({name: `c safety bound: ${v} <= ${k}`, holds})
    }
  }
  const existing = new Set(base.map(l => JSON.stringify(l.holds)))
  let kept = rawCands.filter(l => !existing.has(JSON.stringify(l.holds))).slice(0, 16)
  if (!kept.length) return undefined
  // Fast concrete reachability pre-filter (sound: only discards bounds falsified on
  // reachable states before calling the kernel; all survivors are still proven by checkLaws).
  const methodKey = machine.inputs[0]
  if (methodKey) {
    const zeroInp = (mIdx: number, fill = 0): Record<string, number> => {
      const inp: Record<string, number> = {}
      for (const name of machine.inputs) inp[name] = name === methodKey ? mIdx : (name.endsWith('$neg') ? 0 : fill)
      return inp
    }
    const filterAt = (st: ReturnType<typeof run.init>) => {
      kept = kept.filter(l => evalC(l.holds, p, st, machine))
    }
    for (let mIdx = 0; mIdx < 16 && kept.length; mIdx++) {
      for (const fill of [0, 1]) {
        const inp = zeroInp(mIdx, fill)
        let st = g.init(p)
        if (!allowed(machine, run, p, st, inp)) continue
        for (let step = 0; step < 32 && kept.length; step++) {
          if (!allowed(machine, run, p, st, inp)) break
          st = g.step(p, st, inp)
          filterAt(st)
        }
      }
    }
    if (kept.length) {
      let st = g.init(p)
      for (let step = 0; step < 32 && kept.length; step++) {
        let moved = false
        for (let mIdx = 0; mIdx < 16 && kept.length; mIdx++) {
          const inp = zeroInp(mIdx, step & 1)
          if (!allowed(machine, run, p, st, inp)) continue
          st = g.step(p, st, inp)
          filterAt(st)
          moved = true
        }
        if (!moved) break
      }
    }
  }
  if (!kept.length) return undefined
  const until = clock() + Math.max(500, budgetMs)
  return withDeadline(until, () => {
    // Houdini fixed point: drop any bound not inductive under the surviving set.
    for (let round = 0; round < 16 && kept.length && clock() < until; round++) {
      const all = [...base, ...kept]
      const next: Law[] = []
      let dropped = false
      for (let i = 0; i < kept.length; i++) {
        if (clock() >= until) return undefined
        const r = quietly(() => proveLaw(machine, all, base.length + i))
        if (r.proven) next.push(kept[i]!)
        else dropped = true
      }
      kept = next
      if (!dropped) break
    }
    if (!kept.length || clock() >= until) return undefined
    const laws = [...base, ...kept, ...targets]
    const out = quietly(() => proveLaws(machine, laws))
    if (out.proven && out.checked && out.proof) {
      const bundle: CSafetyProofBundle = {kind: 'usual', machine, laws, proof: out.proof}
      if (verifyCSafetyProof(machine, targets, bundle)) return bundle
    }
    return undefined
  })
}

function proveCSafetyTarget(rule: Rule, machine: Machine, base: Law[], ruleInvariants: Law[], targets: Law[], searchMs: number): ProveOutcome {
  // Fast direct check first (skip redundant cyclic cert translation; checkLaws verifies the usual proof directly).
  const full = [...base, ...targets]
  const direct = quietly(() => proveLaws(machine, full))
  if (direct.proven && direct.checked && direct.proof) {
    const bundle: CSafetyProofBundle = {kind: 'usual', machine, laws: full, proof: direct.proof}
    if (verifyCSafetyProof(machine, targets, bundle)) return {proven: true, bundle}
  }
  // Fast generic scalar-bounds Houdini before full invariant search.
  const seeded = tryScalarBoundsProof(rule, machine, base, targets, Math.min(12_000, Math.floor(searchMs / 2)))
  if (seeded) return {proven: true, bundle: seeded}
  const liveTargets = targets.filter(t => !t.name.includes('(static #'))
  const sought = liveTargets.length ? liveTargets : targets
  // Reachable-state invariant search and bounded model checking, capturing the actual kernel proof.
  let captured: PublicProofOutput | undefined
  const prevObserver = proofOutput.on
  proofOutput.on = e => { captured = e }
  let v: ReturnType<typeof proveRule>
  try {
    v = quietly(() => proveRule(rule, [...ruleInvariants, ...sought], {search: {ms: searchMs, cycles: false}}))
  } finally {
    proofOutput.on = prevObserver
  }
  if (v.proven && v.checked) {
    const found = findVerifiedBundle(captured?.proof, machine, targets)
    if (found) return {proven: true, bundle: found}
    const stateNames = new Set(Object.keys(machine.state))
    const extra = (v.found?.laws ?? []).map(f => f.law).filter(l => {
      const text = JSON.stringify(l.holds)
      return ![...text.matchAll(/"op":"var","name":"([^"]+\$sum)"/g)].some(m => !stateNames.has(m[1]!))
    })
    const reprovedLaws = [...base, ...targets, ...extra]
    const rp = quietly(() => proveLaws(machine, reprovedLaws))
    if (rp.proven && rp.checked && rp.proof) {
      const bundle: CSafetyProofBundle = {kind: 'usual', machine, laws: reprovedLaws, proof: rp.proof}
      if (verifyCSafetyProof(machine, targets, bundle)) return {proven: true, bundle}
    }
    if (v.k !== undefined) {
      const kd = quietly(() => proveKInduction(machine, base, conjunction(targets), {from: v.k, to: v.k, ms: Math.min(searchMs, 5_000)}))
      if (kd.proven && kd.checked && kd.kl && kd.proof) {
        const bundle: CSafetyProofBundle = {kind: 'kind', machine, assumed: base, kl: kd.kl, kproof: kd.proof}
        if (verifyCSafetyProof(machine, targets, bundle)) return {proven: true, bundle}
      }
    }
    return {proven: false, why: 'kernel proof failed independent checkLaws verification'}
  }
  if (v.run) return {proven: false, run: v.run, ...(v.goal ? {goal: v.goal} : {})}
  return {proven: false, why: v.why ?? v.stuck ?? 'unproven'}
}

// Fast deterministic boundary-value probe over C scalar input limits.
// Catches nonlinear faults (e.g. uint16_t * uint16_t overflow) that small-bound random
// walks or linear BMC miss; every candidate trace is still validated by ASan/UBSan replay.
function probeBoundaryFault(read: GoRead, c: CRead, rule: Rule, machine: Machine, alarmName: string | undefined): CSafetyRun | undefined {
  if (!alarmName) return undefined
  const g = rule.compiled(), run = interpret(machine), p = rule.encodeParams({}), init = g.init(p)
  const samplesOf = (ty: TT | undefined): (number | boolean)[] => {
    if (!ty) return [0]
    if (ty.k === 'bool') return [false, true]
    if (ty.k !== 'int' || !ty.bits) return [0]
    const [lo, hi] = limits({bits: ty.bits, signed: ty.signed !== false})
    return [...new Set(ty.signed !== false ? [lo, lo + 1, -1, 0, 1, hi - 1, hi] : [0, 1, Math.min(hi, 16), hi - 1, hi].filter(v => v >= lo && v <= hi))]
  }
  for (const m of read.methods) {
    const params: {key: string, vals: (number | boolean)[]}[] = []
    for (const pa of m.params) {
      const ty = c.pkg.ttab[pa.t]
      if (pa.arg.k === 'input') params.push({key: pa.arg.name, vals: samplesOf(ty)})
      else if (pa.arg.k === 'rec' && ty?.k === 'ptr') {
        const box = c.pkg.ttab[ty.elem!], val = pa.arg.fields.find(([f]) => f === 'value')?.[1]
        if (box?.box && val?.k === 'input') params.push({key: val.name, vals: samplesOf(c.pkg.ttab[box.fields![0]!.t])})
      }
    }
    let combos: Record<string, number | boolean>[] = [{}]
    for (const pr of params) {
      const next: Record<string, number | boolean>[] = []
      for (const base of combos) {
        for (const v of pr.vals) {
          next.push({...base, [pr.key]: v})
          if (next.length >= 256) break
        }
        if (next.length >= 256) break
      }
      combos = next
    }
    for (const args of combos) {
      const raw: Record<string, unknown> = {method: m.name, ...args}
      let enc: Record<string, number>
      try { enc = rule.encodeInput(raw) as Record<string, number> } catch { continue }
      if (!allowed(machine, run, p, init, enc)) continue
      const nx = rule.decode(g.step(p, g.fork(init), enc)) as Record<string, unknown>
      if (nx[alarmName] === true) return {params: {}, trace: [enc]}
    }
  }
  return undefined
}

// Replay a counterexample run on the compiled C code under ASan and UBSan.
// Never uses shell interpolation; passes JSONL request input via a temporary file.
export function replaySafety(o: {
  flags: string[], harness: string, clang?: string, strictFlex?: string[],
  methods: GoRead['methods'], choices: string[], ctor: string[], ttab: TT[],
}, run: CSafetyRun, site?: {where: string, kind: CSafetyKind}): CSafetyReplay {
  type FS = {mkdtempSync: (p: string) => string, writeFileSync: (p: string, s: string) => void, readFileSync: (p: string, e: string) => string, existsSync: (p: string) => boolean, rmSync: (p: string, o?: unknown) => void}
  type CP = {spawnSync: (c: string, a: string[], o: Record<string, unknown>) => {status: number | null, stdout: string, stderr: string}}
  type OS = {tmpdir: () => string}
  const fs = node<FS>('node:fs'), cp = node<CP>('node:child_process'), os = node<OS>('node:os')
  const work = fs.mkdtempSync(`${os.tmpdir()}/gdp-replay-`), h = `${work}/harness.c`, bin = `${work}/harness`, inFile = `${work}/in.jsonl`, outFile = `${work}/out.jsonl`
  try {
    fs.writeFileSync(h, o.harness)
    // The generated replay harness uses POSIX sigsetjmp/siglongjmp/setitimer, which strict
    // -std=c99/c11/c17/c23 hides on glibc/BSD; keep the same C standard year in GNU mode for replay.
    const replayFlags = o.flags.map(f => f.replace(/^-std=c(\d+)$/, '-std=gnu$1'))
    const b = cp.spawnSync(o.clang ?? 'clang', [
      ...replayFlags, '-w', '-O0', '-g', '-fno-omit-frame-pointer',
      '-fsanitize=address,undefined', '-fsanitize-recover=all',
      ...(o.strictFlex ?? []), h, '-o', bin,
    ], {encoding: 'utf8', timeout: 60_000, env: scrubbedClangEnv()})
    if (b.status !== 0) return {built: false, requests: [], reports: [], states: [], stderr: b.stderr.split('\n').slice(0, 12).join('\n'), matchedSite: false}
    const name = (t: Record<string, unknown>) => (typeof t.method === 'number' ? o.choices[t.method] : typeof t.method === 'string' ? t.method : o.methods[0]!.name)!
    const decodeScalar = (t: Record<string, unknown>, key: string, ty: TT | undefined): number | boolean => {
      if (ty?.k === 'bool') return Boolean(t[key])
      return Number(t[key] ?? 0) - Number(t[`${key}$neg`] ?? 0)
    }
    const requests: string[] = [], lines = [JSON.stringify({op: 'new', a: o.ctor.map(p => run.params[p] ?? 0)})]
    for (const t of run.trace) {
      const m = o.methods.find(x => x.name === name(t))
      if (!m) return {built: true, requests, reports: [], states: [], stderr: `unknown method in trace: ${name(t)}`, matchedSite: false}
      const a: unknown[] = [], shown: string[] = []
      for (const p of m.params) {
        const ty = o.ttab[p.t]
        if (p.arg.k === 'input') {
          const v = decodeScalar(t, p.arg.name, ty)
          a.push(v); shown.push(String(v))
        } else if (p.arg.k === 'rec' && ty?.k === 'ptr') {
          const box = o.ttab[ty.elem!], val = p.arg.fields.find(([f]) => f === 'value')?.[1]
          if (box?.box && val?.k === 'input') {
            const v = decodeScalar(t, val.name, o.ttab[box.fields![0]!.t])
            a.push({value: v}); shown.push(`&(${String(v)})`)
          } else {
            a.push({}); shown.push('&out')
          }
        }
      }
      requests.push(`${m.name}(${shown.join(', ')})`)
      lines.push(JSON.stringify({op: 'call', id: 1, m: m.name, a}))
    }
    fs.writeFileSync(inFile, lines.join('\n') + '\n')
    const r = cp.spawnSync(bin, [inFile, outFile], {
      encoding: 'utf8',
      timeout: 30_000,
      env: scrubbedClangEnv({ASAN_OPTIONS: 'detect_leaks=0:halt_on_error=0', UBSAN_OPTIONS: 'print_stacktrace=0:halt_on_error=0'}),
    })
    const reports = r.stderr.split('\n')
      .filter(l => /runtime error:|ERROR: AddressSanitizer|SUMMARY: AddressSanitizer|WRITE of size|READ of size/.test(l))
      .map(l => l.replace(/^.*?([^/\s]+\.c:\d+:\d+: runtime error:)/, '$1').trim())
    const states = fs.existsSync(outFile) ? fs.readFileSync(outFile, 'utf8').trim().split('\n').filter(Boolean).slice(1) : []
    const siteFileLine = site?.where.replace(/#\d+$/, '').replace(/:\d+$/, ':')
    const siteRe = siteFileLine ? new RegExp(`(?:^|[/\\s])${siteFileLine.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`) : undefined
    const matchedSite = !siteRe ? reports.length > 0 : reports.some(l => siteRe.test(l)) || siteRe.test(r.stderr)
    return {built: true, requests, reports, states, stderr: r.stderr.slice(0, 4000), matchedSite}
  } finally {
    try { fs.rmSync(work, {recursive: true, force: true}) } catch { /* gone */ }
  }
}

export function analyzeCSafety(
  read: GoRead,
  c: CRead,
  sites: readonly CSafetySite[],
  domains: Record<string, 'nat' | 'int'>,
  opts: {replay?: (run: CSafetyRun, site: CSafetySite) => CSafetyReplay, searchMs?: number} = {},
): CSafetyResult {
  const coveredFunctions = read.methods.map(m => m.name)
  const coveredHelpers = c.helpers?.length ? [...c.helpers] : undefined
  const coverage = {coveredFunctions, ...(coveredHelpers ? {coveredHelpers} : {}), ...(c.macroConfig ? {macroConfig: c.macroConfig} : {})}
  if (!sites.length) return uncheckedCSafety([], coverage)
  // A single source site can appear on several symbolic paths or events.
  const unique = new Map<string, CSafetySite>()
  for (const site of sites) {
    const key = JSON.stringify([site.where, site.kind]), prev = unique.get(key)
    unique.set(key, prev ? {...prev, condition: I.or(prev.condition, site.condition)} : site)
  }
  const all = [...unique.values()]
  const issue = ({kind, where}: CSafetySite, status: CSafetyStatus, extra?: {replay?: CSafetyReplay, why?: string}): CSafetyIssue =>
    ({where, kind, status, ...(extra?.replay ? {replay: extra.replay} : {}), ...(extra?.why ? {why: extra.why} : {})})
  const {domain, sorts} = inputDomain(read, c)
  const {model, alarmNames} = monitorCSafety(read.model, all, domain)
  const x = fromSafetyModel(model, `${c.entry}.c`, {...domains, ...sorts})
  if (!x.ok || !x.rule) return uncheckedCSafety(all.map(s => issue(s, 'unchecked')), coverage)
  const rule = x.rule, machine = rule.machine
  const laws = x.invariants ?? []
  const first = (read.model.laws ?? []).length, targets = laws.slice(first, first + all.length)
  if (targets.length !== all.length) return uncheckedCSafety(all.map(s => issue(s, 'unchecked')), coverage)
  const modelInvariants = [...laws.slice(0, first), ...laws.slice(first + all.length)]
  const base = [...rule.kindLaws(), ...modelInvariants]
  const searchMs = opts.searchMs ?? 25_000

  const jointly = proveCSafetyTarget(rule, machine, base, modelInvariants, targets, searchMs)
  if (jointly.proven) {
    const issues = all.map(site => issue(site, 'proven'))
    const result: CSafetyResult = {status: 'proven', issues, assumptions, ...coverage}
    safetyArtifacts.set(result, {rule, machine, source: x.source ?? '', baseLaws: base, targetLaws: targets, jointProof: jointly.bundle, siteProofs: targets.map(() => jointly.bundle)})
    return result
  }

  const siteProofs: (CSafetyProofBundle | undefined)[] = []
  const issues: CSafetyIssue[] = all.map((site, j) => {
    const target = targets[j]!
    const reused = !jointly.proven && jointly.run && jointly.goal?.startsWith(target.name)
      ? jointly
      : all.length === 1 ? jointly : proveCSafetyTarget(rule, machine, base, modelInvariants, [target], searchMs)
    if (reused.proven) {
      siteProofs.push(reused.bundle)
      return issue(site, 'proven')
    }
    siteProofs.push(undefined)
    const run = reused.run ?? probeBoundaryFault(read, c, rule, machine, alarmNames[j])
    if (run && opts.replay) {
      const rp = opts.replay(run, site)
      if (rp.built && rp.reports.length > 0 && rp.matchedSite) return issue(site, 'broken', {replay: rp})
      return issue(site, 'unproven', {
        replay: rp,
        why: !rp.built
          ? 'failed to build ASan/UBSan replay harness'
          : rp.reports.length > 0
            ? `ASan/UBSan fired, but did not match target site ${site.where}`
            : 'counterexample run did not trigger ASan/UBSan on compiled C',
      })
    }
    return issue(site, 'unproven', {why: reused.why})
  })
  const status: CSafetyStatus = issues.some(s => s.status === 'broken') ? 'broken' : issues.every(s => s.status === 'proven') ? 'proven' : 'unproven'
  // If every site proved individually, assemble a single unified jointProof when possible.
  let jointProof: CSafetyProofBundle | undefined
  if (status === 'proven') {
    const seen = new Set<string>(base.map(l => JSON.stringify(l.holds)))
    const combined: Law[] = [...base]
    for (const sp of siteProofs) {
      if (sp?.kind !== 'usual') continue
      for (const l of sp.laws) {
        const key = JSON.stringify(l.holds)
        if (!seen.has(key)) { seen.add(key); combined.push(l) }
      }
    }
    for (const t of targets) {
      const key = JSON.stringify(t.holds)
      if (!seen.has(key)) { seen.add(key); combined.push(t) }
    }
    const jp = quietly(() => proveLaws(machine, combined))
    if (jp.proven && jp.checked && jp.proof) {
      const bundle: CSafetyProofBundle = {kind: 'usual', machine, laws: combined, proof: jp.proof}
      if (verifyCSafetyProof(machine, targets, bundle)) jointProof = bundle
    }
  }
  const result: CSafetyResult = {status, issues, assumptions, ...coverage}
  safetyArtifacts.set(result, {rule, machine, source: x.source ?? '', baseLaws: base, targetLaws: targets, ...(jointProof ? {jointProof} : {}), siteProofs})
  return result
}

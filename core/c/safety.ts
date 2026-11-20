// Static-only C safety. The checked C reader validates source coverage; the
// safety backend supplies conditions on defined prefixes, not ordinary refusals.
import {proveLaws} from '../../kernel/prove.ts'
import {noEvidence} from '../extract-check.ts'
import * as I from '../extract-ir.ts'
import {Refusal, type Model, type Term, type Var} from '../extract-read.ts'
import {iteTerm, varTerm} from '../extract-step.ts'
import {fromModel} from '../extract.ts'
import type {GoRead} from '../extract-go.ts'
import type {CRead} from './reader.ts'

export type CSafetyKind = 'bounds' | 'overflow' | 'division'
export type CSafetySite = {where: string, kind: CSafetyKind, condition: I.B}
export type CSafetyStatus = 'proven' | 'unproven' | 'unchecked'
export type CSafetyIssue = {where: string, kind: CSafetyKind, status: CSafetyStatus}
export type CSafetyResult = {status: CSafetyStatus, issues: CSafetyIssue[], assumptions: readonly string[]}

const assumptions = [
  'The Clang target uses 8-bit bytes and two’s-complement integers; only covered scalar types up to 32 bits and arrays of known extent are modeled.',
  'Selected methods run sequentially on one live, zero-initialized receiver, or on modeled globals from their C initialization; no other code changes this state.',
  'Inputs are in their C types. Configured normal refusals end the admitted trace unless a tracked fault has already occurred.',
  'Only the first tracked array-bounds, signed-overflow or division/remainder fault is checked. This is not a proof of general C memory safety.',
] as const
export const uncheckedCSafety = (issues: CSafetyIssue[] = []): CSafetyResult => ({status: 'unchecked', issues, assumptions})

const limits = ({bits, signed}: {bits: number, signed: boolean}): [number, number] => signed ? [-(2 ** (bits - 1)), 2 ** (bits - 1) - 1] : [0, 2 ** bits - 1]

// Bind the alarm conditions to the real C input domain independently of the
// backend's accumulated refusals. A hit must never override a type restriction.
function inputDomain(read: GoRead, c: CRead): {domain: I.B, sorts: Record<string, 'nat' | 'int'>} {
  const m = read.model, event = m.inputs.find(v => v.name === m.event)
  const sorts: Record<string, 'nat' | 'int'> = {}
  if (!event || event.sort.k !== 'choice') throw new Refusal(m.file, 'C safety needs explicit event selectors')
  const selector: I.L = {op: 'var', name: event.name, values: event.sort.values}
  const seen = new Set([event.name])
  const domain = I.and(...read.methods.map(method => {
    const sel = I.is(selector, method.name)
    return I.or(I.not(sel), I.and(...method.params.map(({arg, t}) => {
      const ty = c.pkg.ttab[t]
      if (arg.k !== 'input' || !ty) throw new Refusal(m.file, 'C safety needs scalar inputs with a covered C type')
      seen.add(arg.name)
      if (ty.k === 'bool') return I.T
      if (ty.k !== 'int' || !Number.isInteger(ty.bits) || ty.bits! < 1 || ty.bits! > 32 || typeof ty.signed !== 'boolean') throw new Refusal(m.file, 'C safety needs supported fixed-width integer inputs')
      sorts[arg.name] = ty.signed ? 'int' : 'nat'
      const [lo, hi] = limits({bits: ty.bits!, signed: ty.signed}), e = I.nvar(arg.name)
      return I.and(I.cmp('<=', I.num(lo), e), I.cmp('<=', e, I.num(hi)))
    })))
  }))
  if (m.inputs.some(v => !seen.has(v.name)) || m.params.length) throw new Refusal(m.file, 'C safety does not admit inferred inputs or constructor parameters')
  return {domain, sorts}
}

export function monitorCSafety(m: Model, sites: readonly CSafetySite[], domain: I.B): {model: Model, alarmLaws: string[]} {
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
  const alarms = sites.map((): Var => {
    let name: string
    do { name = `cSafetyAlarm${++nextId}` } while (reserved.has(name))
    reserved.add(name)
    return {name, sort: {k: 'bool'}, role: 'state'}
  })
  const already = I.or(...alarms.map(a => I.bvar(a.name)))
  // Do not infer an order from the site list: each condition is already
  // guarded by the backend's source-specific defined prefix.
  const hits = sites.map(s => I.and(I.not(already), domain, s.condition))
  const stutter = I.or(already, ...hits)
  const init = {...m.init}, writes: Record<string, Term> = {...m.writes}
  for (const v of m.state) if (writes[v.name]) writes[v.name] = iteTerm(stutter, varTerm(v), writes[v.name]!)
  const listWrites = Object.fromEntries(Object.entries(m.listWrites ?? {}).map(([n, ops]) => [n, ops.map(o => ({...o, when: I.and(I.not(stutter), o.when)}))]))
  const alarmLaws = alarms.map(({name}, j) => {
    init[name] = {s: 'bool', e: I.F}
    writes[name] = {s: 'bool', e: I.or(I.bvar(name), hits[j]!)}
    return `r.law(${JSON.stringify(`no first C ${sites[j]!.kind} fault (${name})`)}, ({${name}}) => ${name}.not())`
  })
  return {model: {...m, state: [...m.state, ...alarms], init, writes, listWrites,
    refuse: I.or(I.not(domain), I.and(I.not(stutter), m.refuse)), laws: [...(m.laws ?? []), ...alarmLaws]}, alarmLaws}
}

export function analyzeCSafety(read: GoRead, c: CRead, sites: readonly CSafetySite[], domains: Record<string, 'nat' | 'int'>): CSafetyResult {
  if (!sites.length) return uncheckedCSafety()
  // A single source site can appear on several symbolic paths or events.
  const unique = new Map<string, CSafetySite>()
  for (const site of sites) {
    const key = JSON.stringify([site.where, site.kind]), prev = unique.get(key)
    unique.set(key, prev ? {...prev, condition: I.or(prev.condition, site.condition)} : site)
  }
  const all = [...unique.values()]
  const issue = ({kind, where}: CSafetySite, status: CSafetyStatus): CSafetyIssue => ({where, kind, status})
  // Model construction only: no source check or replay callback. Do not return
  // the proof report (it can contain solver models), or the executable rule.
  const {domain, sorts} = inputDomain(read, c)
  const {model} = monitorCSafety(read.model, all, domain)
  const x = fromModel(model, `${c.entry}.c`, {...domains, ...sorts}, [], noEvidence)
  if (!x.ok || !x.rule) return uncheckedCSafety(all.map(s => issue(s, 'unchecked')))
  const laws = x.invariants ?? [], base = [...x.rule.kindLaws(), ...laws.slice(0, (read.model.laws ?? []).length)]
  // fromModel appends the fixed-list representation laws after model laws.
  const first = (read.model.laws ?? []).length, targets = laws.slice(first, first + all.length)
  if (targets.length !== all.length) return uncheckedCSafety(all.map(s => issue(s, 'unchecked')))
  base.push(...laws.slice(first + all.length))
  const prove = (ls: typeof laws): boolean => { const r = proveLaws(x.rule!.machine, [...base, ...ls]); return r.proven && r.checked }
  const jointly = prove(targets)
  const issues = all.map((site, j) => issue(site, jointly || all.length > 1 && prove([targets[j]!]) ? 'proven' : 'unproven'))
  return {status: issues.every(s => s.status === 'proven') ? 'proven' : 'unproven', issues, assumptions}
}

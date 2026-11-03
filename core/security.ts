// Untrusted security policy templates. These bind policy to source names; they do not infer intent,
// add assumptions, or confer trust on a caller-supplied role/tenant. buildLaw and the normal CLI proof
// and source-replay path check them. A generated candidate is NOT an accepted security policy.
import type {Extraction, Name} from './extract.ts'
import type {LawText} from './laws.ts'

export type SecurityKind = 'authorization' | 'isolation' | 'workflow' | 'quota' | 'ledger'
export type SecuritySpec = {name: string, method?: string} & (
  | {kind: 'authorization', effect: string, requires: string}
  | {kind: 'workflow', effect: string, prerequisite: string}
  | {kind: 'quota', used: string, limit: string}
  | {kind: 'ledger', balance: string}
  | {kind: 'isolation', map: string, identity: string, fields: string[], key?: string}
  | {kind: 'isolation', identity: string, seeing: string}
)
export type SecurityCandidate = LawText & {securityKind: SecurityKind, review: 'required'}

// Isolation covers BOTH domains. Quantifying only post-state keys misses deletions; only pre-state
// keys misses insertions. Presence is checked too, including deleting a foreign zero-valued row.
export function securityLaws(spec: SecuritySpec): SecurityCandidate[] {
  const make = (expr: string, suffix = ''): SecurityCandidate => ({name: spec.name + suffix, expr,
    ...(spec.method ? {method: spec.method} : {}), securityKind: spec.kind, review: 'required'})
  switch (spec.kind) {
    case 'authorization': return [make(`(${spec.effect}) implies (${spec.requires})`)]
    case 'workflow': return [make(`(${spec.effect}) implies old(${spec.prerequisite})`)]
    case 'quota': return [make(`(${spec.used}) <= (${spec.limit})`)]
    case 'ledger': return [make(`(${spec.balance}) >= 0`)]
    case 'isolation': {
      if ('seeing' in spec) return [make(`isolated by ${spec.identity} seeing ${spec.seeing}`)]
      const k = spec.key ?? 'securityKey', m = spec.map
      if (!/^[A-Za-z_]\w*$/.test(k) || [spec.identity, m, ...spec.fields].some(s => (s.match(/[A-Za-z_$][\w$]*/g) ?? []).some(n => n === k)))
        throw new Error('isolation key must be a fresh identifier, not a name in the policy')
      const same = [`${k} in ${m}`, `${k} in old(${m})`, ...spec.fields.map(f => {
        const cell = `${m}[${k}]${f ? `.${f}` : ''}`
        return `${cell} == old(${cell})`
      })].map(s => `(${s})`).join(' and ')
      const body = `${k} != (${spec.identity}) implies (${same})`
      return [make(`forall ${k} in ${m}: ${body}`, ' (new rows)'), make(`forall ${k} in old(${m}): ${body}`, ' (old rows)')]
    }
  }
}

// Bounded, deterministic proposals using only extracted structure and names. Bool inputs and each
// role-choice value are ALTERNATIVE requirements, not inferred policy. No candidate is assumed while
// checking another. A caller must select the intended law and bind identity to authentication.
export function securityTemplates(x: Extraction, max = 48): SecurityCandidate[] {
  if (!x.ok || !x.model || !x.rule) return []
  const m = x.model, names = x.names ?? [], out: SecurityCandidate[] = []
  const name = (rule: string, role?: Name['role']) => names.find(n => n.rule === rule && (!role || n.role === role))
  const states = m.state.filter(v => !m.outputs.includes(v.name)).flatMap(v => {
    const n = name(v.name, 'state'); return n && !n.map && !n.none ? [{v, n}] : []
  })
  const inputs = m.inputs.filter(v => v.name !== m.event).flatMap(v => {
    const n = name(v.name, 'input'); return n && !n.none ? [{v, n}] : []
  })
  const add = (s: SecuritySpec) => {
    const laws = securityLaws(s).filter(l => !out.some(o => o.expr === l.expr && o.method === l.method))
    if (out.length + laws.length <= max) out.push(...laws) // never truncate an isolation pair
  }
  for (const {v, n} of states) {
    if (v.sort.k !== 'num') continue
    add({kind: 'ledger', name: `${n.code} never negative`, balance: n.code})
    for (const p of m.params.filter(p => p.sort.k === 'num')) {
      const cap = name(p.name, 'param')
      if (cap) add({kind: 'quota', name: `${n.code} within ${cap.code}`, used: n.code, limit: cap.code})
    }
  }
  for (const {v, n} of inputs) {
    // Arbitrary bool requests, and every value of a role/permission choice: no privileged value guessed.
    const requirements = v.sort.k === 'bool' ? [n.code] : v.sort.k === 'choice' ? v.sort.values.map(c => `${n.code} == ${JSON.stringify(c)}`) : []
    const effects = states.map(s => ({expr: `${s.n.code} != old(${s.n.code})`, label: `changing ${s.n.code}`}))
    for (const result of names.filter(r => r.role === 'result' && r.method === n.method && !r.none)) {
      if (m.state.find(s => s.name === result.rule)?.sort.k === 'bool') effects.push({expr: result.code, label: `${n.method} succeeds`})
    }
    for (const req of requirements) for (const effect of effects) add({kind: 'authorization', name: `${effect.label} requires ${req}`, method: n.method, effect: effect.expr, requires: req})
  }
  for (const before of states.filter(s => s.v.sort.k === 'bool')) for (const after of states.filter(s => s.v.name !== before.v.name)) {
    add({kind: 'workflow', name: `changing ${after.n.code} only after ${before.n.code}`, effect: `${after.n.code} != old(${after.n.code})`, prerequisite: before.n.code})
  }
  let key = 'securityKey'
  while (names.some(n => n.code === key || n.rule === key)) key += '_'
  for (const map of m.maps.filter(d => !d.carried && !d.ordered)) {
    const n = name(map.name, 'state')
    if (!n?.map || n.none) continue
    for (const input of inputs.filter(i => i.v.sort.k === (map.key === 'str' ? 'str' : 'num'))) {
      if (names.some(n => n.role === 'result' && n.method === input.n.method))
        add({kind: 'isolation', name: `reads isolated by ${input.n.code}`, identity: input.n.code, seeing: 'result', method: input.n.method})
      add({kind: 'isolation', name: `${n.code} isolated by ${input.n.code}`, map: n.code, identity: input.n.code, method: input.n.method,
        fields: map.fields.filter(f => f.name !== 'has').map(f => f.name), key})
    }
  }
  return out
}

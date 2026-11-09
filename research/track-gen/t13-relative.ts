// T-13.2. Exhaustive bounded relative induction, NOT an unbounded proof.
// P*'s hand family plus, separately, the two generated stronger alternatives.
const n = 3, T = 2, V = 2, servers = [0, 1, 2], masks = Array.from({length: 1 << n}, (_, i) => i)
const pop = (v: number): number => v ? 1 + pop(v & (v - 1)) : 0
const has = (v: number, i: number) => !!(v & (1 << i))
const qs = masks.map(x => masks.filter(q => !(q & ~x) && 2 * pop(q) > pop(x)))
const overlap = masks.map(x => masks.map(y => qs[x]!.every(a => qs[y]!.every(b => !!(a & b)))))
for (const x of masks) for (const y of masks) {
  const half = Math.max(0, Math.floor(pop(x) / 2) + 1 - pop(x & ~y)) + Math.max(0, Math.floor(pop(y) / 2) + 1 - pop(y & ~x)) > pop(x & y)
  if (half !== overlap[x]![y]) throw Error('half encoding mismatch')
}
type S = {ct: number[], st: number[], cv: number[], cft: number[], cfg: number[], started: number}
const clone = (s: S): S => ({...s, ct: [...s.ct], st: [...s.st], cv: [...s.cv], cft: [...s.cft], cfg: [...s.cfg]})
const newer = (s: S, a: number, b: number) => s.cft[a]! > s.cft[b]! || (s.cft[a] === s.cft[b] && s.cv[a]! > s.cv[b]!)
const disabled = (s: S, a: number) => 2 * servers.filter(k => has(s.cfg[a]!, k) && !newer(s, k, a)).length <= pop(s.cfg[a]!)
const low = (s: S, a: number, b: number) => servers.filter(k => has(s.cfg[a]!, k) && s.ct[k]! < s.cft[b]!).length
const bq = (s: S, a: number, b: number) => servers.filter(k => has(s.cfg[a]!, k) && s.ct[k]! < s.cft[b]! && !newer(s, k, a)).length
const base = (s: S) => servers.every(a => (s.cv[a] !== 0 || s.cfg[a] === 0) && (s.started || (s.cft[a] === 0 && s.st[a] === 0 && s.ct[a] === 0)) && (!s.st[a] || s.cft[a] === s.ct[a]) && servers.every(b =>
  (!(s.st[a] && s.st[b] && s.ct[a] === s.ct[b]) || a === b) &&
  (!(s.st[a] && s.cft[a] === s.cft[b]) || !newer(s, b, a)) &&
  (s.cft[a] !== s.cft[b] || s.cv[a] !== s.cv[b] || s.cfg[a] === s.cfg[b]) &&
  (overlap[s.cfg[a]!]![s.cfg[b]!] || disabled(s, a) || disabled(s, b)) &&
  2 * bq(s, a, b) <= pop(s.cfg[a]!)))
const alternatives = {
  low: (s: S) => servers.every(a => servers.every(b => 2 * low(s, a, b) <= pop(s.cfg[a]!))),
  overlap: (s: S) => servers.every(a => servers.every(b => overlap[s.cfg[a]!]![s.cfg[b]!])),
}
function* actions(s: S): Generator<[string, S]> {
  if (!s.started) {
    if (s.cv.every(v => v === 0)) for (const cfg of masks.filter(Boolean)) { const t = clone(s); t.cfg[0] = cfg; t.cv[0] = 1; yield [`pick(${cfg})`, t] }
    if (s.cv[0] === 1) for (const i of servers) if (!s.cv[i]) { const t = clone(s); t.cfg[i] = s.cfg[0]!; t.cv[i] = 1; yield [`copy(${i})`, t] }
    if (s.cv.every(v => v === 1)) yield ['start', {...clone(s), started: 1}]
    return
  }
  for (const i of servers) for (const j of servers) if (s.ct[i]! > s.ct[j]!) { const t = clone(s); t.ct[j] = s.ct[i]!; t.st[j] = 0; yield [`update(${i},${j})`, t] }
  for (const i of servers) if (has(s.cfg[i]!, i)) for (const q of qs[s.cfg[i]!]!) {
    if (!has(q, i) || !servers.every(k => !has(q, k) || (s.ct[k]! < s.ct[i]! + 1 && !newer(s, k, i)))) continue
    const t = clone(s)
    for (const k of servers) if (has(q, k)) { t.ct[k] = s.ct[i]! + 1; t.st[k] = k === i ? 1 : 0 }
    t.cft[i] = s.ct[i]! + 1; yield [`lead(${i},${q})`, t]
  }
  for (const i of servers) if (s.st[i] && s.cft[i] === s.ct[i] && qs[s.cfg[i]!]!.some(q => servers.every(k => !has(q, k) || (s.cv[k] === s.cv[i] && s.cft[k] === s.cft[i] && s.ct[k] === s.ct[i])))) {
    for (const cfg of masks) if (has(cfg, i) && overlap[s.cfg[i]!]![cfg]) { const t = clone(s); t.cfg[i] = cfg; t.cv[i] = s.cv[i]! + 1; yield [`reconfig(${i},${cfg})`, t] }
  }
  for (const i of servers) for (const j of servers) if (!s.st[j] && newer(s, i, j)) { const t = clone(s); t.cv[j] = s.cv[i]!; t.cft[j] = s.cft[i]!; t.cfg[j] = s.cfg[i]!; yield [`send(${i},${j})`, t] }
}
const t0 = performance.now(), results = Object.fromEntries(Object.keys(alternatives).map(k => [k, {states: 0, steps: 0, ctis: 0, first: undefined as unknown}]))
let states = 0, inBase = 0, baseCtis = 0
const s: S = {ct: [0, 0, 0], st: [0, 0, 0], cv: [0, 0, 0], cft: [0, 0, 0], cfg: [0, 0, 0], started: 0}
function enumerate(k: number): void {
  if (k < n) {
    for (let ct = 0; ct <= T; ct++) for (let st = 0; st <= 1; st++) for (let cv = 0; cv <= V; cv++) for (let cft = 0; cft <= T; cft++) for (const cfg of masks) {
      if ((!s.started && (ct || st || cft)) || (st && ct !== cft) || (!cv && cfg)) continue
      s.ct[k] = ct; s.st[k] = st; s.cv[k] = cv; s.cft[k] = cft; s.cfg[k] = cfg
      // Prune only completed unary/pair clauses of the base family. Counted
      // clauses depend on all servers and are checked only at a complete state.
      if (servers.slice(0, k).some(a => (st && s.st[a] && ct === s.ct[a]) || (cft === s.cft[a] && cv === s.cv[a] && cfg !== s.cfg[a]) || (st && cft === s.cft[a] && newer(s, a, k)) || (s.st[a] && s.cft[a] === cft && newer(s, k, a)))) continue
      enumerate(k + 1)
    }
    return
  }
  states++
  if (!base(s)) return
  inBase++
  const active = Object.entries(alternatives).filter(([, f]) => f(s))
  for (const [name] of active) results[name]!.states++
  for (const [action, post] of actions(s)) {
    if (!base(post)) baseCtis++
    for (const [name, holds] of active) {
      const r = results[name]!; r.steps++
      if (holds(post)) continue
      r.ctis++
      r.first ??= {action, pre: clone(s), post}
    }
  }
}
for (s.started = 0; s.started <= 1; s.started++) enumerate(0)
console.log(JSON.stringify({n, T, V, scope: 'all P* pre-states in bounds satisfying the hand family; all enabled transitions, including post-states beyond T/V', statesAfterSoundPruning: states, inBase, baseCtis, results, ms: performance.now() - t0}))
if (baseCtis) throw Error('hand family is not relatively inductive on bounded check')

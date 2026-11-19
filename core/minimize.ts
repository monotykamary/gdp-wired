// Minimal refuting runs. Untrusted, like every search: the answer is a run anyone replays through the rule.
//
// `minimizeRun(rule, law, run, opts?)` takes a run that breaks `law` (the requests of a witness: a verdict's `run`, or
// its trace alone) and returns a run that still breaks it on the ORIGINAL rule and is 1-minimal: with any one request
// removed it no longer breaks the law.
//
// What "breaks" means here (the reading core/watch.ts and core/bmc.ts's `replay` give a run): from the rule's start
// state at the run's params, the requests are taken in order by the interpreter, and the law is read at the start and
// after every step (a step law: at every `steps` steps in a row), at the keys core/watch.ts reads a law at. A request
// the rule refuses (its assumption, a request out of order, a fixed-width failure) is not taken. The run returned
// holds only requests the rule takes, and its LAST step is the first that breaks the law, so it breaks the law both
// for a replay that stops at a refused request and for one that skips it; and no run with one request removed breaks
// it under either reading (a removal is tried with the refused requests skipped, the wider of the two).
//
// How: (1) the run is cut at its first breaking step, refused requests dropped; (2) chunks are removed, halving
// (delta debugging), then single requests until a whole pass removes none: that pass is the 1-minimality argument,
// each removal replayed and seen not to break the law; (3) while time is left, pairs of requests, and (for a law or a
// one-step law) a breadth-first search for a shortest breaking subsequence of the run, which is 1-minimal by being
// shortest. Every candidate adopted was replayed to its breaking step, so the result is valid whenever it returns.
// A removal replays only from the cut (the states before it are kept), and stops as soon as its state meets the
// state the kept run had there (then the rest goes as before): a request that changes nothing costs one step.
//
// The budget (`ms`, wall time, 2000 by default) stops the work where it is: the run returned still breaks the law,
// and `minimal` (minimizeRunDetailed) says whether the closing pass finished.
import {type Law, type Machine, type Request, type State, interpret, evalC} from './machine.ts'
import {allowed, isStepLaw, watch, type Watched} from './watch.ts'

type Env = Record<string, number>
// A request as a trace shows it (each map an object of its cells), as the runtimes take it (a Map), or as the rule's
// own values (`rule.encodeInput` reads those).
export type RunRequest = Record<string, unknown>
export type RunTrace = {params: Record<string, number>, trace: readonly RunRequest[]}
export type MinimizeOptions = {
  ms?: number // the wall-time budget (2000)
  params?: Record<string, number> // the params of a run given as its requests alone
  bound?: number // the keys a law about every key is read at (core/watch.ts's keysOf): by default the least of 1, 3, 8, 24 the run breaks at
  shortest?: boolean // also search for a shortest breaking subsequence (true)
}
export type Minimized<R> = {run: R, minimal: boolean, from: number, to: number, replays: number, steps: number, ms: number}
type RuleLike = {machine: Machine, encodeInput?: (input: never) => Request} | Machine

const now = () => performance.now()
const isPlain = (x: unknown): x is Record<string, unknown> => typeof x === 'object' && x !== null && !(x instanceof Map) && !Array.isArray(x)
const decoded = (rule: RuleLike, shown: RunRequest): Request => {
  const vals = Object.values(shown)
  const wire = vals.every(x => typeof x === 'number' || x instanceof Map || isPlain(x) && Object.values(x).every(y => typeof y === 'number'))
  if (!wire) {
    const enc = (rule as {encodeInput?: (input: never) => Request}).encodeInput
    if (typeof enc !== 'function') throw new Error('minimizeRun: a request holds a value that is neither a number nor a map of numbers')
    return enc.call(rule, shown as never)
  }
  return Object.fromEntries(Object.entries(shown).map(([n, x]) => [n, typeof x === 'number' || x instanceof Map ? x : new Map(Object.entries(x as Record<string, number>).map(([k, v]) => [Number(k), v]))])) as Request
}
const sameCells = (a: ReadonlyMap<number, number>, b: ReadonlyMap<number, number>) => { if (a.size !== b.size) return false; for (const [k, v] of a) if (b.get(k) !== v) return false; return true }
const sameRecord = (a: Record<string, number> | undefined, b: Record<string, number> | undefined) => {
  if (a === b) return true
  const ka = Object.keys(a ?? {}), kb = Object.keys(b ?? {})
  return ka.length === kb.length && ka.every(k => a![k] === b?.[k])
}
const sameState = (a: State, b: State): boolean => {
  if (a === b) return true
  if (!sameRecord(a.scalars, b.scalars) || !sameRecord(a.defaults, b.defaults) || a.last !== b.last) return false
  const ma = Object.keys(a.maps)
  if (ma.length !== Object.keys(b.maps).length) return false
  for (const n of ma) { const y = b.maps[n]; if (!y || !sameCells(a.maps[n]!, y)) return false }
  const ha = a.history, hb = b.history
  if (!ha !== !hb) return false
  if (ha && hb) { if (ha.length !== hb.length) return false; for (let i = 0; i < ha.length; i++) if (ha[i] !== hb[i] && !sameRecord(ha[i], hb[i])) return false }
  return true
}
const recKey = (r: Record<string, number> | undefined) => (r ? Object.keys(r).sort().map(k => `${k}:${r[k]}`).join(',') : '')
const cellsKey = (c: ReadonlyMap<number, number>) => [...c].sort((x, y) => x[0] - y[0]).map(([k, v]) => `${k}:${v}`).join(',')
const stateKey = (st: State): string => `${recKey(st.scalars)}|${Object.keys(st.maps).sort().map(n => `${n}{${cellsKey(st.maps[n]!)}}`).join('')}|${recKey(st.defaults)}|${st.last ?? ''}|${st.history ? st.history.map(recKey).join(';') : ''}`
const requestKey = (r: Request): string => Object.keys(r).sort().map(n => { const x = r[n]!; return `${n}=${typeof x === 'number' ? x : `{${cellsKey(x)}}`}` }).join('&')

class OutOfTime extends Error {}

export function minimizeRunDetailed<R extends RunTrace | readonly RunRequest[]>(rule: RuleLike, law: Watched, run: R, opts: MinimizeOptions = {}): Minimized<R> {
  const t0 = now(), deadline = t0 + Math.max(0, opts.ms ?? 2000)
  const m: Machine = 'machine' in rule && typeof (rule as {machine?: unknown}).machine === 'object' ? (rule as {machine: Machine}).machine : rule as Machine
  const isArray = Array.isArray(run)
  const params: Env = {...(isArray ? opts.params ?? {} : (run as RunTrace).params)}
  const given: readonly RunRequest[] = isArray ? run as readonly RunRequest[] : (run as RunTrace).trace
  const it = interpret(m), k = isStepLaw(law) ? law.steps ?? 1 : 0
  const wrap = (shown: RunRequest[]): R => (isArray ? shown : {...(run as RunTrace), params: (run as RunTrace).params, trace: shown}) as unknown as R
  if (m.pre && !evalC(m.pre, params, {scalars: {}, maps: {}}, m)) throw new Error(`minimizeRun: the params fail ${m.name}'s precondition, so the run is not one of the rule's`)
  const all = given.map(s => decoded(rule, s))
  let replays = 0, steps = 0, bound = opts.bound ?? 1
  const timed = () => { if (now() > deadline) throw new OutOfTime() }
  // One step, or undefined where the rule refuses the request.
  const take = (st: State, input: Request): State | undefined => {
    steps++
    try { return allowed(m, it, params, st, input) ? it.step(params, st, input) : undefined } catch (e) { if (e instanceof RangeError) return undefined; throw e }
  }
  // A fresh reading of the law along one run: `start` and `step` say whether it is broken there.
  const reader = () => {
    const on = watch(m, it, law, params, bound)
    return {start: (st: State) => !on.start(st), step: (before: State, input: Request, after: State) => !on.step(before, input, after)}
  }
  // The kept run: the requests taken (`idx`: their places in the given run), the state before each and after the last.
  // Its last step is the first that breaks the law.
  type Kept = {idx: number[], states: State[]}
  // The given run, refused requests skipped, cut at its first breaking step (undefined: it never breaks the law).
  const normal = (): Kept | undefined => {
    replays++
    const on = reader(), idx: number[] = []
    let st = it.init(params)
    const states = [st]
    if (on.start(st)) return {idx, states}
    for (let q = 0; q < all.length; q++) {
      const next = take(st, all[q]!)
      if (!next) continue
      idx.push(q); states.push(next)
      if (on.step(st, all[q]!, next)) return {idx, states}
      st = next
    }
    return undefined
  }
  let cur: Kept | undefined
  if (opts.bound !== undefined) cur = normal()
  else for (const b of [1, 3, 8, 24]) { bound = b; if ((cur = normal())) break }
  if (!cur) throw new Error(`minimizeRun: the run does not break ${JSON.stringify(law.name)} on ${m.name} (replayed from the start${isArray && !opts.params ? ', with no params given' : ''})`)
  const from = cur.idx.length
  const done = (kept: Kept, minimal: boolean): Minimized<R> => ({run: wrap(kept.idx.map(q => given[q]!)), minimal, from: given.length, to: kept.idx.length, replays, steps, ms: now() - t0})
  // The kept run with the places `drop` (sorted, of the kept run) removed, if it still breaks the law: replayed from
  // the first place dropped, refused requests skipped, cut at the first breaking step.
  const without = (kept: Kept, drop: number[]): Kept | undefined => {
    replays++
    const n = kept.idx.length, first = drop[0]!, last = drop[drop.length - 1]!
    // (a k-step law reads k steps in a row: the k-1 steps before the cut are read again, into a fresh window)
    const s = k > 1 ? Math.max(0, first - (k - 1)) : first
    const on = reader()
    let st = kept.states[s]!, d = 0
    const idx = kept.idx.slice(0, s), states = kept.states.slice(0, s + 1)
    for (let p = s; p < n; p++) {
      if ((p & 63) === 0) timed()
      if (d < drop.length && drop[d] === p) { d++; continue }
      const input = all[kept.idx[p]!]!, next = take(st, input)
      if (next) {
        idx.push(kept.idx[p]!); states.push(next)
        if (on.step(st, input, next)) return {idx, states}
        st = next
      }
      // The state the kept run had here: from here on the two runs are one, and the kept run's last step breaks the law.
      if (k <= 1 && p >= last && p + 1 < n && sameState(st, kept.states[p + 1]!)) {
        for (let q = p + 1; q < n; q++) { idx.push(kept.idx[q]!); states.push(kept.states[q + 1]!) }
        return {idx, states}
      }
    }
    return undefined
  }
  const range = (i: number, j: number) => Array.from({length: j - i}, (_, x) => i + x)
  let minimal = false
  try {
    // Chunks, halving; then single requests until a whole pass removes none.
    for (let c = Math.ceil(cur.idx.length / 2); c > 1; c = Math.ceil(c / 2)) {
      for (let i = 0; i < cur.idx.length;) {
        timed()
        const less = without(cur, range(i, Math.min(i + c, cur.idx.length)))
        if (less) cur = less; else i += c
      }
    }
    const singles = () => {
      for (let changed = true; changed;) {
        changed = false
        // (from the end: a later request's removal replays less)
        for (let i = cur!.idx.length - 1; i >= 0; i--) {
          timed()
          const less = without(cur!, [i])
          if (less) { cur = less; changed = true; i = Math.min(i, cur.idx.length) }
        }
      }
    }
    singles()
    minimal = true
    // Shorter still, while time is left. Each result here is 1-minimal again before it replaces the kept run.
    let best = cur
    try {
      // Pairs of requests (a request and the one that undoes it), then single requests again.
      for (let again = true; again && cur.idx.length <= 64;) {
        again = false
        search: for (let i = 0; i < cur.idx.length; i++) for (let j = i + 1; j < cur.idx.length; j++) {
          timed()
          const less = without(cur, [i, j])
          if (less) { cur = less; singles(); best = cur; again = true; break search }
        }
      }
    } catch (e) { if (!(e instanceof OutOfTime)) throw e; return done(best, true) }
    // A shortest breaking subsequence of the given run (breadth first: a state reached at an earlier place of the run
    // stands for the same state reached later, since every request after the later place is after the earlier one too).
    if (opts.shortest !== false && k <= 1 && cur.idx.length > 1) {
      const shorter = shortest(cur.idx.length)
      if (shorter) cur = shorter
    }
  } catch (e) { if (!(e instanceof OutOfTime)) throw e }
  return done(cur, minimal)

  function shortest(below: number): Kept | undefined {
    // The requests by what they are: from a place, each distinct request is tried at its first place after it.
    const classes = new Map<string, number[]>()
    const pool = from <= 4096 ? range(0, all.length) : cur!.idx
    for (const q of pool) { const key = requestKey(all[q]!); const at = classes.get(key); if (at) at.push(q); else classes.set(key, [q]) }
    if (classes.size > 256) return undefined
    const places = [...classes.values()]
    type Node = {st: State, at: number, up?: Node}
    const on = reader(), start: Node = {st: it.init(params), at: -1}
    const seen = new Map<string, number>([[stateKey(start.st), -1]])
    let level: Node[] = [start], nodes = 0
    // (a share of the budget: the kept run is already 1-minimal)
    const until = Math.min(deadline, now() + Math.max(50, (deadline - t0) / 4))
    for (let depth = 1; depth < below && level.length; depth++) {
      const next: Node[] = []
      for (const node of level) {
        for (const at of places) {
          if ((++nodes & 31) === 0 && now() > until || nodes > 50_000) return undefined
          let q = -1
          for (const x of at) if (x > node.at) { q = x; break }
          if (q < 0) continue
          const after = take(node.st, all[q]!)
          if (!after) continue
          if (on.step(node.st, all[q]!, after)) {
            const idx: number[] = [q], states: State[] = [after]
            for (let u: Node | undefined = node; u; u = u.up) { states.push(u.st); if (u.at >= 0) idx.push(u.at) }
            return {idx: idx.reverse(), states: states.reverse()}
          }
          const key = stateKey(after), had = seen.get(key)
          if (had !== undefined && had <= q) continue
          seen.set(key, q)
          next.push({st: after, at: q, up: node})
        }
      }
      level = next
    }
    return undefined
  }
}

// The run, minimized (see the head of this file). Throws if the run given does not break the law.
export function minimizeRun<R extends RunTrace | readonly RunRequest[]>(rule: RuleLike, law: Law | Watched, run: R, opts: MinimizeOptions = {}): R {
  return minimizeRunDetailed(rule, law, run, opts).run
}

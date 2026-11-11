// One work bank. The counter vector and F are authoritative exact integers on
// the frozen coefficient lattice; endpoints may be arbitrary exact rationals.
import {completeWorkProfile} from './work-profile.ts'
import {type WorkKey, legacyWeights, workKeys} from './work-kinds.ts'
import {type ExactRaw, type WorkAmount, commonWorkDenominator, compareWork, exactRaw, minWork, workAdd, workAmount, workFromNumber, workShare, workSub, workToNumber, zeroWork} from './work-amount.ts'
export type {ExactRaw, WorkAmount}
export class BudgetExpired extends Error {
  constructor(readonly phase: string) { super(`work budget (${phase})`); this.name = 'BudgetExpired' }
}
export type WorkEndpointKind = 'root' | 'scope' | 'work-cap' | 'deadline'
export type WorkEndpoint = Readonly<{id: number, kind: WorkEndpointKind, end: ExactRaw}>
export type WorkCapacityRefusal = Readonly<{
  reason: 'quantum' | 'check' | 'scope-entry', limiting: readonly WorkEndpoint[],
  actual: ExactRaw, reserved: ExactRaw, requested?: ExactRaw,
}>
export type WorkCounterVector = Readonly<Record<WorkKey, string>>
export type WorkAdmissionSnapshot = Readonly<{
  version: 'strict-work-v1', rootEpoch: number, scopeEpoch: number, counterEpoch: number,
  actual: ExactRaw, reserved: ExactRaw, effectiveEnd: ExactRaw | null,
  activeEndpoints: readonly WorkEndpoint[], weights: Readonly<Record<WorkKey, ExactRaw>>,
  rootBaseline: Readonly<{actual: ExactRaw, counters: WorkCounterVector}> | null,
  counters: WorkCounterVector,
}>
export type WorkAdmissionEvent = WorkAdmissionSnapshot & Readonly<{
  sequence: number, kind: 'trace-start' | 'trace-end' | 'reserve' | 'start' | 'release' | 'invalidate' | 'refuse' | 'scope-enter' | 'scope-exit',
  sink?: WorkKey, site?: string, requested?: string, granted?: string, leaseId?: number,
}>
export type WorkAdmissionObserver = (event: WorkAdmissionEvent) => void
export type WorkLease = Readonly<{granted: number, remaining: number, start: (count?: number) => void}>
type Scope = {id: number, kind: WorkEndpointKind, end: WorkAmount}
type LeaseState = {id: number, sink: WorkKey, site?: string, remaining: bigint, granted: number, epoch: number, live: boolean}
const nextEpoch = (n: number): number => {
  if (!Number.isSafeInteger(n) || n < 0 || n === Number.MAX_SAFE_INTEGER) throw new RangeError('work epoch exhausted')
  return n + 1
}
const natural = (n: number): bigint => {
  if (!Number.isSafeInteger(n) || n < 0) throw new RangeError('work count must be a nonnegative safe integer')
  return BigInt(n)
}
const synchronous = <T>(value: T): T => {
  if (value && typeof value === 'object' && 'then' in value) throw new TypeError('work leases and scopes must be synchronous')
  return value
}

export class WorkLedger {
  readonly weights: Readonly<Record<WorkKey, WorkAmount>>
  readonly denominator: bigint
  private readonly units: Readonly<Record<WorkKey, bigint>>
  private readonly counters = Object.fromEntries(workKeys.map(key => [key, 0n])) as Record<WorkKey, bigint>
  private consumed = 0n
  private held = 0n
  private readonly scopes: Scope[] = []
  private readonly leases = new Set<LeaseState>()
  private readonly observers: WorkAdmissionObserver[] = []
  private baseline: WorkAdmissionSnapshot['rootBaseline'] = null
  private rootEpoch = 0
  private scopeEpoch = 0
  private counterEpoch = 0
  private leaseSequence = 0
  private endpointSequence = 0
  private eventSequence = 0
  private notifying = false
  private readonly capacityErrors = new WeakMap<object, WorkCapacityRefusal>()
  constructor(weights: Readonly<Record<WorkKey, number>>) {
    if (Object.keys(weights).length !== workKeys.length || workKeys.some(key => !Object.hasOwn(weights, key) || !Number.isFinite(weights[key]) || weights[key] < 0)) throw new RangeError('work ledger requires the exact frozen coefficient vector')
    this.weights = Object.freeze(Object.fromEntries(workKeys.map(key => [key, workFromNumber(weights[key])]))) as Readonly<Record<WorkKey, WorkAmount>>
    this.denominator = commonWorkDenominator(Object.values(this.weights))
    this.units = Object.freeze(Object.fromEntries(workKeys.map(key => [key, this.weights[key].num * (this.denominator / this.weights[key].den)]))) as Readonly<Record<WorkKey, bigint>>
  }
  actual(): WorkAmount { return workAmount(this.consumed, this.denominator) }
  reserved(): WorkAmount { return workAmount(this.held, this.denominator) }
  bounded(): boolean { return this.scopes.length > 0 }
  inBudget(): boolean { return this.scopes.some(scope => scope.kind === 'root') }
  check(phase: string): void { this.checkEntry(); this.invariant(); void phase }
  checkAmount(amount: WorkAmount, phase: string): void {
    this.checkEntry()
    if (amount.den <= 0n || amount.num < 0n) throw new RangeError('invalid work admission amount')
    const left = this.available()
    if (left !== null && compareWork(amount, left) > 0) { this.emit('refuse', {site: phase}); throw this.capacityError(phase, 'check', amount) }
  }
  counter(key: WorkKey): bigint { return this.counters[key] }
  currentScope(): WorkEndpoint | undefined {
    const scope = this.scopes[this.scopes.length - 1]
    return scope && Object.freeze({id: scope.id, kind: scope.kind, end: exactRaw(scope.end)})
  }
  // Only this ledger can authenticate its own capacity failures. Error text,
  // stale leases and exceptions from native/observer code confer no provenance.
  capacityRefusal(error: unknown): WorkCapacityRefusal | undefined {
    return typeof error === 'object' && error !== null ? this.capacityErrors.get(error) : undefined
  }
  private capacityError(phase: string, reason: WorkCapacityRefusal['reason'], requested?: WorkAmount): BudgetExpired {
    const error = new BudgetExpired(phase), end = this.endpoint()
    const limiting = this.scopes.filter(scope => end !== null && compareWork(scope.end, end) === 0)
      .map(scope => Object.freeze({id: scope.id, kind: scope.kind, end: exactRaw(scope.end)}))
    this.capacityErrors.set(error, Object.freeze({reason, limiting: Object.freeze(limiting),
      actual: exactRaw(this.actual()), reserved: exactRaw(this.reserved()),
      ...(requested ? {requested: exactRaw(requested)} : {})}))
    return error
  }
  endpoint(): WorkAmount | null {
    let end: WorkAmount | null = null
    for (const scope of this.scopes) end = end === null ? scope.end : minWork(end, scope.end)
    return end
  }
  available(): WorkAmount | null {
    const end = this.endpoint()
    return end === null ? null : workSub(end, workAmount(this.consumed + this.held, this.denominator))
  }
  private vector(): WorkCounterVector { return Object.freeze(Object.fromEntries(workKeys.map(key => [key, String(this.counters[key])])) as Record<WorkKey, string>) }
  snapshot(): WorkAdmissionSnapshot {
    const end = this.endpoint()
    return Object.freeze({version: 'strict-work-v1', rootEpoch: this.rootEpoch, scopeEpoch: this.scopeEpoch, counterEpoch: this.counterEpoch,
      actual: exactRaw(this.actual()), reserved: exactRaw(this.reserved()), effectiveEnd: end === null ? null : exactRaw(end),
      activeEndpoints: Object.freeze(this.scopes.map(scope => Object.freeze({id: scope.id, kind: scope.kind, end: exactRaw(scope.end)}))),
      weights: Object.freeze(Object.fromEntries(workKeys.map(key => [key, exactRaw(this.weights[key])]))) as Readonly<Record<WorkKey, ExactRaw>>,
      rootBaseline: this.baseline, counters: this.vector()})
  }
  private emit(kind: WorkAdmissionEvent['kind'], extra: Pick<WorkAdmissionEvent, 'sink' | 'site' | 'requested' | 'granted' | 'leaseId'> = {}): void {
    if (!this.observers.length) return
    if (this.notifying) throw new Error('work trace must not reenter the meter')
    this.eventSequence = nextEpoch(this.eventSequence)
    const event = Object.freeze({...this.snapshot(), sequence: this.eventSequence, kind, ...extra})
    this.notifying = true
    try { for (const observe of this.observers) observe(event) } finally { this.notifying = false }
  }
  private checkEntry(): void { if (this.notifying) throw new Error('work trace must not reenter the meter') }
  private invariant(): void {
    const end = this.endpoint()
    if (this.consumed < 0n || this.held < 0n || end !== null && (this.consumed + this.held) * end.den > end.num * this.denominator) throw new Error('work admission invariant violated')
  }
  private invalidate(except?: LeaseState): void {
    let changed = false
    for (const lease of this.leases) if (lease !== except && lease.live) {
      this.held -= lease.remaining * this.units[lease.sink]
      lease.remaining = 0n; lease.live = false; changed = true
    }
    if (changed) { this.invariant(); this.emit('invalidate') }
  }
  withTrace<T>(observe: WorkAdmissionObserver, run: () => T): T {
    this.checkEntry(); this.observers.push(observe)
    try { this.emit('trace-start'); return synchronous(run()) }
    finally { try { this.emit('trace-end') } finally { this.observers.pop() } }
  }
  withEndpoint<T>(kind: WorkEndpointKind, end: WorkAmount, run: () => T): T {
    this.checkEntry()
    if (end.den <= 0n || end.num < 0n) throw new RangeError('work endpoint must be nonnegative with a positive denominator')
    const nextRoot = kind === 'root' ? nextEpoch(this.rootEpoch) : this.rootEpoch
    const nextScope = nextEpoch(this.scopeEpoch), nextEndpoint = nextEpoch(this.endpointSequence)
    this.invalidate()
    if (compareWork(this.actual(), end) > 0) { this.emit('refuse', {site: 'scope entry'}); throw this.capacityError('scope entry', 'scope-entry') }
    const priorBaseline = this.baseline
    if (kind === 'root') {
      if (this.scopes.some(scope => scope.kind === 'root')) throw new Error('cannot replace an active work root')
      this.rootEpoch = nextRoot
      this.baseline = Object.freeze({actual: exactRaw(this.actual()), counters: this.vector()})
    }
    this.scopeEpoch = nextScope; this.endpointSequence = nextEndpoint
    const scope = {id: this.endpointSequence, kind, end: workAmount(end.num, end.den)}
    this.scopes.push(scope)
    try { this.invariant(); this.emit('scope-enter'); return synchronous(run()) }
    finally {
      try { this.invalidate(); this.emit('scope-exit') }
      finally {
        this.scopes.pop()
        if (kind === 'root') this.baseline = priorBaseline
        this.scopeEpoch = nextEpoch(this.scopeEpoch)
        this.invariant()
      }
    }
  }
  withBudget<T>(grant: WorkAmount, run: () => T): T {
    if (grant.den <= 0n || grant.num < 0n) throw new RangeError('work grant must be nonnegative')
    return this.withEndpoint(this.scopes.some(scope => scope.kind === 'root') ? 'scope' : 'root', workAdd(this.actual(), grant), run)
  }
  withShare<T>(numerator: bigint, denominator: bigint, run: () => T): T {
    const available = this.available()
    if (available === null) throw new Error('work share needs an inherited finite endpoint')
    return this.withBudget(workShare(available, numerator, denominator), run)
  }
  withChunk<T>(sink: WorkKey, requested: number, run: (lease: WorkLease) => T, site?: string): T {
    this.checkEntry()
    if (!Object.hasOwn(this.units, sink)) throw new RangeError('unknown work sink')
    const count = natural(requested), weight = this.units[sink], end = this.endpoint()
    let grant = count
    if (end !== null && weight > 0n) {
      const left = end.num * this.denominator - (this.consumed + this.held) * end.den
      const fits = left <= 0n ? 0n : left / (weight * end.den)
      if (grant > fits) grant = fits
    }
    if (count > 0n && grant === 0n) { this.emit('refuse', {sink, site, requested: String(count), granted: '0'}); throw this.capacityError(site ?? sink, 'quantum', workAmount(count * weight, this.denominator)) }
    this.leaseSequence = nextEpoch(this.leaseSequence)
    const state: LeaseState = {id: this.leaseSequence, sink, site, remaining: grant, granted: Number(grant), epoch: this.counterEpoch, live: true}
    this.leases.add(state); this.held += grant * weight
    this.invariant()
    const lease: WorkLease = Object.freeze({granted: state.granted, get remaining() { return Number(state.remaining) }, start: (n = 1) => {
      this.checkEntry(); const take = natural(n)
      if (!state.live || state.epoch !== this.counterEpoch) throw new BudgetExpired(`stale lease: ${site ?? sink}`)
      if (take > state.remaining) throw new RangeError('work lease overspend')
      if (take === 0n) return
      // Other counters/scopes cannot share this credit. Expected owner commits
      // advance this lease's epoch; all unrelated reservations become stale.
      const nextCounter = nextEpoch(this.counterEpoch)
      this.invalidate(state)
      state.remaining -= take; this.held -= take * weight; this.consumed += take * weight; this.counters[sink] += take
      this.counterEpoch = nextCounter; state.epoch = nextCounter
      this.invariant(); this.emit('start', {sink, site, granted: String(take), leaseId: state.id})
    }})
    try {
      this.emit('reserve', {sink, site, requested: String(count), granted: String(grant), leaseId: state.id})
      return synchronous(run(lease))
    }
    finally {
      try {
        if (state.live) { this.held -= state.remaining * weight; state.remaining = 0n; state.live = false; this.invariant(); this.emit('release', {sink, site, leaseId: state.id}) }
      } finally { this.leases.delete(state) }
    }
  }
  // An indivisible unit has to fit in full. A partial reservation is retired
  // without starting work, but its refusal still names the real boundary.
  start(sink: WorkKey, count = 1, site?: string): void {
    this.withChunk(sink, count, lease => {
      if (lease.granted !== count) throw this.capacityError(site ?? sink, 'quantum',
        workAmount(natural(count) * this.units[sink], this.denominator))
      lease.start(count)
    }, site)
  }
  // Compatibility seeds are allowed only outside a bounded root/scope. During
  // counted work, a direct counter assignment is an unadmitted mutation.
  setUnscopedCounter(key: WorkKey, value: number): void {
    this.checkEntry()
    if (this.bounded() || this.leases.size) throw new Error(`unadmitted work counter mutation: ${key}`)
    const next = natural(value), epoch = nextEpoch(this.counterEpoch)
    this.consumed += (next - this.counters[key]) * this.units[key]
    this.counters[key] = next; this.counterEpoch = epoch
  }
}
const weights = Object.freeze({...Object.fromEntries(legacyWeights), ...completeWorkProfile.weights}) as Readonly<Record<WorkKey, number>>
export const workLedger = new WorkLedger(weights)
export const workSinkRegistry = Object.freeze(workKeys.map(key => Object.freeze({key, weight: exactRaw(workLedger.weights[key])})))
export const withAdmittedChunk = <T>(sink: WorkKey, requested: number, run: (lease: WorkLease) => T, site?: string): T => workLedger.withChunk(sink, requested, run, site)
export const withWorkAdmissionTrace = <T>(observe: WorkAdmissionObserver, run: () => T): T => workLedger.withTrace(observe, run)
export const workAdmissionSnapshot = (): WorkAdmissionSnapshot => workLedger.snapshot()
// Display only. No allocator or endpoint constructor may consume this value.
export const admittedWorkNumber = (): number => workToNumber(workLedger.actual())
export const admittedWork = (): WorkAmount => workLedger.actual()
export const remainingAdmittedWork = (): WorkAmount | null => workLedger.available()
export const emptyWork = zeroWork
// Atomic adapters still use the one allocator. They refuse a partial grant
// before any body starts; loops which can stop early consume a lease itemwise.
export function startWork(sink: WorkKey, count = 1, site?: string): void {
  if (!completeWorkProfile.enabled) return
  workLedger.start(sink, count, site)
}
export function workCounterView<T extends Record<string, number>>(initial: T, mapping: Partial<Record<keyof T, WorkKey>>): T {
  if (!completeWorkProfile.enabled) return initial
  return new Proxy(initial, {
    get(target, property, receiver) {
      const key = typeof property === 'string' ? mapping[property as keyof T] : undefined
      return key === undefined ? Reflect.get(target, property, receiver) : Number(workLedger.counter(key))
    },
    set(target, property, value, receiver) {
      const key = typeof property === 'string' ? mapping[property as keyof T] : undefined
      if (key === undefined) return Reflect.set(target, property, value, receiver)
      if (typeof value !== 'number') throw new RangeError('work counter must be numeric')
      workLedger.setUnscopedCounter(key, value)
      return true
    },
  })
}

import {strict as assert} from 'node:assert'

// Versioned read-only contract. No phase-specific coefficient or synthesized count.
export const meterKeys = ['fm','fcells','plainRows','values','copies','edges','scan','pivotRows','unitRows','unfoldRows','goalNodes','translateRows','tableCells','checkSteps','astNodes','evals','cubeTests','ticks','cdclNodes','epr'] as const
export type MeterKey = typeof meterKeys[number]
export type Raw = Readonly<Record<MeterKey, number>>
export type Phase = Readonly<{id: number, parentId: number | null, name: string, depth: number, completed: boolean, raw: Raw, exclusiveRaw: Raw, wallMs: number, exclusiveWallMs: number, units: number, exclusiveUnits: number, unitModel: 'legacy' | 'explicit-complete'}>
export function validatePhaseLedger(raw: Raw, events: readonly Phase[]) {
  const checkRaw = (row: Raw) => {
    assert.deepEqual(Object.keys(row).sort((a,b)=>a<b?-1:a>b?1:0), [...meterKeys].sort((a,b)=>a<b?-1:a>b?1:0), 'exact meter key set')
    for (const key of meterKeys) assert(Number.isSafeInteger(row[key]) && row[key] >= 0, key + ' nonnegative safe integer')
  }
  checkRaw(raw)
  assert(events.length > 0, 'nonempty ledger')
  const byId = new Map<number, Phase>(), position = new Map<number, number>()
  for (const [index, event] of events.entries()) {
    assert(Number.isSafeInteger(event.id) && event.id > 0 && !byId.has(event.id), 'unique positive phase id')
    assert(Number.isSafeInteger(event.depth) && event.depth >= 0)
    assert(typeof event.name === 'string' && event.name.length > 0)
    assert(typeof event.completed === 'boolean')
    assert(['legacy', 'explicit-complete'].includes(event.unitModel))
    for (const n of [event.wallMs, event.exclusiveWallMs, event.units, event.exclusiveUnits]) assert(Number.isFinite(n) && n >= 0, 'finite nonnegative phase cost')
    checkRaw(event.raw); checkRaw(event.exclusiveRaw)
    byId.set(event.id, event); position.set(event.id, index)
  }
  const roots = events.filter(event => event.parentId === null)
  assert.equal(roots.length, 1, 'one root')
  const root = roots[0]!
  assert.equal(root.depth, 0)
  assert.equal(events.at(-1)!.id, root.id, 'root closes last')
  assert.deepEqual(root.raw, raw, 'root end-minus-start is total raw work')
  for (const event of events) {
    if (event.parentId !== null) {
      const parent = byId.get(event.parentId)
      assert(parent, 'parent exists'); assert.equal(event.depth, parent.depth + 1)
      assert(position.get(event.id)! < position.get(parent.id)!, 'child closes before parent')
    }
    const children = events.filter(child => child.parentId === event.id)
    for (const key of meterKeys) {
      const sum = event.exclusiveRaw[key] + children.reduce((n, child) => n + child.raw[key], 0)
      assert(Number.isSafeInteger(sum)); assert.equal(sum, event.raw[key], key + ' direct-child reconciliation')
    }
  }
  for (const key of meterKeys) {
    const total = events.reduce((n, event) => n + event.exclusiveRaw[key], 0)
    assert(Number.isSafeInteger(total)); assert.equal(total, raw[key], key + ' exclusive-total reconciliation')
  }
  return {schema: 'gdp-work-phase/v1' as const, keys: [...meterKeys], events: events.length, rootCompleted: root.completed,
    phaseNames: [...new Set(events.map(event => event.name))], raw, exclusiveReconciled: true}
}
// This is exactly the mini kit's per-instance fit row; never sum inclusive rows.
export const calibrationRows = (raw: Raw, events: readonly Phase[]) => {
  validatePhaseLedger(raw, events)
  return events.map(event => ({phase: event.name, raw: event.exclusiveRaw, wallMs: event.exclusiveWallMs}))
}

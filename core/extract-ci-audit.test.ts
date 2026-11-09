import {expect, test} from 'bun:test'
import {extract, type Extraction} from './extract.ts'
import {buildLaw} from './laws.ts'
import {proveSteps} from './dsl.ts'

const noReplay = {runs: 0, states: 0, probes: false as const}
const verdict = (x: Extraction, expr: string, method = 'decide') => {
  const b = buildLaw(x, {name: expr, expr, method})
  if (b.kind !== 'step') throw new Error('expected step law')
  return proveSteps(x.rule!, x.invariants ?? [], [b.law], {from: 'any', search: false})
}

test('CI audit B1: default replay cannot validate optional calendar law translation', () => {
  for (const [source, standalone] of [
    ['export function decide(flag: boolean): number | undefined { if (flag) return 0; }', true],
    ['export function decide(flag: boolean): number | null { return flag ? 0 : null; }', true],
    ['export class Decision { values = new Map<string, number>(); decide(key: string): number | undefined { return this.values.get(key); } }', false],
  ] as const) {
    const x = extract(source, standalone ? {entry: 'decide', mode: 'standalone'} : {entry: 'Decision'})
    expect({ok: x.ok, refusals: x.refusals}).toEqual({ok: true, refusals: []})
    expect(x.evidence!.requests).toBeGreaterThan(0)
    expect(x.evidence!.fromStates).toBeGreaterThan(0)
    for (const expr of ['result - 0 <= 1 business days', '1 business days >= result - 0', '0 - result <= 1 business days']) {
      expect(() => buildLaw(x, {name: expr, expr, method: 'decide'}, {clock: 1, calendar: {weekend: ['sat', 'sun']}})).toThrow('arithmetic on an optional')
    }
  }
})

test('CI audit P2: named and destructured records have independent heap identities', () => {
  for (const reversed of [false, true]) {
    const parameters = reversed ? '{enabled}: {enabled: boolean}, arg: {enabled: boolean}' : 'arg: {enabled: boolean}, {enabled}: {enabled: boolean}'
    const x = extract(`export function decide(${parameters}): boolean { return arg.enabled; }`, {entry: 'decide', mode: 'standalone', check: noReplay})
    expect({ok: x.ok, refusals: x.refusals}).toEqual({ok: true, refusals: []})
    expect(verdict(x, 'result == enabled')).toMatchObject({proven: false, stuck: 'sat'})
    expect(verdict(x, 'result == arg.enabled')).toMatchObject({proven: true, checked: true})
    const r = x.rule!, machine = r.interpreter(), params = r.encodeParams({})
    const output = x.model!.results!.decide!
    if (output.k !== 'maybe') throw new Error('expected optional result encoding')
    const inputs = x.names!.filter(n => n.role === 'input').map(n => n.rule)
    expect(inputs).toHaveLength(2)
    expect(new Set(inputs).size).toBe(2)
    for (const first of [false, true]) for (const second of [false, true]) {
      const state = r.decode(machine.step(params, machine.init(params), r.encodeInput({[inputs[0]!]: first, [inputs[1]!]: second})))
      expect(state[output.missing]).toBe(false)
      expect(state[output.name]).toBe(reversed ? second : first)
    }
  }
})

test('CI audit B2: falsy map payloads remain present in both truthiness arms', () => {
  for (const kind of ['boolean', 'number']) for (const negated of [false, true]) {
    const branch = negated ? 'if (!v) return v === undefined; return true;' : 'if (v) return true; return v === undefined;'
    const source = `export class Decision { values = new Map<string, ${kind}>(); put(key: string, value: ${kind}) { this.values.set(key, value); } test(key: string): boolean { const v = this.values.get(key); ${branch} } }`
    const x = extract(source, {entry: 'Decision', check: noReplay})
    expect({ok: x.ok, refusals: x.refusals}).toEqual({ok: true, refusals: []})
    expect(verdict(x, 'result == true', 'test')).toMatchObject({proven: false, stuck: 'sat'})
    const replayed = extract(source, {entry: 'Decision'})
    expect({ok: replayed.ok, refusals: replayed.refusals}).toEqual({ok: true, refusals: []})
    expect(replayed.evidence!.requests).toBeGreaterThan(0)
  }
}, 60000)

test('CI audit C1: accepted records report the plain-data contract', () => {
  for (const source of [
    'export function decide(facts: {enabled: boolean}): boolean { return facts.enabled === facts.enabled; }',
    'export function decide({enabled}: {enabled: boolean}): {accepted: boolean} { return {accepted: enabled}; }',
  ]) {
    const x = extract(source, {entry: 'decide', mode: 'standalone'})
    expect({ok: x.ok, refusals: x.refusals}).toEqual({ok: true, refusals: []})
    const notes = x.notes.join('\n')
    expect(notes).toContain('immutable plain-data snapshots')
    expect(notes).toContain('own data properties')
    expect(notes).toContain('no accessors or Proxies')
  }
  // An accessor-backed object is explicitly outside that contract, despite its structural type.
  let reads = 0
  const outsideContract = {get enabled() { return ++reads % 2 === 0 }}
  expect(outsideContract.enabled === outsideContract.enabled).toBe(false)
  const snapshot = {enabled: true}
  expect(snapshot.enabled === snapshot.enabled).toBe(true)
})

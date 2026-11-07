import {expect, test} from 'bun:test'
import {cpair, interpret} from '../../../core/machine.ts'
import {mldr} from './mldr.ts'

const req = (op: number, S: number[] = [], i = 0, j = 0) => ({op, i, j, hx: 0, hy: 0, S: new Map(S.map(k => [k, 1])), Q2: new Map<number, number>()})

test('MLDR initializes every configuration row atomically from the same nonempty set', () => {
  const m = mldr().machine, run = interpret(m), p = {size: 3}
  const start = run.init(p)
  expect(start.scalars.started).toBe(0)
  const st = run.step(p, start, req(0, [0, 2]))
  expect(st.scalars.started).toBe(1)
  for (let a = 0; a < 3; a++) for (let b = 0; b < 3; b++) expect(st.maps.Config!.get(cpair(a, b)) ?? 0).toBe(b === 1 ? 0 : 1)
  // A later init request cannot rewrite the configuration.
  expect(run.step(p, st, req(0, [1], 0, 1)).maps.Config).toEqual(st.maps.Config)
  expect(() => run.step(p, start, req(0))).toThrow()
})

test('MLDR still elects a leader with a majority and demotes voters', () => {
  const m = mldr().machine, run = interpret(m), p = {size: 3}
  const st = run.step(p, run.init(p), req(0, [0, 1, 2]))
  const elected = run.step(p, st, req(2, [0, 1]))
  expect(elected.maps.St!.get(0)).toBe(1)
  expect(elected.maps.CT!.get(0)).toBe(1)
  expect(elected.maps.CT!.get(1)).toBe(1)
  expect(elected.maps.CfgT!.get(0)).toBe(1)
  expect(() => run.step(p, st, req(2, [0]))).toThrow()
  const badRun = interpret(mldr('become_leader without a majority').machine)
  expect(badRun.step(p, st, req(2, [0])).maps.St!.get(0)).toBe(1)
})

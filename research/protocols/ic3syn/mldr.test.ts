import {expect, test} from 'bun:test'
import {interpret} from '../../../core/machine.ts'
import {mldr} from './mldr.ts'
import {N} from './common.ts'

const req = (op: number, S: number[] = [], i = 0, j = 0) => ({op, i, j, hx: 0, hy: 0, S: new Map(S.map(k => [k, 1])), Q2: new Map<number, number>()})

test('MLDR P* preserves equal-version rows during pick/copy and starts only after copying', () => {
  const run = interpret(mldr().machine), p = {size: 3}
  let st = run.init(p)
  const aligned = () => {
    for (let a = 0; a < 3; a++) for (let b = 0; b < 3; b++) if ((st.maps.CV!.get(a) ?? 0) === (st.maps.CV!.get(b) ?? 0))
      for (let k = 0; k < 3; k++) expect(st.maps.Config!.get(a * N + k) ?? 0).toBe(st.maps.Config!.get(b * N + k) ?? 0)
  }
  expect(st.scalars.started).toBe(0)
  expect(Object.keys(st.maps).sort()).toEqual(['CT', 'CV', 'CfgT', 'Config', 'St'])
  expect(() => run.step(p, st, req(0))).toThrow()
  aligned()
  st = run.step(p, st, req(0, [0, 2])); aligned()
  expect(st.maps.CV!.get(0)).toBe(1)
  expect(st.maps.CV!.get(1) ?? 0).toBe(0)
  expect(run.step(p, st, req(2)).scalars.started).toBe(0)
  expect(run.step(p, st, req(0, [1], 0, 1)).maps.Config).toEqual(st.maps.Config)
  for (const i of [1, 2]) { st = run.step(p, st, req(1, [], i)); aligned() }
  st = run.step(p, st, req(2))
  expect(st.scalars.started).toBe(1)
  for (let a = 0; a < 3; a++) for (let b = 0; b < 3; b++) expect(st.maps.Config!.get(a * N + b) ?? 0).toBe(b === 1 ? 0 : 1)
})

test('MLDR P* retains the majority guard and its broken negative control', () => {
  const run = interpret(mldr().machine), p = {size: 3}
  let st = run.step(p, run.init(p), req(0, [0, 1, 2]))
  for (const i of [1, 2]) st = run.step(p, st, req(1, [], i))
  st = run.step(p, st, req(2))
  const elected = run.step(p, st, req(4, [0, 1]))
  expect(elected.maps.St!.get(0)).toBe(1)
  expect(elected.maps.CT!.get(0)).toBe(1)
  expect(elected.maps.CT!.get(1)).toBe(1)
  expect(elected.maps.CfgT!.get(0)).toBe(1)
  expect(() => run.step(p, st, req(4, [0]))).toThrow()
  expect(interpret(mldr('without a majority').machine).step(p, st, req(4, [0])).maps.St!.get(0)).toBe(1)
})

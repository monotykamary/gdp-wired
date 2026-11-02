import {expect, test} from 'bun:test'
import {type E} from '../../../core/machine.ts'
import {showC, showE} from './show.ts'

test('profile text preserves nested tuple and projection structure', () => {
  const pair: E = {op: 'tup', a: {op: 'const', value: 2}, b: {op: 'var', name: 'x'}}
  const tail: E = {op: 'proj', k: 1, a: pair}
  expect(showE(pair)).toBe('⟨2, x⟩')
  expect(showE(tail)).toBe('proj(1, ⟨2, x⟩)')
  expect(showE({op: 'get', map: 'M', key: pair})).toBe('M[⟨2, x⟩]')
  expect(showC({op: '=', a: tail, b: {op: 'var', name: 'x'}})).toBe('proj(1, ⟨2, x⟩) = x')
})

import {expect, test} from 'bun:test'
import {checkRefutation, checkWitness} from './check.ts'
import {add, eq, k, le, lt, nat, solve, v} from './solver.ts'

test('2x = 1 has no integer solution, by a cut', () => {
  const cs = eq(add(v('x'), v('x')), k(1))
  const r = solve(cs)
  expect(r.kind).toBe('refuted')
  if (r.kind === 'refuted') expect(checkRefutation(cs, r.steps)).toBe(true)
})
test('3x + 3y = 2 refuted; x + 2y = 3 with x, y >= 0 has a witness', () => {
  const a = eq(add(v('x'), v('x'), v('x'), v('y'), v('y'), v('y')), k(2))
  const ra = solve(a)
  expect(ra.kind === 'refuted' && checkRefutation(a, ra.steps)).toBe(true)
  const b = [...eq(add(v('x'), v('y'), v('y')), k(3)), ...nat('x', 'y')]
  const rb = solve(b)
  expect(rb.kind === 'sat' && checkWitness(b, rb.witness)).toBe(true)
})
test('random small systems: every refutation and witness checks, and agrees with brute force', () => {
  let seed = 7
  const rnd = (n: number) => ((seed = (seed * 1103515245 + 12345) % 2 ** 31), seed % n)
  let refuted = 0, sat = 0, unknown = 0
  for (let trial = 0; trial < 3000; trial++) {
    const names = ['x', 'y', 'z']
    const cs = [...nat(...names), ...names.flatMap(n => le(v(n), k(6)))]
    for (let i = 0; i < 1 + rnd(4); i++) {
      const lin = add(...names.map(n => ({[n]: rnd(7) - 3})), k(rnd(13) - 6))
      cs.push({lin, label: `c${i}`})
    }
    let brute = false
    for (let x = 0; x <= 6 && !brute; x++) for (let y = 0; y <= 6 && !brute; y++) for (let z = 0; z <= 6 && !brute; z++) brute = checkWitness(cs, {x, y, z})
    const r = solve(cs)
    if (r.kind === 'refuted') {
      refuted++
      expect(brute).toBe(false)
      expect(checkRefutation(cs, r.steps)).toBe(true)
    } else if (r.kind === 'sat') {
      sat++
      expect(brute).toBe(true)
      expect(checkWitness(cs, r.witness)).toBe(true)
    } else unknown++
  }
  console.log({refuted, sat, unknown})
})

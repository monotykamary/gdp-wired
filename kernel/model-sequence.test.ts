import {expect, test} from 'bun:test'
import {atMost, n, x} from '../core/machine.ts'
import {check, type Goal} from './kernel.ts'
import {clock, grow} from './prove.ts'
import {REFUTED} from './cdcl.ts'
import {modelSequence} from './model-sequence.ts'

test('growing model queries remap cores after insertion, reordering and duplication', () => {
  const ask = modelSequence(), lower=atMost(n(2),x('x')), upper=atMost(x('x'),n(1)), other=atMost(x('y'),n(4))
  expect(ask({name:'sequence',hyps:[other,lower]},clock()+5000)).toMatchObject({stuck:'sat'})
  const goal:Goal={name:'sequence',hyps:[lower,upper,other,lower]}
  const out=ask(goal,clock()+5000)
  expect(out).toMatchObject({why:REFUTED})
  expect(out.core?.length).toBeGreaterThan(0)
  expect(out.core!.every(i=>Number.isInteger(i)&&i>=0&&i<goal.hyps.length)).toBe(true)
  const part={...goal,hyps:out.core!.map(i=>goal.hyps[i]!)}
  const proof=grow(part,new Map(),{nodes:0,until:clock()+5000})
  expect('tree' in proof && check(part,proof.tree)).toBe(true)
  // A removed hypothesis must invalidate learned contradictions.
  expect(ask({name:'sequence',hyps:[other,lower]},clock()+5000)).toMatchObject({stuck:'sat'})
  // A changed bound is not the old expression, even under the same goal name.
  expect(ask({name:'sequence',hyps:[atMost(x('x'),n(3)),other,lower]},clock()+5000)).toMatchObject({stuck:'sat'})
})

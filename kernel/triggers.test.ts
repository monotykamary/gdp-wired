import {expect, test} from 'bun:test'
import {type Machine, type Law, all, get, n, not, same, x} from '../core/machine.ts'
import {triggered} from './prove.ts'

const m: Machine = {name: 'joint reads', params: ['a','b','c','d'], inputs: [], state: {}, maps: {R: 0, F: 0}, relations: {R: ['Node','Node']}, step: {}}
const edge = (a: string, b: string) => same(get('R', {op:'tup',a:x(a),b:x(b)}),n(1))
const law: Law = {name: 'edge field', forall: 'u', keys: ['v'], holds: not(all(edge('u','v'),not(same(get('F',x('u')),x('v')))))}

test('joint tuple triggers do not admit the Cartesian product of independent field reads', () => {
  const inst = {[law.name]: ['a','b','a','c','d','b'].map(x)}
  const build = () => [{name: 'query',hyps: [edge('a','b'),same(get('F',x('a')),x('c')),same(get('F',x('d')),x('b'))]}]
  expect(triggered(m,[law],inst,build,['a'])).toEqual({[law.name]: [x('a'),x('b')]})
  expect(inst[law.name]).toHaveLength(6)
})

test('tuple-keyed function images retain legacy focus seeds without widening unary fields', () => {
  const inst = {[law.name]: ['a','c','d','b'].map(x)}, build = () => [{name: 'query', hyps: []}]
  const withImage: Machine = {...m, inputs: ['i','j','value'], maps: {...m.maps, W: 0}, step: {maps: {W: {key: {op: 'tup', a: x('i'), b: x('j')}, value: x('value')}}}}
  expect(triggered(withImage, [law], inst, build, ['a'])).toEqual({[law.name]: [x('a'),x('c')]})
  const unary: Machine = {...withImage, step: {maps: {W: {key: x('i'), value: x('value')}}}}
  expect(triggered(unary, [law], inst, build, ['a'])).toEqual({[law.name]: []})
  expect(inst[law.name]).toHaveLength(4)
})

test('newly relevant tuples enter the trigger fixpoint', () => {
  const inst = {[law.name]: ['a','b','c','d','d','c'].map(x)}
  const build = (kept: typeof inst) => [{name:'query',hyps:[edge('a','b'),...(kept[law.name]!.length ? [edge('c','d')] : [])]}]
  expect(triggered(m,[law],inst,build)).toEqual({[law.name]: ['a','b','c','d'].map(x)})
})

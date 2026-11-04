import {expect,test} from 'bun:test'
import {get,n,x,same} from '../../core/machine.ts'
import {Meter} from './match.ts'
import {TriggerIndex} from './trigger-index.ts'
test('filtered matches do not spend result slots on rejected duplicates',()=>{
  const p=get('F',x('k')),meter=new Meter(10000),g=new TriggerIndex(meter,[p]);g.seed([same(get('F',n(1)),n(9)),same(get('F',n(2)),n(9)),same(get('F',n(3)),n(9))])
  let enumerated=0
  const result=g.match([p],['k'],1,b=>{meter.tick();enumerated++;return b.k!.op==='const'&&b.k!.value===3})
  expect(result).toEqual([{k:n(3)}]);expect(enumerated).toBe(3)
})
test('an all-rejecting predicate remains fuel bounded and returns no invented binding',()=>{
  const p=get('F',x('k')),m=new Meter(10000),g=new TriggerIndex(m,[p]);g.seed([same(get('F',n(1)),n(9))])
  expect(g.match([p],['k'],32,()=>{m.tick();return false})).toEqual([])
  expect(g.match([p],['k'],0,()=>{throw Error('must not call predicate')})).toEqual([])
})

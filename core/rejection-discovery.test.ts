import {expect,test} from 'bun:test'
import {type Law,type Machine,n,plus,same,x} from './machine.ts'
import {rejectionStage} from './rejection-discovery.ts'
import {createRejectionStage} from './rejection-stage.ts'
import {counted,fullRate} from '../kernel/prove.ts'
const full=(run:()=>void)=>counted(fullRate,run,true)
test('the production screen goes directly to relative size-two replay',()=>{
 const source:Machine={name:'relative copy',params:['dimension'],inputs:[],state:{left:n(0),right:n(0)},counts:{unused:{j:'r',key:'c',below:n(1),body:n(0)}},step:{state:{left:x('right')}}}
 const law:Law={name:'left zero',holds:same(x('left'),n(0))}
 full(()=>{
  const stage=rejectionStage(source,source,[],[law],10000)
  expect(stage.active()).toEqual([])
  expect(stage.phases.map(phase=>phase.kind)).toEqual(['relative-two-server'])
  expect(stage.evidence()[0]?.kind).toBe('relative')
  expect(stage.evidence()[0]?.params).toEqual({dimension:2})
 })
})
test('one shared transition is replayed once for all falsified laws',()=>{
 const source:Machine={name:'shared transition',params:[],inputs:[],state:{value:n(0)},counts:{unused:{j:'r',key:'c',below:n(1),body:n(0)}},step:{state:{value:plus(x('value'),n(1))}}}
 const laws:Law[]=['first','second','third'].map(name=>({name,holds:same(x('value'),n(0))}))
 full(()=>{
  const ledger=createRejectionStage(source,source,[],laws,10000)
  let calls=0
  const stage={...ledger,relative:(...args:Parameters<typeof ledger.relative>)=>{calls++;return ledger.relative(...args)}}
  const result=rejectionStage(source,source,[],laws,10000,{stage})
  expect(result.active()).toEqual([])
  expect(calls).toBe(1)
 })
})
test('zero allowance never explores or rejects',()=>{
 const source:Machine={name:'zero',params:[],inputs:[],state:{value:n(0)},step:{state:{value:plus(x('value'),n(1))}}}
 const law:Law={name:'value zero',holds:same(x('value'),n(0))}
 full(()=>{
  const stage=rejectionStage(source,source,[],[law],0)
  expect(stage.active()).toEqual([law])
  expect(stage.evidence()).toEqual([])
  expect(stage.phases.every(phase=>!phase.complete)).toBe(true)
 })
})

import {expect,test} from 'bun:test'
import {type Law,type Machine,type State,n,plus,same,x} from './machine.ts'
import {createRejectionStage,rejectionFamily} from './rejection-stage.ts'
import {check,obligations} from '../kernel/kernel.ts'
import {grow,counted,fullRate,fullWork} from '../kernel/prove.ts'
import {costs} from './solver.ts'
const source:Machine={name:'delayed helper',params:[],inputs:[],state:{a:n(0),b:n(0)},step:{state:{a:x('b')}}}
const H:Law={name:'H',holds:same(x('a'),n(0))},G:Law={name:'G',holds:same(x('b'),n(0))}
const state=(a:number,b:number):State=>({scalars:{a,b},maps:{}})
test('only owned rejection work is charged, and nested calls cannot reset its cap',()=>{
 const previous=costs.fm
 try{counted(fullRate,()=>{
  const stage=createRejectionStage(source,source,[],[H],1000),initial=stage.work().used
  costs.fm+=10;expect(stage.work().used).toBe(initial)
  const before=fullWork();stage.within(()=>stage.within(()=>{costs.fm++}))
  expect(stage.work().used-initial).toBe((fullWork()-before)/fullRate)
 },true)}finally{costs.fm=previous}
})

test('relative rejection returns when a later candidate excludes its pre-state; restored family proves',()=>{
 const stage=createRejectionStage(source,source,[],[H],10000)
 expect(stage.relative({},state(0,1),{}).rejected).toEqual([H]);expect(stage.active()).toEqual([])
 expect(rejectionFamily(stage,[G])).toEqual([H,G]);expect(stage.active()).toEqual([H,G])
 expect(rejectionFamily(stage,[G])).toEqual([H,G])
 expect(rejectionFamily(stage,[G])).toEqual([H,G])
 for(const goal of obligations(source,stage.active())){const out=grow(goal);expect('tree'in out&&check(goal,out.tree)).toBe(true)}
})
test('a restored law can be omitted again only after a new validated rejection',()=>{
 const m={...source,step:{state:{a:plus(x('a'),n(1))}}},stage=createRejectionStage(m,m,[],[H],10000)
 expect(stage.relative({},state(0,1),{}).rejected).toEqual([H])
 expect(rejectionFamily(stage,[G])).toEqual([H,G])
 expect(stage.reachable({},[{}]).rejected).toEqual([H])
 expect(rejectionFamily(stage,[G])).toEqual([G]);expect(rejectionFamily(stage,[G])).toEqual([G])
})
test('reachable evidence is permanent when a later candidate arrives',()=>{
 const m={...source,step:{state:{a:plus(x('a'),n(1))}}},stage=createRejectionStage(m,m,[],[H],10000)
 expect(stage.reachable({},[{}]).rejected).toEqual([H]);expect(stage.evidence()[0]!.kind).toBe('reachable')
 expect(stage.addCandidates([G])).toEqual([]);expect(stage.active()).toEqual([G])
})
test('restoration cascades through other relative witnesses',()=>{
 const X:Law={name:'X',holds:same(x('z'),n(0))},m:Machine={...source,state:{...source.state,z:n(0)},step:{state:{a:x('b'),z:x('a')}}},stage=createRejectionStage(m,m,[],[H,X],10000)
 expect(stage.relative({}, {scalars:{a:0,b:1,z:0},maps:{}},{}).rejected).toEqual([H])
 expect(stage.relative({}, {scalars:{a:1,b:0,z:0},maps:{}},{}).rejected).toEqual([X])
 expect(new Set(stage.addCandidates([G]))).toEqual(new Set([H,X]));expect(stage.active()).toEqual([H,X,G])
 expect(rejectionFamily(stage,[G])).toEqual([H,X,G])
 expect(rejectionFamily(stage,[G])).toEqual([H,X,G])
})
test('a pre-state violating any current family law rejects nothing',()=>{
 const stage=createRejectionStage(source,source,[],[H,G],10000)
 expect(stage.relative({},state(0,1),{}).status).toBe('ignored');expect(stage.active()).toEqual([H,G])
})
test('an unknown pre or post evaluation is never rejection evidence',()=>{
 const unknown:Law={name:'unbounded unknown',forall:'u',holds:same({op:'mul',k:2,a:x('u')},x('u'))}
 const stage=createRejectionStage(source,source,[],[H,unknown],10000)
 expect(stage.relative({},state(0,1),{}).status).toBe('ignored');expect(stage.reachable({},[{}]).status).toBe('ignored')
 expect(stage.active()).toEqual([H,unknown])
})
test('a request refused by the original interpreter rejects nothing',()=>{
 const m:Machine={...source,inputs:['go'],assume:same(x('go'),n(1))},stage=createRejectionStage(m,m,[],[H],10000)
 expect(stage.relative({},state(0,1),{go:0}).status).toBe('ignored');expect(stage.active()).toEqual([H])
})
test('safety is never rejected: reachable means broken, relative means weak',()=>{
 const stage=createRejectionStage(source,source,[H],[],10000)
 expect(stage.relative({},state(0,1),{}).status).toBe('weak');expect(stage.active()).toEqual([H])
 const m={...source,step:{state:{a:plus(x('a'),n(1))}}},reached=createRejectionStage(m,m,[H],[],10000)
 expect(reached.reachable({},[{}]).status).toBe('broken');expect(reached.active()).toEqual([H])
})
test('evidence snapshots cannot be rewritten by mutating input or returned records',()=>{
 const stage=createRejectionStage(source,source,[],[H],10000),pre=state(0,1)
 stage.relative({},pre,{});pre.scalars.b=0
 const evidence=stage.evidence()[0]!;if(evidence.kind==='relative')evidence.pre.scalars.b=0
 evidence.law.name='changed externally';evidence.law.holds=same(n(0),n(1))
 expect(stage.evidence()[0]!.law.name).toBe('H');expect(H.name).toBe('H')
 expect(stage.addCandidates([G])).toEqual([H])
})
test('zero allowance cannot reject and invalid allowances are refused',()=>{
 const stage=createRejectionStage(source,source,[],[H],0)
 expect(stage.relative({},state(0,1),{}).status).toBe('ignored');expect(stage.active()).toEqual([H])
 for(const limit of [-1,Infinity,NaN])expect(()=>createRejectionStage(source,source,[],[H],limit)).toThrow(RangeError)
})

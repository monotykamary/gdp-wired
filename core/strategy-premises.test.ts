import {expect,test} from 'bun:test'
import {type Law,type Machine,n,same} from './machine.ts'
import {strategyPremiseSelector} from './strategy-premises.ts'
const m:Machine={name:'selector test',params:[],inputs:[],state:{},step:{}}
const good:Law={name:'good',holds:same(n(0),n(0))},bad:Law={name:'bad',holds:same(n(0),n(1))}
test('rejected names, aliases and scalar premises cannot enter the offered family',()=>{
 const alias={...bad,name:'alias'},selector=strategyPremiseSelector(m,[good,bad,alias],[bad])
 expect(selector.find(l=>l.name==='bad')).toBeUndefined();expect(selector.find(l=>l.name==='alias')).toBeUndefined()
 expect(()=>selector.run({bad:[]},()=>1)).toThrow('rejected or unknown')
 expect(selector.run({},laws=>laws)).toEqual([good])
})
test('later mutation cannot convert a selected law to an excluded premise',()=>{
 const law={...good},selector=strategyPremiseSelector(m,[law],[bad]);law.name='changed'
 expect(()=>selector.find(()=>true)).toThrow('changed after selection')
})

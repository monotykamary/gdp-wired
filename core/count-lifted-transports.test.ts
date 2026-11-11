import {expect,test} from 'bun:test'
import {type Count} from '../kernel/kernel.ts'
import {type C,type E,type Law,all,atMost,get,ite,n,not,same,x} from './machine.ts'
import {liftedCopyTuples,matchLiftedCountBodies,proposeTransportPartitions} from './count-lifted-transports.ts'
const bit=(c:C)=>ite(c,n(1),n(0))
const member=(map:string)=>atMost(n(1),get(map,x('k')))
const count=(v:string,body:E,below:E=x('size')):Count=>({v,body,below,key:'k'})
test('transport partitions match renamed Boolean count definitions, not map labels',()=>{
 const a=member('Arbitrary$old'),b=member('arbitrary$new'),counts=[count('whole',bit(a)),count('difference',bit(all(a,not(b)))),count('intersection',bit(all(a,b))),count('newWhole',bit(b)),count('reverse',bit(all(b,not(a))))]
 const partitions=proposeTransportPartitions(counts),matches=(terms:[number,string][])=>partitions.some(partition=>JSON.stringify(partition.terms)===JSON.stringify(terms))
 expect(matches([[1,'whole'],[-1,'difference'],[-1,'intersection']])).toBe(true)
 expect(partitions.some(partition=>partition.terms.some(([coefficient,id])=>coefficient===1&&id==='newWhole'))).toBe(true)
 expect(proposeTransportPartitions(counts.map(c=>c.v==='intersection'?{...c,body:bit(not(b))}:c)).some(partition=>JSON.stringify(partition.terms)===JSON.stringify([[1,'whole'],[-1,'difference'],[-1,'intersection']]))).toBe(false)
 expect(proposeTransportPartitions(counts.map(c=>c.v==='intersection'?{...c,below:n(9)}:c)).some(partition=>JSON.stringify(partition.terms)===JSON.stringify([[1,'whole'],[-1,'difference'],[-1,'intersection']]))).toBe(false)
})
test('count-body matching is alpha-stable across direct and indicator membership reads',()=>{
 const direct=count('left',get('Arbitrary',x('k'))),indicator={...count('right',bit(atMost(n(1),get('Arbitrary',x('member'))))),key:'member'}
 expect(matchLiftedCountBodies(direct,indicator)).toBe(true)
 expect(matchLiftedCountBodies(direct,{...indicator,below:n(9)})).toBe(false)
 expect(matchLiftedCountBodies(direct,{...indicator,body:get('Different',x('member'))})).toBe(false)
 expect(matchLiftedCountBodies(direct,{...indicator,body:get('Arbitrary',x('freeRow'))})).toBe(false)
})

test('copy own-law tuples retain both independent half binders',()=>{
 const law:Law={name:'anything',forall:'alpha',keys:['beta','halfA','halfB'],holds:same(n(0),n(0))},source=x('source$renamed'),tuples=liftedCopyTuples(law,source)
 expect(tuples).toEqual([[x('alpha#'),x('beta'),x('halfA'),x('halfB')],[x('alpha#'),source,x('halfA'),x('halfB')],[source,x('beta'),x('halfA'),x('halfB')],[source,source,x('halfA'),x('halfB')]])
 expect(liftedCopyTuples({...law,keys:['beta']},source)).toEqual([])
})

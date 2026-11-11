import {expect,test} from 'bun:test'
import {type C,all,atMost,get,ite,n,not,x} from './machine.ts'
import {type Count,linOk} from '../kernel/kernel.ts'
import {clock,counted,fullRate,withWall} from '../kernel/prove.ts'
import {proveBooleanPartitionCut} from './count-boolean-partition.ts'
const fixture=():Count[]=>{const a=atMost(n(1),get('left',x('k'))),b=atMost(n(1),get('right',x('k'))),count=(v:string,c:C):Count=>({v,key:'k',below:n(4),body:ite(c,n(1),n(0))});return [count('d',all(a,not(b))),count('h',all(a,b)),count('r',a)]}
test('indicator splits prove both condition-free partition orientations',()=>withWall(performance.now()+5000,()=>counted(fullRate,()=>{
 const counts=fixture()
 for(const sign of [1,-1]){const result=proveBooleanPartitionCut(counts,[],[[sign,'d'],[sign,'h'],[-sign,'r']],clock()+500);expect(result).toBeDefined();expect(result&&linOk(counts,result.cut)).toBe(true)}
},true)))
test('an incorrect indicator partition is not returned as a cut',()=>withWall(performance.now()+5000,()=>counted(fullRate,()=>{
 const counts=fixture();counts[1]={...counts[1]!,body:counts[2]!.body}
 expect(proveBooleanPartitionCut(counts,[],[[1,'d'],[1,'h'],[-1,'r']],clock()+500)).toBeUndefined()
},true)))

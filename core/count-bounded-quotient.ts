// An ordinary finite E term, not a division axiom or a new kernel rule.
import {type E,n} from './machine.ts'
export function boundedQuotient(value:E,divisor:number,upper:number):E{
 if(!Number.isSafeInteger(divisor)||divisor<1||!Number.isSafeInteger(upper)||upper<0||upper>4096)throw Error('invalid quotient range')
 const build=(lo:number,hi:number):E=>{
  if(lo===hi)return n(lo)
  const mid=Math.floor((lo+hi+1)/2)
  return {op:'if',c:{op:'<',a:value,b:n(divisor*mid)},then:build(lo,mid-1),else:build(mid,hi)}
 }
 return build(0,Math.floor(upper/divisor))
}

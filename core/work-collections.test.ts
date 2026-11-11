import {expect,test} from 'bun:test'
import {workMap,workFilter,workFlatMap,workConcat,workStrings,workJoin,workJSON,workSlice} from './work-collections.ts'
import {completeWorkProfile} from './work-profile.ts'
import {BudgetExpired,admittedWork,withWorkAdmissionTrace,workLedger} from './work-admission.ts'
import {compareWork,workAdd,workMultiply,workAmount,workShare,workSub} from './work-amount.ts'
import {linear,type Path} from '../kernel/kernel.ts'
import type {E} from './machine.ts'
const full=completeWorkProfile.enabled?test:test.skip

test('funded collection helpers preserve native ordering and values',()=>{
 const a=[3,1,2],b=[7,5]
 expect(workMap(a,x=>x*2,'map')).toEqual(a.map(x=>x*2))
 expect(workFilter(a,x=>x!==1,'filter')).toEqual(a.filter(x=>x!==1))
 expect(workFlatMap(a,x=>[x,x+1],'flatMap')).toEqual(a.flatMap(x=>[x,x+1]))
 expect(workConcat(a,b,'concat')).toEqual([...a,...b])
 const strings=['z','a','A','aa','\ud800','\udfff','🫡','']
 expect(workStrings([...strings],'sort')).toEqual([...strings].sort())
 expect(workJoin(strings,'|','join')).toBe(strings.join('|'))
 for(const start of [-10,-2,0,1,20])expect(workSlice('abcdef',start,5)).toBe('abcdef'.slice(start,5))
})
test('funded scalar JSON preserves controls and paired or lone UTF16 surrogates',()=>{
 for(const value of [undefined,null,true,false,0,-0,1.2,Infinity,NaN,'','"\\\n\t\b\u0000','\ud800','\udfff','\ud800\udfff','\ud800a\udfff','🫡\u2028\u2029']){
  expect(workJSON(value,'json')).toBe(JSON.stringify(value))
 }
})
full('collection iteration refuses before the next callback effect',()=>{
 const seen:number[]=[],before=admittedWork(),two=workMultiply(workLedger.weights.ticks,workAmount(2n))
 expect(()=>workLedger.withBudget(workAdd(two,workShare(workLedger.weights.ticks,1n,2n)),()=>workMap([0,1,2],x=>{seen.push(x);return x},'bounded map'))).toThrow(BudgetExpired)
 expect(seen).toEqual([0,1]);expect(compareWork(workSub(admittedWork(),before),two)).toBe(0)
})
full('sort input traversal is admitted and the native whole-array sort is absent',()=>{
 const input=['b','a'];let reads=0
 Object.defineProperty(input,0,{configurable:true,get(){reads++;return'b'}})
 expect(()=>workLedger.withBudget(workAmount(0n),()=>workStrings(input,'blocked sort'))).toThrow(BudgetExpired)
 expect(reads).toBe(0)
 const original=Array.prototype.sort;let output:string[]|undefined
 Array.prototype.sort=function(){throw new Error('unfunded native sort')}
 try{output=workStrings(['b','a'],'owned sort')}finally{Array.prototype.sort=original}
 expect(output).toEqual(['a','b'])
})
full('native join is not entered on an incomplete materialization grant',()=>{
 const input=['alpha','beta'],original=Array.prototype.join
 let called=0
 Array.prototype.join=function(separator?:string){if(this===input)called++;return original.call(this,separator)}
 try{
  const need=workAdd(workMultiply(workLedger.weights.ticks,workAmount(2n)),workMultiply(workLedger.weights.tableCells,workAmount(10n)))
  expect(()=>workLedger.withBudget(workSub(need,workShare(workLedger.weights.tableCells,1n,2n)),()=>workJoin(input,':','join'))).toThrow(BudgetExpired)
  expect(called).toBe(0)
  expect(workLedger.withBudget(need,()=>workJoin(input,':','join'))).toBe('alpha:beta');expect(called).toBe(1)
 }finally{Array.prototype.join=original}
})
full('fresh cold linear output writes have independently observed emission starts',()=>{
 const create=Object.create
 for(let budget=0;budget<=12;budget++){
  let credits=0,writes=0,violations=0
  Object.create=((prototype:object|null,properties?:PropertyDescriptorMap)=>{
   const target=properties===undefined?create(prototype):create(prototype,properties)
   return prototype===null?new Proxy(target,{set(object,key,value){
    if(typeof value==='number'&&value!==0){writes++;if(credits<=0)violations++;else credits--}
    return Reflect.set(object,key,value)
   }}):target
  }) as typeof Object.create
  try{
   const expression:E={op:'var',name:`cold_${budget}`},path:Path=new Map()
   try{workLedger.withBudget(workAmount(BigInt(budget)),()=>withWorkAdmissionTrace(event=>{
    if(event.kind==='start'&&event.site?.endsWith(':emit'))credits+=Number(event.granted)
   },()=>linear(expression,path)))}catch(error){expect(error).toBeInstanceOf(BudgetExpired)}
   expect(violations,`budget ${budget}, writes ${writes}`).toBe(0)
   if(budget===12)expect(writes).toBeGreaterThan(0)
  }finally{Object.create=create}
 }
})

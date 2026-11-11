import {expect,test as profileTest} from 'bun:test'
import {stepWorkProfile} from './step-work.ts'
import {type Law,type Machine,plus,ite,n,x} from './machine.ts'
import {small} from './exists.ts'
import {countReachabilityScreen} from './count-reachability.ts'
import {countReachabilityAllowance} from './count-reachability-budget.ts'
import {BudgetExpired,clock,counted,fullRate,withBudget,withWall} from '../kernel/prove.ts'
// No-witness screens require the bookkeeping clock; raw legacy OFF omits it.
const test=profileTest.skipIf(!stepWorkProfile.enabled)
const bound=(name:string,amount:number):Law=>({name,holds:{op:'<=',a:x('v'),b:n(amount)}})
const counter:Machine={name:'unbounded counter',params:[],inputs:[],state:{v:n(0)},step:{state:{v:plus(x('v'),n(1))}}}
const run=<T>(body:()=>T,work=2_000_000)=>counted(fullRate,()=>withBudget(work,()=>withWall(clock()+work/fullRate,body)),true)
test('retained extrema are extended and only original replay can reject',()=>run(()=>{
 const states=small(counter,{},1,4,4),last=Math.max(...states.map(s=>s.scalars.v!)),law=bound('sample maximum',last)
 const screen=countReachabilityScreen(counter,counter,[],100000,()=>[{p:{},sts:states}])
 const result=screen.screen(law,1000,0,clock()+10000)
 expect(result.outcome).toBe('rejected');expect(result.stage).toBe('samples');expect(screen.rejected()).toEqual([law]);expect(result.used).toBeGreaterThan(0)
 expect(screen.screen(law,10000,10000,clock()+10000)).toBe(result)
}))
test('the fair native frontier reaches a size beyond the retained samples',()=>run(()=>{
 const machine:Machine={name:'size threshold fixture',params:['size'],inputs:[],state:{v:n(0)},step:{state:{v:ite({op:'<=',a:n(5),b:x('size')},n(1),n(0))}}}
 const law=bound('zero until larger size',0),screen=countReachabilityScreen(machine,machine,[],100000)
 const result=screen.screen(law,1000,0,clock()+10000)
 expect(result.outcome).toBe('rejected');expect(result.stage).toBe('frontier');expect(result.maxSize).toBeGreaterThanOrEqual(5)
}))
test('an arbitrary false prestate and a narrow solver model are not reachable evidence',()=>run(()=>{
 const machine:Machine={...counter,name:'stuttering counter',step:{state:{v:x('v')}}},law=bound('unreachable violation',0)
 const screen=countReachabilityScreen(machine,machine,[],100000,()=>[{p:{},sts:[{scalars:{v:9},maps:{}}]}])
 const result=screen.screen(law,1000,0,clock()+10000,{v:9})
 expect(screen.rejected()).toEqual([]);expect(result.outcome).not.toBe('rejected');expect(result.incomplete).toBe(true)
}))
test('transformed step is never used to validate an original path',()=>run(()=>{
 const original:Machine={...counter,name:'original stutter',step:{state:{v:x('v')}}},law=bound('original holds',0)
 const screen=countReachabilityScreen(original,counter,[],100000)
 expect(screen.screen(law,1000,0,clock()+10000).outcome).not.toBe('rejected');expect(screen.rejected()).toEqual([])
}))
test('zero local budget is unknown and unused candidates cost no screen work',()=>run(()=>{
 const law=bound('untouched',0),screen=countReachabilityScreen(counter,counter,[],0)
 const result=screen.screen(law,1000,0,clock()+10000)
 expect(result.outcome).toBe('exhausted');expect(result.used).toBe(0)
 expect(screen.receipts([bound('not needed',0)])[0]).toMatchObject({stage:'not-required',used:0,outcome:'not-required'})
}))
test('outer cancellation is not swallowed as a local incomplete result',()=>{
 expect(()=>run(()=>{
  const screen=countReachabilityScreen(counter,counter,[],100000),law=bound('far away',1e9)
  withBudget(0,()=>screen.screen(law,1000,0,clock()+10000))
 })).toThrow(BudgetExpired)
})
test('a reached protected caller is broken, never silently dropped',()=>run(()=>{
 const law=bound('caller',0),screen=countReachabilityScreen(counter,counter,[law],100000)
 expect(screen.screen(law,1000,0,clock()+10000).outcome).toBe('broken');expect(screen.rejected()).toEqual([])
}))
test('a decoded narrow-model request is only a hint until original replay',()=>run(()=>{
 const machine:Machine={...counter,inputs:['amount'],step:{state:{v:plus(x('v'),x('amount'))}}},law=bound('model directed',5)
 const screen=countReachabilityScreen(machine,machine,[],100000)
 const row=screen.screen(law,1000,0,clock()+10000,{v:0,amount:6})
 expect(row.stage).toBe('model');expect(row.outcome).toBe('rejected')
}))
test('huge model domains exhaust counted enumeration before a huge allocation',()=>run(()=>{
 const machine:Machine={...counter,params:['size'],inputMaps:['values'],step:{state:{v:x('v')}}},law=bound('huge unneeded domain',0)
 const screen=countReachabilityScreen(machine,machine,[],1000)
 const row=screen.screen(law,10,0,clock()+100,{size:1_000_000_000,v:0})
 expect(row.outcome).toBe('exhausted');expect(screen.rejected()).toEqual([])
}))

test('machine-view rebuilds spend only the unspent part of the first grant',()=>run(()=>{
 const law=bound('bounded repeated search',1e9),funding=new Map<string,{grant:number,used:number}>()
 const first=countReachabilityScreen(counter,counter,[],1000,undefined,funding).screen(law,10,0,clock()+1000)
 const again=countReachabilityScreen(counter,{...counter},[],1000,undefined,funding).screen({holds:law.holds,name:law.name},1e6,1e6,clock()+1000)
 expect(again.granted).toBeLessThanOrEqual(Math.max(0,first.granted-first.used)+1e-7)
 expect(funding.size).toBe(1)
}))
test('all three screen stages work with raw clocks forbidden',()=>{
 let reads=0
 const result=run(()=>{
  const time=Object.getOwnPropertyDescriptor(performance,'now'),date=Object.getOwnPropertyDescriptor(Date,'now'),forbidden=()=>{reads++;throw Error('raw reachability clock')}
  try{
   Object.defineProperty(performance,'now',{configurable:true,value:forbidden});Object.defineProperty(Date,'now',{configurable:true,value:forbidden})
   const screen=countReachabilityScreen(counter,counter,[],100000),law=bound('clock free',3)
   return screen.screen(law,1000,0,clock()+10000)
  }finally{if(time)Object.defineProperty(performance,'now',time);else Reflect.deleteProperty(performance,'now');if(date)Object.defineProperty(Date,'now',date);else Reflect.deleteProperty(Date,'now')}
 })
 expect(result.outcome).toBe('rejected');expect(reads).toBe(0)
})

test('screen grants fit their original root and have no invalid numeric inputs',()=>{
 for(const root of [0,1,100,1e6])for(const share of [0,1,100,1e9]){
  const amount=countReachabilityAllowance(root,share,share/2)
  expect(amount).toBeGreaterThanOrEqual(0);expect(amount).toBeLessThanOrEqual(root/20)
 }
 expect(()=>countReachabilityAllowance(-1,0,0)).toThrow(RangeError)
 expect(()=>countReachabilityAllowance(1,NaN,0)).toThrow(RangeError)
})

import {expect,test} from 'bun:test'
import {type Machine,type Request,type State,get,interpret,n,same,x} from './machine.ts'
import {small} from './exists.ts'
import {requestQuotient} from './request-quotient.ts'
import {completeWorkProfile} from './work-profile.ts'
import {fullWork} from './work-meter.ts'
import {BudgetExpired,withBudget} from './wall.ts'

const machine=():Machine=>({
 name:'read-set quotient',params:[],inputs:['op','a','unused'],state:{value:n(0)},
 step:{flags:{first:same(x('op'),n(0)),second:same(x('op'),n(1))},
  state:{value:{op:'if',c:{op:'flag',name:'first'},then:x('a'),else:x('value')}}},
})
function requests(m:Machine,b=3):Request[]{
 let out:Request[]=[{}]
 for(const name of m.inputs)out=out.flatMap(r=>Array.from({length:b},(_,v)=>({...r,[name]:v})))
 const sets=Array.from({length:1<<b},(_,s)=>new Map(Array.from({length:b},(_,k)=>k).filter(k=>(s>>k)&1).map(k=>[k,1])))
 for(const name of m.inputMaps??[])out=out.flatMap(r=>sets.map(set=>({...r,[name]:set})))
 return out
}
const stateText=(s:State)=>JSON.stringify([s.scalars,Object.entries(s.maps).map(([name,cells])=>[name,[...cells].filter(([,v])=>v!==0).sort((a,b)=>a[0]!-b[0]!) ]),s.defaults??{}])
function withQuotient<T>(on:boolean,run:()=>T):T{
 const previous=process.env.GDP_REQUEST_QUOTIENT
 process.env.GDP_REQUEST_QUOTIENT=on?'1':'0'
 try{return run()}finally{if(previous===undefined)delete process.env.GDP_REQUEST_QUOTIENT;else process.env.GDP_REQUEST_QUOTIENT=previous}
}
function equivalent(m:Machine,b=3):void{
 const rs=requests(m,b),q=requestQuotient(m,rs)
 expect(q).toBeDefined()
 const run=interpret(m),start=run.init({}),states=[start,...rs.flatMap(r=>{try{return[run.step({},start,r)]}catch{return[]}}).slice(0,12)]
 for(const st of states){
  const values=new Map<number,string>()
  for(let i=0;i<rs.length;i++){
   let next:State
   try{next=run.step({},st,rs[i]!)}catch{continue}
   const key=q!.classes[i]!,text=stateText(next),previous=values.get(key)
   if(previous!==undefined)expect(text).toBe(previous);else values.set(key,text)
  }
 }
}

test('specializes every selector value, including absent tags',()=>{
 const m=machine(),rs=requests(m),q=requestQuotient(m,rs)!
 expect(q.selector).toBe('op');expect(q.count).toBe(5)
 expect(q.reads.get(0)).toEqual(['a']);expect(q.reads.get(1)).toEqual([]);expect(q.reads.get(2)).toEqual([])
 expect([...requestQuotient(m,rs)!.classes]).toEqual([...q.classes]);equivalent(m)
})
test('does not generalize refusals; finite prefixes and seeded walks stay identical',()=>{
 const m=machine();m.assume=same(x('unused'),n(1))
 for(const work of[0,1,2,4,9,10,15,26,27,28,67,400])for(const walks of[0,48,100]){
  const before=withQuotient(false,()=>small(m,{},3,7,work,walks).map(stateText))
  expect(withQuotient(true,()=>small(m,{},3,7,work,walks).map(stateText))).toEqual(before)
 }
 equivalent(m)
})
test('count dependencies include bounds and bodies',()=>{
 const m:Machine={name:'count inputs',params:[],inputs:['limit','unused'],inputMaps:['S'],state:{v:n(0)},
  counts:{size:{j:'row',key:'cell',below:x('limit'),body:get('S',x('cell'))}},step:{state:{v:get('size',n(0))}}}
 expect(requestQuotient(m,requests(m))!.reads.get(undefined)).toEqual(['limit','S']);equivalent(m)
})
test('flags expand at definition scope, not an enclosing binder',()=>{
 const m=machine()
 m.step={flags:{outer:same(x('a'),n(0)),every:{op:'all',key:'a',c:{op:'flag',name:'outer'}}},
  state:{value:{op:'if',c:{op:'flag',name:'every'},then:n(1),else:n(0)}}}
 expect(requestQuotient(m,requests(m))!.reads.get(undefined)).toEqual(['a'])
})
test('unread carried support cannot change a plain-key past representative',()=>{
 const m:Machine={name:'quantifier support',params:[],inputs:['unused'],inputMaps:['S','extra'],state:{v:n(0)},maps:{A:0},
  step:{flags:{empty:{op:'all',key:'k',c:same(get('S',x('k')),n(0))}},
   state:{v:{op:'if',c:{op:'flag',name:'empty'},then:n(1),else:n(0)}}}}
 expect(requestQuotient(m,requests(m,2))!.reads.get(undefined)).toEqual(['S']);equivalent(m,2)
 const rs:Request[]=[{unused:0,S:new Map(),extra:new Map()},{unused:1,S:new Map(),extra:new Map([[1000000,1]])}]
 expect(requestQuotient(m,rs)!.count).toBe(1)
 const run=interpret(m),start=run.init({})
 expect(stateText(run.step({},start,rs[0]!))).toBe(stateText(run.step({},start,rs[1]!)))
})
test('unsupported functions, leasts, namespaces and forward flags retain the old sampler',()=>{
 const base=machine(),rs=requests(base)
 expect(requestQuotient({...base,fns:{f:{js:'x => x',lean:'id'}}},rs)).toBeUndefined()
 expect(requestQuotient({...base,leasts:{}},rs)).toBeUndefined()
 expect(requestQuotient({...base,params:['a']},rs)).toBeUndefined()
 expect(requestQuotient({...base,step:{flags:{first:{op:'flag',name:'second'},second:same(x('op'),n(1))},state:base.step.state}},rs)).toBeUndefined()
})
test('does not treat memoized count keys as complete quantified support',()=>{
 const base=machine(),m:Machine={...base,counts:{C:{j:'row',key:'cell',below:n(3),body:{op:'if',c:same(x('cell'),x('row')),then:n(1),else:n(0)}}},
  step:{flags:{allZero:{op:'all',key:'k',c:same(get('C',x('k')),n(0))}},state:{value:{op:'if',c:{op:'flag',name:'allZero'},then:n(1),else:n(0)}}}}
 expect(requestQuotient(m,requests(m))).toBeUndefined()
})
test('arithmetic and Boolean branch dependencies agree with every concrete successful member',()=>{
 for(const op of['add','sub','min','max','prod'] as const){
  const m=machine()
  m.step.state={value:{op:'if',c:{op:'flag',name:'first'},then:{op,a:x('a'),b:n(2)},else:x('value')}}
  equivalent(m)
 }
 for(const op of['and','or'] as const){
  const m=machine()
  m.step.flags!.first={op,xs:[same(x('op'),n(0)),same(x('a'),n(1))]}
  equivalent(m)
 }
})
test('one-cell and bulk map updates retain all concrete successor components',()=>{
 for(const bulk of[false,true]){
  const m=machine();m.inputMaps=['S'];m.maps={M:0}
  m.step.maps={M:bulk?{each:'k',value:{op:'if',c:{op:'flag',name:'first'},then:get('S',x('k')),else:n(1)}}:
   {key:x('a'),value:{op:'if',c:{op:'flag',name:'first'},then:get('S',x('a')),else:n(1)}}}
  equivalent(m,2)
 }
})
test.skipIf(!completeWorkProfile.enabled)('quotient setup checks the endpoint within 256 provisional tick units',()=>{
 const m=machine();m.inputMaps=['S','extra']
 const rs=requests(m)
 for(const budget of[0,1,255,256,1000]){
  const start=fullWork()
  expect(()=>withBudget(budget,()=>requestQuotient(m,rs))).toThrow(BudgetExpired)
  expect(fullWork()-start).toBeLessThanOrEqual(budget+256)
 }
})
test('logical prefixes remain equal across the native compiled-step threshold',()=>{
 const m=machine()
 m.step.state={value:{op:'if',c:{op:'flag',name:'first'},then:{op:'add',a:x('value'),b:x('a')},else:x('value')}}
 for(const work of[999,1000,1001,5000])for(const walks of[0,100]){
  const before=withQuotient(false,()=>small(m,{},3,128,work,walks).map(stateText))
  expect(withQuotient(true,()=>small(m,{},3,128,work,walks).map(stateText))).toEqual(before)
 }
})

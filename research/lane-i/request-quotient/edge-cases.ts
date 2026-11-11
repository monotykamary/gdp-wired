import {strict as a} from 'node:assert'
import {join} from 'node:path'
const root=process.argv[2]!
const {interpret,n,x,same,get}=await import(join(root,'core/machine.ts'))
const {requestQuotient}=await import(join(root,'core/request-quotient.ts'))
const base=():any=>({
 name:'selector/default regression',params:[],inputs:['op','a','unused'],state:{value:n(0)},
 step:{flags:{first:same(x('op'),n(0)),second:same(x('op'),n(1))},state:{value:n(0)}},
})
let selectorChecks=0,successorChecks=0,defaultChecks=0
for(const op of ['add','sub','min','max','prod'])for(let target=0;target<=14;target++){
 const m=base()
 m.step.flags.choose=same({op,a:x('op'),b:n(2)},n(target))
 m.step.state.value={op:'if',c:{op:'flag',name:'choose'},then:x('a'),else:n(0)}
 const requests=Array.from({length:7},(_,op)=>[0,1,2].flatMap(a=>[0,1].map(unused=>({op,a,unused})))).flat()
 const q=requestQuotient(m,requests);a(q);a.equal(q.selector,'op')
 const run=interpret(m),st=run.init({})
 for(let tag=0;tag<7;tag++){
  const actual=run.step({},st,{op:tag,a:1,unused:0}).scalars.value===1
  a.equal(q.reads.get(tag).includes('a'),actual,`${op} selector ${tag}, target ${target}`)
  selectorChecks++
 }
 const representatives=new Map<number,number>()
 for(let i=0;i<requests.length;i++){
  const cls=q.classes[i],value=run.step({},st,requests[i]).scalars.value
  if(representatives.has(cls))a.equal(value,representatives.get(cls));else representatives.set(cls,value)
  successorChecks++
 }
}
const canonical=(s:any)=>JSON.stringify({scalars:s.scalars,maps:Object.entries(s.maps).map(([name,cells]:any)=>{
 const d=s.defaults?.[name]??4
 return[name,d,[...cells].filter(([,v]:any)=>v!==d).sort((a:any,b:any)=>a[0]-b[0])]
})})
const sets=[new Map(),new Map([[0,1]]),new Map([[100,1]])]
const requests=[0,1].flatMap(op=>[0,1].flatMap(a=>[0,1].flatMap(unused=>sets.flatMap(S=>sets.map(extra=>({op,a,unused,S,extra}))))))
const values=[
 {op:'if',c:{op:'flag',name:'first'},then:get('S',x('k')),else:n(1)},
 {op:'if',c:{op:'<',a:x('k'),b:n(3)},then:x('a'),else:n(1)},
 get('S',{op:'add',a:x('k'),b:n(1)}),
]
for(let variant=0;variant<values.length;variant++){
 const m=base();m.inputMaps=['S','extra'];m.maps={M:4};m.step.maps={M:{each:'k',value:values[variant]}}
 const q=requestQuotient(m,requests);a(q)
 const run=interpret(m),st=run.init({}),representatives=new Map<number,string>()
 for(let i=0;i<requests.length;i++){
  const cls=q.classes[i],next=run.step({},st,requests[i]),text=canonical(next)
  if(variant===0&&requests[i]!.op===1){a.equal(next.defaults.M,1);defaultChecks++}
  if(variant===1){a.equal(next.defaults.M,1);defaultChecks++}
  if(variant===2){a.equal(next.defaults.M,0);defaultChecks++}
  if(representatives.has(cls))a.equal(text,representatives.get(cls),`bulk variant ${variant}`);else representatives.set(cls,text)
  successorChecks++
 }
}
console.log('QUOTIENT_EDGE_CASES '+JSON.stringify({selectorChecks,successorChecks,defaultChecks,ops:['add','sub','min','max','prod'],selectorValues:'0..6',targets:'0..14',bulkVariants:3,unreadSupportKeys:[0,100]}))

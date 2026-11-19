// Derive a filtered weighted-sum proposal from a guarded
// subtraction and the write cluster it refers to; never assume the proposal.
import {type C,type E,type Law,type Machine,get,n,same,walkOnce,x} from '../../core/machine.ts'
import {ghostedMachine,ghostedOk,substC,substE,sumMachine,type Ghosted} from '../../kernel/kernel.ts'

const text=(u:unknown)=>JSON.stringify(u)
const eq=(a:unknown,b:unknown)=>text(a)===text(b)
const flat=(op:'and'|'or', c:C):C[] => c.op===op ? c.xs.flatMap(t=>flat(op,t)) : [c]
const zero=n(0)
const sameKey=(t:E,k:E)=>eq(t,k)
const at=(t:E,nm:string)=>t.op==='var'&&t.name===nm
const isZero=(t:E,o?:number)=>t.op==='const'&&t.value===(o??0)
const and=(xs:C[]):C=>({op:'and',xs})
const ite=(c:C,then:E,otherwise:E):E=>({op:'if',c,then,else:otherwise})
const noSub={vars:{},maps:{},flags:{}}
type Read=Extract<E,{op:'get'}>
const termReads=(t:unknown)=>{const a:Read[]=[];walkOnce(t,o=>{const e=o as E;if(e.op==='get')a.push(e)});return a}
const points=(m:Machine,map:string)=>{const w=m.step.maps?.[map];return w&&!('each'in w)?w:undefined}
const labels=(m:Machine,c:C,matching:(r:Read)=>boolean,negated=false):[string,number][]=>{
  const r:[string,number][]=[]
  const pattern=(node:C)=>{
    if(node.op!=='=')return
    const t=node.a.op==='get'?node.a:node.b.op==='get'?node.b:undefined, v=t===node.a?node.b:node.a
    if(t&&v.op==='const'&&matching(t)&&Object.hasOwn(m.maps??{},t.map)&&m.maps![t.map]!==v.value) r.push([t.map,v.value])
  }
  if(!negated)walkOnce(c,o=>pattern(o as C))
  else walkOnce(c,o=>{const q=o as C;if(q.op==='not')pattern(q.x)})
  return r
}

export type WeightedCandidate={ghost:Ghosted,machine:Machine,laws:Law[],links:{balance:string,weight:string,group:string,gates:[string,number][],absence?:[string,number],point:E,events:string[]},observer:string}
export function weightedCandidates(m:Machine,law:Law):WeightedCandidate[] {
  if (!law.forall || law.keys?.length || law.some?.length || m.history || m.sums || m.counts || m.inputMaps?.length) return []
  const key=law.forall, ws=m.step.maps??{}, names=text([m,law]);let prefix='weight$';while(names.includes(prefix))prefix += 'a'
  const obs=`${prefix}observer`, binder=`${prefix}item`, wm=`${prefix}map`, sum=`${prefix}sum`, selected=x(obs)
  const o={...m,params:[...m.params,obs]}, res:WeightedCandidate[]=[]
  const ownFlags=Object.fromEntries(Object.keys(m.step.flags??{}).map(name=>[name,{op:'flag',name} as C]))
  for (const aMap of new Set(termReads(law.holds).filter(r=>at(r.key,key)).map(r=>r.map))) {
    const wr=ws[aMap], u=wr&&'each'in wr&&wr.value
    if(!u||u.op!=='if'||!isZero(u.then))continue
    const ix=(wr as {each:string}).each, delta=u.else
    if(delta.op!=='if'||!eq(delta.else,get(aMap,x(ix)))||delta.then.op!=='sub')continue
    const sub=delta.then
    if(sub.a.op!=='add'||!eq(sub.a.a,get(aMap,x(ix)))||sub.b.op!=='if'||!isZero(sub.b.else)||sub.b.then.op!=='get')continue
    const {map:weight,key:point}=sub.b.then, ww=points(m,weight)
    if(!ww||!m.maps||m.maps[aMap]!==0)continue
    // Structural role match: the accumulator's addressed guard equates its
    // own key to a foreign-key field of the same row as the removed weight.
    const groups=new Set<string>()
    walkOnce(delta.c,node=>{const c=node as C;if(c.op!=='=')return
      for(const [k,t] of [[c.a,c.b],[c.b,c.a]] as const) {
        if(at(k,ix)&&t.op==='get'&&sameKey(t.key,point)&&eq(points(m,t.map)?.key,ww.key))groups.add(t.map)
      }
    })
    if(groups.size!==1)continue
    const [group]=groups as Set<string>
    const aliases=point.op==='if'?[point.then,point.else]:[point]
    const guards=flat('or',sub.b.c).flatMap(c=>c.op==='flag'&&m.step.flags?.[c.name]?[m.step.flags[c.name]!]:[])
    if(!guards.length)continue
    const byGuard=guards.map(c=>labels(m,c,r=>aliases.some(k=>eq(k,r.key))&&!!points(m,r.map)))
    const gates=[...new Map(byGuard[0]!.filter(a=>byGuard.every(xs=>xs.some(b=>eq(a,b)))).map(t=>[text(t),t])).values()]
    if(!gates.length||gates.length>3||!gates.some(([name])=>eq(points(m,name)?.key,point)))continue
    const initGuards=flat('and',u.c), creating=initGuards.find(c=>c.op==='flag')
    const aRef=initGuards.find(c=>c.op==='='&&at(c.a,ix))
    const absent=creating?.op==='flag'&&aRef?.op==='='&&m.step.flags?.[creating.name] ?
      labels(m,m.step.flags[creating.name]!,r=>eq(r.key,aRef.b)&&!!ws[r.map]&&'each'in ws[r.map]!,true) : []
    const absence=absent.length===1?absent[0]:undefined
    const contribution=(read:(m:string)=>E)=>ite(and([...gates.map(([g,v])=>same(read(g),n(v))),same(read(group!),selected)]),read(weight),zero)
    const added=sub.a.b
    if(added.op!=='if'||!isZero(added.else))continue
    const groupSelected=substC(delta.c,{...noSub,flags:ownFlags,vars:{[ix]:selected}})
    // The delta must still agree with the complete post-row shape at every key.
    const value=ite(and([groupSelected,sub.b.c]),zero,ite(and([groupSelected,added.c]),added.then,get(wm,point)))
    const ghost={orig:o,vars:{},maps:{[wm]:{start:0,write:{key:point,value}}}}
    if(!ghostedOk(ghost))continue
    const instrumented=ghostedMachine(ghost)
    const machine={...instrumented,state:{...instrumented.state,[sum]:zero},sums:{[sum]:{term:get(wm,x(`${prefix}index`)),key:`${prefix}index`}}}
    try{sumMachine(machine)}catch{continue}
    const laws:Law[]=[
      ...(absence?[{name:`${prefix}absent storage is zero`, holds:{op:'or',xs:[same(get(absence[0],selected),n(absence[1])),same(get(aMap,selected),zero)]} as C}]:[]),
      {name:`${prefix}point contribution`,forall:binder,holds:same(get(wm,x(binder)),contribution(name=>get(name,x(binder))))},
      {name:`${prefix}accumulator equals weighted live sum`,holds:same(get(aMap,selected),x(sum))},
      {name:law.name,holds:substC(law.holds,{...noSub,vars:{[key]:selected}})},
    ]
    const eventNames=new Set<string>()
    walkOnce([u.c,sub.a.b,sub.b],node=>{const c=node as C;if(c.op==='flag')eventNames.add(c.name)})
    res.push({ghost,machine,laws,observer:obs,links:{balance:aMap,weight,group:group!,gates,absence,point,events:[...eventNames]}})
  }
  return res
}

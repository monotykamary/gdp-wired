// Existing-schema instances for the old/new decision comparison; no new axioms.
import {readFileSync} from 'node:fs'
import type {E} from '../../../core/machine.ts'
import type {Instances,CountInst,MapRead} from '../../../kernel/kernel.ts'
import {sha,type safetyContext} from './safety-context.ts'
type Context=ReturnType<typeof safetyContext>
const v=(name:string):E=>({op:'var',name}),n=(value:number):E=>({op:'const',value})
const pk=(a:E,b:E):E=>({op:'add',a:{op:'mul',k:64,a},b})
const same=(a:unknown,b:unknown)=>JSON.stringify(a)===JSON.stringify(b)
export function originalFocusInstances(c:Context):Instances{
  const bytes=readFileSync('research/egraph/historical/recovery/safety-focus-v6.json')
  if(sha(bytes)!=='4d7c5adf0d85dd3f32e42ad23b0e1ded8db9b928f44e044e4fd0ae4286891a14')throw Error('focus pin')
  const p=JSON.parse(bytes.toString()) as {keys:string[],candidates:{binding:Record<string,E>}[]}
  if(p.candidates.length!==24)throw Error('focus cap')
  return {...c.metadata.instances,[c.input.law.name]:[...c.metadata.instances[c.input.law.name]!,...p.candidates.flatMap(x=>p.keys.map(k=>x.binding[k]!))]}
}
export function directSafety(c:Context,original:Instances){
  const instances={...original},reads:MapRead[]=[...c.metadata.reads],insts:CountInst[]=[...c.metadata.insts]
  let addedLawTuples=0
  const instance=(prefix:string,arity:number,terms:E[])=>{
    const law=c.input.laws.find(l=>l.name.startsWith(prefix));if(!law||[law.forall,...(law.keys??[])].filter(Boolean).length!==arity)throw Error('law schema')
    const old=instances[law.name]??[]
    for(let i=0;i<old.length;i+=arity)if(same(old.slice(i,i+arity),terms))return
    instances[law.name]=[...old,...terms];addedLawTuples++
  }
  const read=(map:string,key:E,name:string):string=>{
    const old=reads.find(r=>r[1]===map&&same(r[2],key));if(old)return old[0]
    if(reads.some(r=>r[0]===name))throw Error('read collision')
    reads.push([name,map,key]);return name
  }
  const count=(terms:CountInst['terms'],unit:number,wit:string):CountInst=>{
    const below=v('size'),old=insts.find(i=>i.unit===unit&&same(i.terms,terms)&&same(i.below,below));if(old)return old
    if(insts.some(i=>i.wit===wit)||JSON.stringify([c.input.m,c.input.laws]).includes(JSON.stringify(wit)))throw Error('witness collision')
    const next={wit,below,terms,unit};insts.push(next);return next
  }
  const r=v('r'),value=v('v'),a=v('key$2#'),b=v('key$3'),d=v('key$4'),e=v('key$5')
  const votes=read('pubVotes',pk(r,value),'r$15'),blocked=read('pubBlocked',pk(r,value),'r$16')
  const members=read('members',n(0),'unusedMembers'),missing=read('missing',n(0),'unusedMissing')
  count([[1,members],[-1,missing],[-1,votes]],0,'w$directBridge')
  const pairs:[E,E,string,string][]=[[a,b,read('pubVotes',pk(a,b),'unusedOldVotes0'),read('pubBlocked',pk(a,b),'unusedBlocked0')],[d,e,read('pubVotes',pk(d,e),'unusedOldVotes1'),read('pubBlocked',pk(d,e),'unusedBlocked1')],[r,value,votes,blocked]]
  for(const [i,[round,val,vr,br]]of pairs.entries()){
    const positive=count([[1,vr]],0,`w$directVote${i}`)
    instance('P2 ',3,[v(positive.wit),round,val])
    count([[1,vr],[1,br]],-1,`w$directDisjoint${i}`)
  }
  instance('P1 ',3,[r,b,e])
  for(const [round,val]of [[a,b],[d,e]] as [E,E][]){instance('P5 ',4,[round,val,r,value]);instance('P5 ',4,[r,value,round,val])}
  if(24+addedLawTuples>32||insts.length>1000||reads.length-c.metadata.reads.length>2)throw Error('fixed proposal cap')
  return {instances,reads,insts,picks:c.metadata.picks,addedLawTuples,addedCountInstances:insts.length-c.metadata.insts.length}
}

// Untrusted recovery from an oversized counted goal. Each returned certificate
// is an ordinary counted proof, checked by the caller's existing kernel gate.
import {type E,type Law,type Machine,walkOnce,x} from './machine.ts'
import {type CountCert,type CountDecl,type Goal,type Instances,countedObligations,mcGoal} from '../kernel/kernel.ts'
import {clock,grow,pastWall} from '../kernel/prove.ts'
import {env} from './solver.ts'
import {countLawSeeds,countRowBridges,fieldGuardSeeds,fieldLawBridges,focusCountCert,rowKeyNames} from './count-focused.ts'
import {seedCountWitnessFlags} from './count-witness-flags.ts'
import {finiteCountChoice,proveCountCases} from './count-cases.ts'

export type FocusedCountProof={instances:Instances,certs:Record<string,CountCert>}
// Normal finite-input machines use the bounded recovery; 0 remains an explicit
// opt-out, while 1 also enables the legacy non-finite recovery experiment.
export const focusedCountRecoveryEnabled=(m:Machine,setting:string|undefined=env.GDP_COUNTS_FOCUS):boolean=>setting==='1'||setting!=='0'&&!!finiteCountChoice(m)
export function proveFocusedCounts(m:Machine,laws:Law[],law:Law,at:Instances,until:number,propose:(goal:Goal,decls:CountDecl[])=>Pick<CountCert,'reads'|'insts'>,trace?:(event:Record<string,unknown>)=>void):FocusedCountProof|undefined {
  if(clock()>=until||pastWall()||!m.inputMaps?.length)return undefined
  let clean:Instances={}
  for(const [name,terms] of Object.entries(at)){
    const l=laws.find(l=>l.name===name),arity=l?1+(l.keys?.length??0):1,keep:E[]=[]
    for(let i=0;i<terms.length;i+=arity){
      const tuple=terms.slice(i,i+arity);let witness=false
      walkOnce(tuple,(o:any)=>{if(o.op==='var'&&/^w(?:\$\d+|\?)/.test(o.name))witness=true})
      if(!witness)keep.push(...tuple)
    }
    clean[name]=keep
  }
  if(law.forall){
    const tuple=[x(`${law.forall}#`),...(law.keys??[]).map(x)],had=clean[law.name]??[],arity=tuple.length
    if(!Array.from({length:Math.floor(had.length/arity)},(_,i)=>JSON.stringify(had.slice(i*arity,(i+1)*arity))).includes(JSON.stringify(tuple)))clean[law.name]=[...had,...tuple]
  }
  const names=[law.forall,...law.keys??[]],own=names.filter((n):n is string=>!!n).map((n,i)=>x(i===0?`${n}#`:n)),scalar=rowKeyNames(m,law)
  let targetCounts=false
  walkOnce(law.holds,(o:any)=>{if(o.op==='get'){if(o.key.op==='var')scalar.add(o.key.name);if(m.counts?.[o.map])targetCounts=true}})
  const rows=own.filter((_,i)=>scalar.has(names[i]!)),request=m.inputs.filter(name=>Object.values(m.counts??{}).some(d=>![d.j,d.lo,d.key].includes(name)&&JSON.stringify([d.below,d.body]).includes(`"name":${JSON.stringify(name)}`))).map(x)
  const bridgeLaws=targetCounts?laws.filter(l=>(l.keys?.length??0)===0):laws
  clean=countLawSeeds(m,laws,clean,rows.length?rows:own,request,!targetCounts,{requestDiagonals:true})
  clean=fieldLawBridges(m,bridgeLaws,clean,rows.length?rows:own,request,own.length===3?own[2]:undefined)
  clean=countRowBridges(m,law,clean,own,request)
  if(!targetCounts)clean=fieldGuardSeeds(m,clean,[...rows,...request,{op:'const',value:0}])
  const index=laws.findIndex(l=>l.name===law.name)
  for(const carried of [undefined,...m.inputMaps]){
    if(clock()>=until||pastWall())return undefined
    let instances=clean
    const retained=new Map<string,Pick<CountCert,'reads'|'insts'>>()
    const proposal=(goal:Goal,decls:CountDecl[])=>focusCountCert(m,decls,propose(goal,decls),{carried,structural:false,frames:true,algebraic:true,requestFrames:true,copyFrames:true,targets:!targetCounts?rows:undefined,claim:goal.hyps.at(-1)})
    const packetsByInstances=new Map<string,{goal:Goal,decls:CountDecl[],cert:Pick<CountCert,'reads'|'insts'>}[]>()
    const build=()=>{
      const key=JSON.stringify(instances),had=packetsByInstances.get(key)
      if(had)return had
      const packets=countedObligations(m,laws,{[law.name]:instances},index).map(({goal,decls})=>({goal,decls,cert:retained.get(goal.name)??proposal(goal,decls)}))
      packetsByInstances.set(key,packets);return packets
    }
    let packets=build()
    const seeded=seedCountWitnessFlags(m,instances,packets,true)
    if(seeded!==instances){instances=seeded;packets=build()}
    const rowGoal=!targetCounts&&own.length===3
    const certs:Record<string,CountCert>={};let complete=!rowGoal&&!finiteCountChoice(m)
    const quickUntil=Math.min(until,clock()+1000)
    for(const {goal,decls,cert} of rowGoal||finiteCountChoice(m)?[]:packets){
      const g=mcGoal(goal.hyps,decls,cert)
      if(!g){complete=false;break}
      const result=grow({...g,name:goal.name},new Map(),{nodes:0,until:quickUntil})
      if(!('tree'in result)){complete=false;break}
      certs[goal.name]={...cert,tree:result.tree}
    }
    if(complete)return {instances,certs}
    if(clock()>=until||pastWall())continue
    let cold:Instances={}
    cold=countLawSeeds(m,laws,cold,rows.length?rows:own,request,!targetCounts,{requestDiagonals:true})
    cold=fieldLawBridges(m,bridgeLaws,cold,rows.length?rows:own,request,own.length===3?own[2]:undefined)
    if(law.forall)cold[law.name]=[...cold[law.name]??[],...own]
    cold=countRowBridges(m,law,cold,own,request)
    if(!targetCounts)cold=fieldGuardSeeds(m,cold,[...rows,...request,{op:'const',value:0}])
    instances=cold;packets=build()
    const flags=seedCountWitnessFlags(m,instances,packets,true)
    if(flags!==instances){instances=flags;packets=build()}
    const step=packets.find(p=>p.goal.name.endsWith('@step'))
    if(!step)continue
    trace?.({stage:'focused-packet',carried:carried??null,hyps:step.goal.hyps.length,insts:step.cert.insts.length,reads:step.cert.reads.length,instances:Object.fromEntries(Object.entries(instances).map(([name,terms])=>[name,terms.length]))})
    const result=proveCountCases(m,laws,instances,step.cert,until,next=>{
      instances=next
      return build().find(p=>p.goal.name.endsWith('@step'))!
    },{propose:proposal,saturate:true,queryMs:200,trace,...(!targetCounts&&own.length===3?{localModels:true,coreLimit:16,units:false,corePointOnly:true}:{})})
    if(!result)continue
    instances=result.instances;retained.set(step.goal.name,result.cert);packetsByInstances.clear();packets=build()
    trace?.({stage:'focused-step-certificate',before:step.cert.insts.length,after:result.cert.insts.length})
    const combined:Record<string,CountCert>={[step.goal.name]:result.cert}
    let closed=true
    for(const p of packets){
      if(p.goal.name===step.goal.name)continue
      const g=mcGoal(p.goal.hyps,p.decls,p.cert),out=g&&grow({...g,name:p.goal.name},new Map(),{nodes:0,until})
      if(!out||!('tree'in out)){closed=false;break}
      combined[p.goal.name]={...p.cert,tree:out.tree}
    }
    if(closed)return {instances,certs:combined}
  }
  return undefined
}

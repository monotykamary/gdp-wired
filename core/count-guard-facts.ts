// Generic ordinary guard-restricted count facts for optional proof strategies.
// Every result is an ordinary checkMC/check proof under its explicitly recorded
// conditions; a proposal is never added to the original goal as an axiom.
import {type C,type E,atMost,get,n,not,same,walkOnce} from './machine.ts'
import {countsForReads} from './count-facts.ts'
import {type CountCert,type CountDecl,type Goal,type LinCut,type MapRead,type Tree,check,checkMC,linOk,mcGoal} from '../kernel/kernel.ts'
import {brokenOf,clock,grow,pastWall} from '../kernel/prove.ts'
export type GuardCountProposal={name:string,kind:string,when:C[],terms:[number,string][]}
export type CheckedGuardCountFact={proposal:GuardCountProposal,claim:C,goal:Goal,cert:CountCert}
export type CheckedGuardLinearFact={proposal:GuardCountProposal,goal:Goal,cut:LinCut}
export type GuardCountTrace={outcome:string,encoded?:Goal,witness?:Record<string,number>,broken?:unknown,searchEnd?:number}
export type GuardBodyProposal={name:string,kind:'excluded-body-frame',when:C[],pre:E,post:E}
export type CheckedGuardBodyFact={proposal:GuardBodyProposal,goal:Goal,tree:Tree}
const mentions=(t:E|C,key:string)=>{let found=false;walkOnce(t,(v:any)=>{if(v.op==='var'&&v.name===key)found=true});return found}
export function guardCountFact(premises:C[],decls:CountDecl[],reads:MapRead[],proposal:GuardCountProposal,wit:string,until:number,observe?:(trace:GuardCountTrace)=>void):CheckedGuardCountFact|undefined{
 if(pastWall()||clock()>=until||!proposal.terms.length||proposal.when.some(c=>mentions(c,wit)))return
 const counts=countsForReads(decls,reads),terms=proposal.terms
 if(!counts||new Set(terms.map(t=>t[1])).size!==terms.length)return
 const first=counts.find(c=>c.v===terms[0]![1]);if(!first)return
 let positive:E=n(0),negative:E=n(0)
 for(const [coefficient,name]of terms){
  if(!Number.isSafeInteger(coefficient)||!coefficient)return
  const read=reads.find(r=>r[0]===name),count=counts.find(c=>c.v===name)
  if(!read||!count||JSON.stringify(count.below)!==JSON.stringify(first.below))return
  const value:E={op:'mul',k:Math.abs(coefficient),a:get(read[1],read[2])}
  if(coefficient>0)positive={op:'add',a:positive,b:value};else negative={op:'add',a:negative,b:value}
 }
 const claim=atMost(positive,negative),goal:Goal={name:proposal.name,hyps:[...premises,...proposal.when,not(claim)]}
 const request={reads,insts:[{wit,below:first.below,terms,unit:0}],picks:[]},encoded=mcGoal(goal.hyps,decls,request)
 if(!encoded){observe?.({outcome:'invalid-encoding'});return}
 const result=grow(encoded,new Map(),{nodes:0,until})
 if(!('tree'in result)){
  const witness='witness'in result?result.witness:undefined,broken=witness?brokenOf(encoded)(witness):undefined
  if(witness&&broken?.length)throw Error('invalid auxiliary witness')
  observe?.({outcome:result.stuck,encoded,witness,broken});return
 }
 const cert={...request,tree:result.tree},checked=checkMC(goal.hyps,decls,cert)
 observe?.({outcome:checked?'proof':'rejected-proof',encoded})
 return checked?{proposal,claim,goal,cert}:undefined
}
export function guardLinearFact(decls:CountDecl[],reads:MapRead[],proposal:GuardCountProposal,until:number,observe?:(trace:GuardCountTrace)=>void):CheckedGuardLinearFact|undefined{
 if(pastWall()||clock()>=until||!proposal.terms.length)return
 const counts=countsForReads(decls,reads);if(!counts)return
 const pos:[number,string][]=[],neg:[number,string][]=[]
 for(const [coefficient,name]of proposal.terms){
  if(!Number.isSafeInteger(coefficient)||!coefficient||!counts.some(c=>c.v===name))return
  if(coefficient>0)pos.push([coefficient,name]);else neg.push([-coefficient,name])
 }
 const first=counts.find(c=>c.v===proposal.terms[0]![1])!
 if(counts.filter(c=>proposal.terms.some(t=>t[1]===c.v)).some(c=>c.key!==first.key||JSON.stringify(c.below)!==JSON.stringify(first.below)))return
 const term=(side:[number,string][]):E=>side.reduceRight<E>((rest,[k,name])=>({op:'add',a:{op:'mul',k,a:counts.find(c=>c.v===name)!.body},b:rest}),n(0))
 const goal:Goal={name:proposal.name,hyps:[...proposal.when,{op:'<',a:{op:'var',name:first.key},b:first.below},{op:'<',a:term(neg),b:term(pos)}]}
 const result=grow(goal,new Map(),{nodes:0,until}),searchEnd=clock()
 if(searchEnd>=until){observe?.({outcome:'deadline',encoded:goal,searchEnd});return}
 if(!('tree'in result)){
  const witness='witness'in result?result.witness:undefined,broken=witness?brokenOf(goal)(witness):undefined
  if(witness&&broken?.length)throw Error('invalid linear auxiliary witness')
  observe?.({outcome:result.stuck,encoded:goal,witness,broken,searchEnd});return
 }
 const cut:LinCut={when:proposal.when,pos,neg,tree:result.tree},checked=linOk(counts,cut)
 observe?.({outcome:checked?'proof':'rejected-proof',encoded:goal,searchEnd})
 return checked?{proposal,goal,cut}:undefined
}

export function guardBodyFact(proposal:GuardBodyProposal,until:number):CheckedGuardBodyFact|undefined{
 if(pastWall()||clock()>=until)return
 const goal:Goal={name:proposal.name,hyps:[...proposal.when,not(same(proposal.pre,proposal.post))]}
 const result=grow(goal,new Map(),{nodes:0,until})
 return 'tree'in result&&check(goal,result.tree)?{proposal,goal,tree:result.tree}:undefined
}

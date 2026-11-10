// Proposal inspection only: no new premise is asserted and no proof is accepted.
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {termColumn} from '../../kernel/kernel.ts'
import {memberInclusions} from '../../core/count-recovery/member-inclusions.ts'
import {admitMemberWitnesses,memberPremiseState} from '../../core/count-recovery/member-premises.ts'
const p=JSON.parse(gunzipSync(readFileSync(process.argv[2]!)).toString()),name=process.argv[3]
for(const [i,t]of p.columns.entries())if(termColumn(t)!==`⟦${i}⟧`)throw Error('column map mismatch')
const queries=p.captures.filter((c:any)=>c.pass===1&&c.phase==='query'&&c.goal?.endsWith('@step'))
for(const [position,c]of [['first',queries[0]],['last',queries.at(-1)]] as const){
 if(!c)continue
 const cert=c.certificateRequest,byId=new Map<string,any>(cert.reads.map((r:any)=>[r[0],r])),proposals=memberInclusions(p.m,c.decls,cert.reads),admitted=admitMemberWitnesses(p.m,c.decls,cert,memberPremiseState([p.m,p.laws]),10)
 const show=(q:any)=>({positive:byId.get(q.positive)?.slice(1),negative:byId.get(q.negative)?.slice(1),guards:q.guards})
 const d=p.m.counts['inX$canVote$3'],probeReads=[['probeS','inS',{op:'const',value:0}],['probeB','inX$canVote$3',{op:'add',a:{op:'mul',k:d.base,a:{op:'var',name:'i'}},b:{op:'var',name:'b$field'}}]]
 const hypothetical=memberInclusions(p.m,c.decls,probeReads as any)
 console.log(JSON.stringify({name,position,hyps:c.hyps.length,seedCount:c.seedCount,readCount:cert.reads.length,existingInstances:cert.insts.length,proposals:proposals.length,admitted:admitted.hints.length,examples:proposals.slice(0,12).map(show),hypotheticalActorPair: {proposalCount:hypothetical.length,guards:hypothetical.map(q=>q.guards)}}))
}

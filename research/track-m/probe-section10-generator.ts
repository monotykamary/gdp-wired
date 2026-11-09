// Fixture-only census of the generic proposer, before source search.
import {readFileSync} from 'node:fs'
import {type Law,type Machine,x,walkOnce} from '../../core/machine.ts'
import {countedObligations} from '../../kernel/kernel.ts'
import {certFor} from '../../core/counts.ts'
import {countLawSeeds,countRowBridges,fieldLawBridges,focusCountCert,rowKeyNames} from '../../core/count-focused.ts'
import {memberInclusions} from '../../core/count-recovery/member-inclusions.ts'
const {m,laws}=JSON.parse(readFileSync(process.argv[2]!,'utf8')) as {m:Machine,laws:Law[]}
for(const prefix of ['Inv*','Inv2973']){
 const index=laws.findIndex(l=>l.name.startsWith(prefix)),law=laws[index]!,names=[law.forall,...law.keys??[]],own=names.map((name,i)=>x(i?name!:`${name}#`)),scalar=rowKeyNames(m,law)
 let targetCounts=false;walkOnce(law.holds,(o:any)=>{if(o.op==='get'){if(o.key.op==='var')scalar.add(o.key.name);if(m.counts?.[o.map])targetCounts=true}})
 const rows=own.filter((_,i)=>scalar.has(names[i]!)),request=m.inputs.filter(name=>Object.values(m.counts??{}).some(d=>![d.j,d.lo,d.key].includes(name)&&JSON.stringify([d.below,d.body]).includes(`"name":${JSON.stringify(name)}`))).map(x)
 let at=countLawSeeds(m,laws,{},rows.length?rows:own,request,!targetCounts,{requestDiagonals:true})
 at=fieldLawBridges(m,targetCounts?laws.filter(l=>(l.keys?.length??0)===0):laws,at,rows.length?rows:own,request,own.length===3?own[2]:undefined)
 if(law.forall)at[law.name]=[...at[law.name]??[],...own]
 at=countRowBridges(m,law,at,own,request)
 const p=countedObligations(m,laws,{[law.name]:at},index).find(p=>p.goal.name.endsWith('@step'))!,full=certFor(p.goal,p.decls,true,1000),focused=focusCountCert(m,p.decls,full,{structural:false,frames:true,algebraic:true,requestFrames:true,copyFrames:true,claim:p.goal.hyps.at(-1)}),proposals=memberInclusions(m,p.decls,focused.reads)
 const found=focused.insts.filter(q=>proposals.some(p=>JSON.stringify(q.terms)===JSON.stringify([[1,p.positive],[-1,p.negative]])))
 console.log(JSON.stringify({test:'section10-generator',law:law.name,reads:focused.reads,proposals,emitted:found,pool:focused.insts.length}))
 if(prefix==='Inv*'&&!found.some(q=>JSON.stringify(q.terms)===JSON.stringify([[1,'r$4'],[-1,'r$16']])))throw new Error('expected captured inclusion was not emitted')
}

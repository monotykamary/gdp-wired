// Repackage retained, already-proved requests. No grow/search call belongs here.
import {readFileSync,mkdirSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import type {E,Law,Machine} from '../../core/machine.ts'
import {countedObligations,mcGoal,type CountCert,type Instances} from '../../kernel/kernel.ts'
const root='runs/track-p-gap-source',dest='runs/track-p-certs'
const text=(path:string)=>readFileSync(path,'utf8')
const fixture=JSON.parse(text(root+'/fixture.json')) as {machine:Machine,laws:Law[]}
const {machine:m,laws}=fixture,ids=[2,3,4,7,9,10,11,13,14,17,33,45,61,64,66,70,71,73,74]
const v=(name:string):E=>({op:'var',name}),n=(value:number):E=>({op:'const',value})
const jsonLines=(path:string)=>text(path).split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l) as {name:string,tree:CountCert['tree']})
const c9=jsonLines(root+'/probes-v2-run/c9.log').find(r=>r.name==='c9/1')!
if(!c9?.tree)throw Error('missing retained C9 tree')
const own=laws[9]!,at:Instances={[own.name]:[v('a$c')]}
const c9ob=countedObligations(m,[own],{[own.name]:at},0)[1]!
const c9cert:CountCert={reads:[['old','members$Qs',v('a$c')],['post','members$Qs#',v('a$c#')],['incoming','members',n(0)]],insts:[{wit:'wOld',below:v('size'),terms:[[1,'old'],[-1,'post']],unit:0},{wit:'wIncoming',below:v('size'),terms:[[1,'incoming'],[-1,'post']],unit:0}],picks:[],tree:c9.tree}
const alt=text(root+'/alternate-run/alternate.log').split('\n'),c11=JSON.parse(alt.find(l=>l.startsWith('{'))!) as {tree:CountCert['tree']}
const req=JSON.parse(alt.find(l=>l.startsWith('REQUEST '))!.slice(8)) as {instances:Instances,cert:CountCert,hyps:unknown}
const c11ob=countedObligations(m,ids.map(i=>laws[i]!),{[laws[11]!.name]:req.instances},ids.indexOf(11))[1]!
if(JSON.stringify(c11ob.goal.hyps)!==JSON.stringify(req.hyps))throw Error('C11 request is not source-bound')
const records=[{id:'c9',scope:'C9_ORIGINAL_OWN_PRE_STEP_RETAINED_17',ob:c9ob,cert:c9cert,instances:at,familyIndices:[9]},{id:'c11',scope:'C11_ORIGINAL19_STEP_RETAINED_32',ob:c11ob,cert:{...req.cert,tree:c11.tree},instances:req.instances,familyIndices:ids}]
for(const r of records){
 const gg=mcGoal(r.ob.goal.hyps,r.ob.decls,r.cert);if(!gg)throw Error('cannot encode '+r.id)
 mkdirSync(dest+'/'+r.id,{recursive:true})
 for(const [file,value]of [['goal.json',{scope:r.scope,raw:r.ob.goal,decls:r.ob.decls,gg}],['proof.json',r.cert],['source.json',{fixtureSHA256:createHash('sha256').update(text(root+'/fixture.json')).digest('hex'),familyIndices:r.familyIndices,instances:r.instances}]] as const)writeFileSync(dest+'/'+r.id+'/'+file,JSON.stringify(value)+'\n')
 console.log(JSON.stringify({id:r.id,rawHyps:r.ob.goal.hyps.length,encodedHyps:gg.hyps.length,decls:r.ob.decls.length,paths:['goal.json','proof.json'].map(f=>dest+'/'+r.id+'/'+f)}))
}

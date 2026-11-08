import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {auditSupport} from '../audit-support.ts';
import {candidateWork,prepareSupport,sparseReadInstances,keyId} from '../../../core/count-support.ts';
import {countedObligations,mcGoal} from '../../../kernel/kernel.ts';
const load=(s:string)=>JSON.parse(readFileSync(s,'utf8')),root='research/track-p/thirtythree/evidence/';
const f=load('research/track-p/input/family.json'),source=load(root+'source.json'),cert=load(root+'proof.json'),m=f.machine,laws=source.familyIndices.map((i:number)=>f.laws[i]),own=f.laws[33];
function emit(file:string,value:any){const text=JSON.stringify(value);for(let p=0;p<text.length;p+=10000)console.log('PART '+JSON.stringify({file,part:p/10000,data:text.slice(p,p+10000)}));}
const required=Object.entries(source.instances).flatMap(([name,vs]:any)=>{const l=laws.find((l:any)=>l.name===name),width=1+(l?.keys?.length??0);return Array.from({length:vs.length/width},(_,i)=>({name,tuple:vs.slice(i*width,(i+1)*width)}));});
const id=(r:any)=>JSON.stringify([r.name,r.tuple.map(keyId)]),needed=new Set(required.map(id));
for(const flags of ['all','none'] as const){
const generic=auditSupport(m,laws,own,source.instances,cert,flags);delete (generic as any).phaseMs;emit('audit-generic-'+flags+'.json',generic);console.log('SUMMARY '+JSON.stringify({mode:'generic',flags,required:generic.required,rounds:generic.trace.map((t:any)=>({phase:t.phase,emitted:t.emitted,missing:t.missing.length,extras:t.extras.length})),insts:generic.finalCert.insts.length,generationWork:generic.generationWork}));
const budget=candidateWork(),V=(name:string)=>({op:'var',name}),terms=[V(own.forall+'#'),...own.keys.map(V),...m.inputs.map(V)],initial=flags==='all'?Object.fromEntries(Object.entries(m.step.flags).filter(([,q]:any)=>q.op==='all'&&!q.keys?.length).map(([f])=>['?'+f,terms])):{};
const prep=prepareSupport(m,laws,own,initial,1,budget);let at=prep.at,admitted=prep.seedCount;const trace:any[]=[];const seen=new Map<string,string>();
function snapshot(phase:string){const rows=Object.entries(at).flatMap(([name,vs]:any)=>{const l=laws.find((l:any)=>l.name===name),width=name.startsWith('?')?1:1+(l?.keys?.length??0);return Array.from({length:vs.length/width},(_,i)=>({name,tuple:vs.slice(i*width,(i+1)*width)}));});for(const r of rows)if(needed.has(id(r))&&!seen.has(id(r)))seen.set(id(r),phase);const present=new Set(rows.map(id));trace.push({phase,emitted:rows.length,missing:required.filter(r=>!present.has(id(r))),extras:rows.filter(r=>!needed.has(id(r)))});}
snapshot('prepare');for(let round=0;round<6;round++){const {goal,decls}=countedObligations(m,laws,{[own.name]:at},laws.indexOf(own))[1]!;const gg=mcGoal(goal.hyps,decls,cert);if(!gg)throw Error('hand cert rejected');const next=sparseReadInstances(m,laws,own,at,gg,cert,64-admitted,goal.hyps.at(-1),decls,prep.sourceMaps,goal.hyps.slice(0,-1),budget);at=next.at;admitted+=next.added.length;snapshot('closure:'+round);if(!next.added.length||budget.state.exhausted)break;}
const result={mode:'hand',flags,required:required.map(r=>({...r,firstSeen:seen.get(id(r))??null})),trace,finalInstances:at,finalCert:{reads:cert.reads,insts:cert.insts,picks:cert.picks},generationWork:budget.state};emit('audit-hand-'+flags+'.json',result);console.log('SUMMARY '+JSON.stringify({...result,trace:trace.map(t=>({phase:t.phase,emitted:t.emitted,missing:t.missing.length,extras:t.extras.length})),finalInstances:undefined}));
}
emit('audit-hashes.json',{supportSHA256:createHash('sha256').update(readFileSync('core/count-support.ts')).digest('hex'),helperSHA256:createHash('sha256').update(readFileSync('research/track-p/audit-support.ts')).digest('hex')});

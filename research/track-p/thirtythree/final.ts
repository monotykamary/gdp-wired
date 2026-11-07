import {readFileSync} from 'node:fs';
import {countedObligations,mcGoal,checkMC} from '../../../kernel/kernel.ts';
import {grow,widen,clock,withWall,withDeadline,counted,fullRate} from '../../../kernel/prove.ts';
const load=(s:string)=>JSON.parse(readFileSync(s,'utf8')),root='research/track-p/thirtythree/evidence/';
const f=load('research/track-p/input/family.json'),original=load('research/track-p/thirtythree/original/fixture.json'),s=load(root+'source.json'),g=load(root+'goal.json'),p=load(root+'proof.json'),laws=s.familyIndices.map((i:number)=>f.laws[i]),own=f.laws[33];
if(JSON.stringify(original)!==JSON.stringify(f))throw Error('original fixture differs');console.log('ORIGINAL '+JSON.stringify({same:true,source:sourcePath(),scope:g.scope}));function sourcePath(){return 'runs/track-p-gap-source/fixture.json';}
function emit(file:string,value:any){const text=JSON.stringify(value);for(let p=0;p<text.length;p+=10000)console.log('PART '+JSON.stringify({file,part:p/10000,data:text.slice(p,p+10000)}));}
const results:any[]=[],ledgers:any[]=[];
for(const mode of ['generic-all','generic-none','hand-all','hand-none']){const audit=load(root+'audit-'+mode+'.json');
const {goal,decls}=countedObligations(f.machine,laws,{[own.name]:audit.finalInstances},laws.indexOf(own))[1]!;const cert=audit.finalCert,gg=mcGoal(goal.hyps,decls,cert)!;
const out=withWall(performance.now()+2500,()=>counted(fullRate,()=>withDeadline(clock()+1500,()=>grow(gg,new Map(),{nodes:0,until:clock()+1500})),true));
const directChecked='tree'in out&&checkMC(goal.hyps,decls,{...cert,tree:out.tree});
const extended=withWall(performance.now()+2500,()=>counted(fullRate,()=>withDeadline(clock()+1500,()=>widen(g.gg,gg,p.tree)),true));const liftedChecked=!!extended&&checkMC(goal.hyps,decls,{...cert,tree:extended});
const result={mode,rawHyps:goal.hyps.length,encodedHyps:gg.hyps.length,reads:cert.reads.length,insts:cert.insts.length,direct:'tree'in out?'tree':out.stuck,directChecked,liftedChecked,...('tree'in out?{}:{why:out.why})};results.push(result);console.log('RESULT '+JSON.stringify(result));
const index=(name:string)=>s.familyIndices[laws.findIndex((l:any)=>l.name===name)]??null;
ledgers.push({mode,required:audit.required.map((r:any)=>({index:index(r.name),...r})),rounds:audit.trace.map((t:any)=>({phase:t.phase,emitted:t.emitted,extras:t.extras.map((r:any)=>({index:index(r.name),...r})),missing:t.missing.map((r:any)=>({index:index(r.name),...r})),insts:t.insts??cert.insts,reads:t.reads??cert.reads})),final:result});
}
emit('final-validation.json',{originalSourceMatches:true,results});emit('emission-diff.json',{normalization:'keyId affine normalization; selected witness names normalized by instId in auditSupport; hand cert has no witnesses',ledgers});

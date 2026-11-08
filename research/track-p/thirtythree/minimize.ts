import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {countedObligations,mcGoal,checkMC} from '../../../kernel/kernel.ts';
import {grow,clock,withWall,withDeadline,counted,fullRate} from '../../../kernel/prove.ts';
const bytes=readFileSync('research/track-p/input/family.json','utf8'),{machine:m,laws}=JSON.parse(bytes);
const ids=[2,3,4,7,9,10,11,13,14,17,33,45,61,64,66,70,71,73,74],family=ids.map(i=>laws[i]),own=laws[33];
const V=(name:string):any=>({op:'var',name}),A=(a:any,b:any):any=>({op:'add',a,b}),M=(k:number,a:any):any=>({op:'mul',k,a});
const a=V('key1$enum#'),b=V('key2$enum'),c=V('key3$enum');
const rows=[{i:33,t:[a,b,c]},{i:61,t:[b]},{i:61,t:[c]},{i:3,t:[A(M(64,a),b)]},{i:3,t:[A(M(64,a),c)]}];
function emit(file:string,value:any){const text=JSON.stringify(value);for(let p=0;p<text.length;p+=10000)console.log('PART '+JSON.stringify({file,part:p/10000,data:text.slice(p,p+10000)}));}
let kept=rows;
const tests:any[]=[];
function run(name:string,rs:typeof rows,save=false){const at:any={};for(const r of rs)(at[laws[r.i].name]??=[]).push(...r.t);
const {goal,decls}=countedObligations(m,family,{[own.name]:at},ids.indexOf(33))[1]!;const cert:any={reads:[],insts:[],picks:[]};const gg=mcGoal(goal.hyps,decls,cert)!;
const out=withWall(performance.now()+2500,()=>counted(fullRate,()=>withDeadline(clock()+1500,()=>grow(gg,new Map(),{nodes:0,until:clock()+1500})),true));
const checked='tree'in out&&checkMC(goal.hyps,decls,{...cert,tree:out.tree});const result={name,rows:rs,checked,hyps:gg.hyps.length,...('tree'in out?{}:out)};tests.push(result);console.log('RESULT '+JSON.stringify(result));
if(checked&&save){emit('goal.json',{scope:'C33_ORIGINAL_FAMILY19_STEP_MINIMAL',raw:goal,decls,gg});emit('proof.json',{...cert,tree:out.tree});emit('source.json',{fixtureSHA256:createHash('sha256').update(bytes).digest('hex'),fixturePath:'runs/track-p-gap-source/fixture.json',familyIndices:ids,targetIndex:33,instances:at});}return checked;}
for(let j=0;j<rows.length;j++){const trial=kept.filter(r=>r!==rows[j]);if(run('drop-'+j,trial))kept=trial;}
if(!run('final',kept,true))throw Error('final request rejected');emit('minimization.json',{method:'greedy deletion; 1500 counted ms and 2500 wall cap per request; unchanged machine/family assumptions',tests,remainingRows:kept});

import {readFileSync} from 'node:fs';
import {countedObligations,mcGoal,checkMC} from '../../../kernel/kernel.ts';
import {grow,clock,withWall,withDeadline,counted,fullRate} from '../../../kernel/prove.ts';
const {machine:m,laws}=JSON.parse(readFileSync('research/track-p/input/family.json','utf8'));
const ids=[2,3,4,7,9,10,11,13,14,17,33,45,61,64,66,70,71,73,74],family=ids.map(i=>laws[i]),own=laws[33];
const V=(name:string):any=>({op:'var',name}),A=(a:any,b:any):any=>({op:'add',a,b}),M=(k:number,a:any):any=>({op:'mul',k,a});
const a=V('key1$enum#'),b=V('key2$enum'),c=V('key3$enum');
const base:any={[own.name]:[a,b,c],[laws[61].name]:[b,c]};
for(const [name,at] of [['minimal3',base],['kind5',{...base,[laws[3].name]:[A(M(64,a),b),A(M(64,a),c)]}],['no-own',{[laws[61].name]:[b,c]}],['one-carry',{[own.name]:[a,b,c],[laws[61].name]:[b]}]] as any){
const {goal,decls}=countedObligations(m,family,{[own.name]:at},ids.indexOf(33))[1]!; const cert:any={reads:[],insts:[],picks:[]};const gg=mcGoal(goal.hyps,decls,cert)!;
const out=withWall(performance.now()+2500,()=>counted(fullRate,()=>withDeadline(clock()+1500,()=>grow(gg,new Map(),{nodes:0,until:clock()+1500})),true));
const checked='tree'in out&&checkMC(goal.hyps,decls,{...cert,tree:out.tree});console.log(JSON.stringify({name,checked,hyps:gg.hyps.length,...('tree'in out?{tree:out.tree}:out)}));
if(checked)for(const [file,value]of Object.entries({goal:{scope:'C33_ORIGINAL_FAMILY19_STEP_'+name,raw:goal,decls,gg},proof:{...cert,tree:out.tree},source:{fixturePath:'runs/track-p-gap-source/fixture.json',familyIndices:ids,targetIndex:33,instances:at}})){const text=JSON.stringify(value);for(let p=0;p<text.length;p+=10000)console.log('PART '+JSON.stringify({file:name+'/'+file+'.json',part:p/10000,data:text.slice(p,p+10000)}));}
}

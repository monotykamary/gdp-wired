import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {countedObligations,mcGoal,checkMC} from '../../../kernel/kernel.ts';
import {grow,clock,withWall,withDeadline,counted,fullRate} from '../../../kernel/prove.ts';
const bytes=readFileSync('research/track-p/input/family.json'),{machine:m,laws}=JSON.parse(bytes.toString());
const ids=[2,3,4,7,9,10,11,13,14,17,33,45,61,64,66,70,71,73,74],family=ids.map(i=>laws[i]),idx=Number(process.argv[2]),target=laws[idx];
const V=(name:string):any=>({op:'var',name}),K=(value:number):any=>({op:'const',value}),M=(k:number,a:any):any=>({op:'mul',k,a}),A=(a:any,b:any):any=>({op:'add',a,b});
const a=V('a$c#'),b=V('b$c'),key=A(M(64,a),b),oldKey=A(M(64,V('pmaxr')),V('pv')),incomingKey=A(M(64,V('maxr')),V('v'));
const count:any=idx===10?{reads:[['old','members$Decision',key],['post','members$Decision#',key],['incoming','members',K(0)],['missing','missing',K(0)]],insts:[{wit:'wOld',below:V('size'),terms:[[1,'old'],[-1,'post']],unit:0},{wit:'wIncoming',below:V('size'),terms:[[1,'incoming'],[-1,'missing'],[-1,'post']],unit:0}],picks:[]}:{reads:[],insts:[],picks:[]};
function run(at:any,label:string, c=count){const {goal:raw,decls}=countedObligations(m,family,{[target.name]:at},family.indexOf(target))[1]!;const gg=mcGoal(raw.hyps,decls,c);if(!gg){console.log('RESULT',JSON.stringify({idx,label,status:'rejected count'}));return;}
 const out=withWall(performance.now()+2500,()=>counted(fullRate,()=>withDeadline(clock()+1500,()=>grow(gg,new Map(),{nodes:0,until:clock()+1500})),true));
 const checked='tree'in out&&checkMC(raw.hyps,decls,{...c,tree:out.tree}); console.log('RESULT',JSON.stringify({idx,label,status:'tree'in out?'tree':out.stuck,checked,hyps:gg.hyps.length,...(!('tree'in out)?{why:out.why,witness:out.witness}:{})}));
 if(checked)return {raw,decls,gg,proof:{...c,tree:out.tree},at};}
const trials=idx===10?[{[target.name]:[a,b]}]:[{[laws[45].name]:[V('w'),V('maxr'),V('v')]},{[laws[45].name]:[V('w'),V('maxr'),V('v')],[laws[3].name]:[oldKey,incomingKey]}];
let result:any;for(let i=0;i<trials.length;i++){result=run(trials[i],'initial-'+i);if(result)break;}
if(result){let at=structuredClone(result.at);for(const name of Object.keys(at)){const law=laws.find((l:any)=>l.name===name),width=name.startsWith('?')?1:1+(law?.keys?.length??0);for(let pos=at[name].length-width;pos>=0;pos-=width){const next=structuredClone(at);next[name].splice(pos,width);if(!next[name].length)delete next[name];const candidate=run(next,'drop-'+ids[family.findIndex((l:any)=>l.name===name)]+'-'+pos);if(candidate){at=next;result=candidate;}}}
 for(let pos=result.proof.insts.length-1;pos>=0;pos--){const c={...result.proof,insts:result.proof.insts.filter((_:any,j:number)=>j!==pos)};const candidate=run(result.at,'drop-count-'+pos,c);if(candidate)result=candidate;}
 const scope={targetIndex:idx,phase:'step',familyIndices:ids,fixtureSHA256:createHash('sha256').update(bytes).digest('hex'),countedMs:1500,wallMs:2500};
 const files:any={'goal.json':{scope,raw:result.raw,decls:result.decls,gg:result.gg},'proof.json':result.proof,'source.json':{...scope,instances:result.at}};
 for(const [file,value]of Object.entries(files)){const text=JSON.stringify(value);for(let j=0;j<text.length;j+=7000)console.log('ARTIFACT',JSON.stringify({file,offset:j,text:text.slice(j,j+7000)}));}
 console.log('SAVED',JSON.stringify({idx,hyps:result.gg.hyps.length,at:result.at}));
}else process.exitCode=2;

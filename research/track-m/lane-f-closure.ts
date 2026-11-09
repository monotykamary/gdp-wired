// A direct frozen counted-goal closure, conditional on its existing hypotheses.
// Bypass activation allocation only in this diagnostic; never a full helper pass.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {canon,mcGoal,termColumn,type Path} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,withWall} from '../../kernel/prove.ts'
import {certFor} from '../../core/counts.ts'
import {focusCountCert} from '../../core/count-focused.ts'
import {finiteCountChoice} from '../../core/count-cases.ts'
import {deriveCountClosure} from '../../core/count-recovery/derivability-closure.ts'
import {checkConditionalProof} from '../../core/count-recovery/conditional-proof.ts'
import {rowPairs,writesReadState} from '../../core/count-recovery/row-cases.ts'
const [file,opText,out]=process.argv.slice(2),raw=readFileSync(file!,'utf8'),p=JSON.parse(raw),op=Number(opText)
for(const [i,t]of p.columns.entries())if(termColumn(t)!==`⟦${i}⟧`)throw Error('column restoration failed')
const choice=finiteCountChoice(p.m);if(!choice||!choice[1].has(op)||!out)throw Error('invalid operation')
const path:Path=new Map(),a={[choice[0]]:1,'1':-op},b={[choice[0]]:-1,'1':op};path.set(canon(a),{lin:a,holds:true});path.set(canon(b),{lin:b,holds:true})
const events:object[]=[],start=performance.now(),work=fullWork();let tree:any,cert:any,goal:any,error:string|undefined
try{withWall(start+7000,()=>counted(fullRate,()=>{
 const until=clock()+6000
 cert=focusCountCert(p.m,p.packet.decls,certFor(p.packet.goal,p.packet.decls,true,1000),{structural:false,frames:true,algebraic:true,requestFrames:true,copyFrames:true,claim:p.packet.goal.hyps.at(-1)})
 goal=mcGoal(p.packet.goal.hyps,p.packet.decls,cert);if(!goal)throw Error('invalid MC packet')
 tree=deriveCountClosure(p.m,p.packet.decls,goal,cert,path,until,events,{claim:p.packet.goal.hyps.at(-1),conditional:true})
},true))}catch(e){error=String(e)}
const searchUnits=(fullWork()-work)/fullRate,searchWallMs=performance.now()-start,checked=!!tree&&checkConditionalProof(goal,tree,path)
const record={conditional:true,directClosure:true,wholeHelper:false,law:p.lawName,op,packetSha256:createHash('sha256').update(raw).digest('hex'),searchUnits,searchWallMs,units:(fullWork()-work)/fullRate,wallMs:performance.now()-start,checked,error,reads:cert?.reads.length,instances:cert?.insts.length,pairs:cert?rowPairs(p.m,cert,path,p.packet.goal.hyps.at(-1)):[],writes:cert?writesReadState(p.m,cert,path,p.packet.goal.hyps.at(-1)):null,rowQueries:events.filter((e:any)=>e.stage==='row-case'&&!e.cached).length,rowSplits:events.filter((e:any)=>e.stage==='row-demand').length,rowMirrors:events.filter((e:any)=>e.stage==='row-mirror').length,events}
mkdirSync(out,{recursive:true});writeFileSync(join(out,'result.json'),JSON.stringify(record)+'\n');console.log(JSON.stringify({...record,events:undefined}))

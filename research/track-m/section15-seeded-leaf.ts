// Direct old-fixture leaf falsification, not a real E-14 family or whole-op claim.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {check,mcGoal,termColumn,columnTerm,canon,type Path,type LemmaCut} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,withWall} from '../../kernel/prove.ts'
import {deriveCountClosure} from '../../core/count-recovery/derivability-closure.ts'
import {fieldBoundLemmas} from '../../core/count-recovery/field-bound-lemmas.ts'
import {type E} from '../../core/machine.ts'
import {checkConditionalProof} from '../../core/count-recovery/conditional-proof.ts'
import {tierControl} from './section14-control.ts'
import {fieldAttemptObserver,type FieldAttempt} from '../../core/count-recovery/field-demand.ts'
import {pack} from './section18-codec.ts'
const [packetFile,seedFile,leafFile,out]=process.argv.slice(2);if(!packetFile||!seedFile||!leafFile||!out)throw Error('PACKET SEEDS LEAF OUTPUT')
const setupStarted=performance.now()
console.log(JSON.stringify({phase:'load-fixture'}))
const packetText=readFileSync(packetFile,'utf8'),p=JSON.parse(packetText),seed=JSON.parse(readFileSync(seedFile,'utf8')),old=JSON.parse(readFileSync(leafFile,'utf8')),path:Path=new Map(old.firstFailure?.path)
if(!path.size)throw Error('missing captured leaf scope')
console.log(JSON.stringify({phase:'restore-columns',count:seed.columns.length}))
for(const [i,t]of seed.columns.entries())if(termColumn(t)!==`⟦${i}⟧`)throw Error('column restoration')
console.log(JSON.stringify({phase:'construct-root'}))
const root=mcGoal(p.packet.goal.hyps,p.packet.decls,p.cert)
if(!root||JSON.stringify(root.hyps)!==JSON.stringify(seed.root.hyps))throw Error('packet/seed root lineage mismatch')
const preparationStarted=performance.now(),verified:{lemma:LemmaCut,good:{op:'<=',a:E,b:E},index:number}[]=[]
console.log(JSON.stringify({phase:'seed-verification',candidates:seed.accepted.length}))
for(const entry of seed.accepted){const lemma=entry.lemma,source={name:seed.root.name,hyps:lemma.slice.map((i:number)=>seed.root.hyps[i])},against:Path=new Map([[canon(lemma.cut),{lin:lemma.cut,holds:false}]])
 if(lemma.when.length||!check(source,lemma.tree,against))throw Error('unverified root seed '+entry.index)
 // Root equality was checked above. Retain this already-checked slice instead
 // of expanding it into a full-root tree and rechecking thousands of columns.
 verified.push({lemma,good:entry.good,index:entry.index})
 console.log(JSON.stringify({phase:'verified-seed',count:verified.length,index:entry.index,wallMs:performance.now()-preparationStarted}))
}
tierControl.initial=()=>verified
const events:object[]=[],attempts:FieldAttempt[]=[];fieldAttemptObserver.on=e=>attempts.push(e)
const started=performance.now(),work=fullWork();let tree
try{tree=withWall(started+7000,()=>counted(fullRate,()=>deriveCountClosure(p.m,p.packet.decls,root,p.cert,path,clock()+6000,events,{claim:p.packet.goal.hyps.at(-1),conditional:true,fieldSource:(source,proposal,claim,scope,end)=>fieldBoundLemmas(p.m,p.packet.decls,source,proposal,end,events,undefined,scope,{closure:false,splitRows:false,deferCheck:true,fieldClaim:claim,conditional:true})}),true))}finally{fieldAttemptObserver.on=undefined}
const units=(fullWork()-work)/fullRate,searchWallMs=performance.now()-started,checked=!!tree&&checkConditionalProof(root,tree,path),wallMs=performance.now()-started,columns=[]
for(let i=0;;i++){const t=columnTerm(`⟦${i}⟧`);if(t===undefined)break;columns.push(t)}
const record={legacyFixture:true,conditional:true,wholeOp:false,preparationWallMs:started-setupStarted,packetSha256:createHash('sha256').update(packetText).digest('hex'),op:old.op,scope:[...path],seedCount:verified.length,allowance:6000,wallAllowance:7000,units,searchWallMs,wallMs,checked,classAttempts:events.filter((e:any)=>e.stage==='derive-class-attempt'),last:events.filter((e:any)=>e.stage==='closure-final').at(-1),attempts,events}
mkdirSync(out,{recursive:true});writeFileSync(join(out,'leaf.json'),pack({record,root,tree,columns,seeds:verified}));console.log(JSON.stringify({...record,events:undefined,attempts:undefined,scope:undefined}))

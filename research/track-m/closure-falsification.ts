// Reuse the captured-packet preparation verbatim, changing only the diagnostic
// call at its boundary. The generated child is removed even when a test fails.
import {readFileSync,writeFileSync,unlinkSync} from 'node:fs'
import {join} from 'node:path'
const input=process.argv[2]!,reference=process.argv[3]!
if(!input||!reference)throw new Error('usage: closure-falsification.ts input.json checked-core.json')
const original=readFileSync(join(import.meta.dir,'active-source-probe.ts'),'utf8')
const marker='for(const [branch,path]of paths.entries()){' ,position=original.indexOf(marker)
if(position<0||original.indexOf(marker,position+1)>=0)throw new Error('packet preparation boundary changed')
const child=join(import.meta.dir,`.closure-${process.pid}.ts`)
const tail=`
for(const [branch,path]of paths.entries()){
 if(process.env.LAB_ROW_MODE==='equal'){
  const writer=activeWriteRow(m,path);if(!writer)throw new Error('no active row')
  for(const row of rows){const a=linear(row,path)!,b=linear(x(writer),path)!,lin=sub(a,b),back=sub(b,a);path.set(canon(lin),{lin,holds:true});path.set(canon(back),{lin:back,holds:true})}
 }
 const reference=JSON.parse(readFileSync(process.env.LAB_CLOSURE_REFERENCE!,'utf8'))
 const signature=(q:any)=>JSON.stringify({wit:q.wit,below:q.below,terms:q.terms,unit:q.unit})
 const referenceIndices=law.name===reference.law?reference.usedCounts.map((q:any)=>packet.cert.insts.findIndex(p=>signature(p)===signature(q))):[]
 if(referenceIndices.some((i:number)=>i<0))throw new Error('reference core does not match packet')
 const events:any[]=[],start=performance.now(),budget=1500
 const result=withWall(start+60000,()=>counted(fullRate,()=>deriveClosure(m,packet.decls,goal,packet.cert,path,clock()+budget,events,process.env.LAB_CLOSURE_PROFILE==='1'),true))
 const {tree,lemmas,...summary}=result
 const attempts=events.filter(e=>e.stage==='phase-b').map(e=>({round:e.round,index:e.index,arity:e.arity,wit:e.wit,terms:e.terms,checked:e.checked,ms:e.ms,sourceHyps:e.sourceHyps,last:e.events.findLast((v:any)=>v.stage==='boolean-core')?.last}))
 const unions=packet.cert.insts.flatMap((q,index)=>q.terms.length===5?[{index,wit:q.wit,closed:result.closedIndices.includes(index)}]:[])
 console.log(JSON.stringify({falsification:true,law:law.name,branch,rowMode:process.env.LAB_ROW_MODE??'unconstrained',budget,hyps:goal.hyps.length,instances:packet.cert.insts.length,wallMs:performance.now()-start,...summary,referenceIndices,referenceClosed:referenceIndices.filter((i:number)=>result.closedIndices.includes(i)),unions,phaseA:events.filter(e=>e.stage==='phase-a').map(e=>({good:e.good,sourceHyps:e.sourceHyps,sourceInsts:e.sourceInsts,ms:e.ms,checked:e.checked})),roundsLog:events.filter(e=>e.stage==='round'),attempts,final:events.filter(e=>e.stage==='phase-c-query'),transport:events.filter(e=>e.stage==='count-transport')}))
 if(process.env.LAB_CLOSURE_PROFILE==='1'){
  const sources=events.filter(e=>e.stage==='phase-b').map(e=>({index:e.index,wit:e.wit,terms:e.terms,checked:e.checked,pointOutcome:e.pointOutcome,ms:e.ms,...e.profile,columns:Object.fromEntries(e.profile.path.flatMap(([,a]:any)=>Object.keys(a.lin)).filter((name:string)=>name.startsWith('⟦')).map((name:string)=>[name,columnTerm(name)]))}))
  console.log(JSON.stringify({artifact:'source-profile',encoding:'gzip-base64',data:gzipSync(JSON.stringify({law:law.name,reads:packet.cert.reads,insts:packet.cert.insts,sources})).toString('base64')}))
 }
 if(tree&&result.checked)console.log(JSON.stringify({artifact:law.name,encoding:'gzip-base64',proof:gzipSync(JSON.stringify({goal,path:[...path],tree,lemmas})).toString('base64')}))
}
`
writeFileSync(child,"import {deriveClosure} from './derivability-closure.ts'\nimport {gzipSync} from 'node:zlib'\nimport {columnTerm} from '../../kernel/kernel.ts'\n"+original.slice(0,position)+tail)
try{
 for(const test of [{name:'equal-row-star',law:'Inv*',row:'equal'},{name:'active-overlap',law:'Inv2973',row:''}].filter(t=>!process.env.LAB_CLOSURE_ONLY||t.law===process.env.LAB_CLOSURE_ONLY)){
  console.log(JSON.stringify({begin:test.name}))
  const out=Bun.spawnSync(['timeout','-s','KILL','25s',process.execPath,child,input,test.law,'5','all'],{env:{...process.env,LAB_CLOSURE_REFERENCE:reference,LAB_ROW_MODE:test.row},stdout:'pipe',stderr:'pipe'})
  process.stdout.write(out.stdout);process.stderr.write(out.stderr)
  console.log(JSON.stringify({end:test.name,exit:out.exitCode}))
  if(out.exitCode!==0)process.exitCode=1
 }
}finally{unlinkSync(child)}

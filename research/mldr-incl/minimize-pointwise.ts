// Greedily weaken the premises of an already checked conditional certificate.
// The negated conclusion is fixed; each removal needs a new checked proof.
import {readFileSync,writeFileSync} from 'node:fs'
import {brotliCompressSync,brotliDecompressSync,constants} from 'node:zlib'
import {createHash} from 'node:crypto'
import {checkMC,mcGoal} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,grow,withWall} from '../../kernel/prove.ts'
const [input,output,guardText,limitText='2700']=process.argv.slice(2)
if(!input||!output||guardText===undefined)throw Error('INPUT OUTPUT ORIGINAL_GUARD_INDEX [TOTAL_UNITS] required')
const bytes=readFileSync(input),p=JSON.parse(brotliDecompressSync(bytes).toString()),guard=Number(guardText),limit=Number(limitText)
if(!Number.isInteger(guard)||guard<0||guard>=p.hyps.length-1||!Number.isFinite(limit)||limit<=0||limit>2700)throw Error('invalid guard index or bounded diagnostic limit')
if(p.kind!=='conditional-pointwise'||!checkMC(p.hyps,p.decls,p.cert))throw Error('input certificate rejected')
const start=performance.now(),work=fullWork(),result=withWall(start+12000,()=>counted(fullRate,()=>{
 const until=clock()+limit,base={reads:p.cert.reads,insts:p.cert.insts},trials:any[]=[]
 let kept=p.hyps.map((hyp:any,index:number)=>({hyp,index})),tree=p.cert.tree
 for(let index=0;index<p.hyps.length-1&&clock()<until;index++){
  const next=kept.filter((r:any)=>r.index!==index),hyps=next.map((r:any)=>r.hyp),goal=mcGoal(hyps,p.decls,base)
  if(!goal)throw Error('malformed reduced obligation')
  const before=clock(),out=grow(goal,new Map(),{nodes:0,until:Math.min(until,clock()+100)}),proven='tree'in out,checked=proven&&checkMC(hyps,p.decls,{...base,tree:out.tree})
  trials.push({index,removed:checked,verdict:proven?'proven':out.stuck,units:clock()-before})
  if(checked){kept=next;tree=out.tree}
 }
 const remainingOriginalIndices=kept.map((r:any)=>r.index)
 if(!remainingOriginalIndices.includes(guard))throw Error('guard unexpectedly dispensable; inspect rather than asserting non-vacuity')
 const negative=mcGoal(kept.filter((r:any)=>r.index!==guard).map((r:any)=>r.hyp),p.decls,base)
 if(!negative||clock()>=until)throw Error('no budget for missing-guard control')
 const neg=grow(negative,new Map(),{nodes:0,until:Math.min(until,clock()+100)})
 if('tree'in neg||neg.stuck!=='sat')throw Error('missing-guard control did not remain SAT')
 const bundle={...p,hyps:kept.map((r:any)=>r.hyp),cert:{...base,tree},parentSha256:createHash('sha256').update(bytes).digest('hex'),remainingOriginalIndices}
 if(!checkMC(bundle.hyps,bundle.decls,bundle.cert))throw Error('final reduced certificate rejected')
 return {bundle,trials,negative:{stuck:neg.stuck,why:neg.why},remainingOriginalIndices}
},true)),packed=brotliCompressSync(Buffer.from(JSON.stringify(result.bundle)),{params:{[constants.BROTLI_PARAM_QUALITY]:4}})
writeFileSync(output,packed)
console.log(JSON.stringify({scope:'greedily weakened conditional lemma; NOT safety',control:p.control,inputSha256:p.inputSha256,carried:p.carried,targetMap:p.targetMap,proven:true,checked:true,minimized:true,premisesBefore:p.hyps.length-1,premisesAfter:result.bundle.hyps.length-1,remainingOriginalIndices:result.remainingOriginalIndices,trials:result.trials,negative:result.negative,countedMs:(fullWork()-work)/fullRate,wallMs:performance.now()-start,artifact:{encoding:'br',sha256:createHash('sha256').update(packed).digest('hex'),data:packed.toString('base64')}}))

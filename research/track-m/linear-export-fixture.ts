// Ordinary checked linear-cut fixture; no protocol names or assumed count facts.
import {mkdirSync,writeFileSync} from 'node:fs'
import {dirname} from 'node:path'
import {type C,type E,get,n,x} from '../../core/machine.ts'
import {countsForReads} from '../../core/count-facts.ts'
import {type CountCert,type CountDecl,type Goal,type LinCut,type MapRead,checkMC,framePath,linOk,mcGoal} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,grow,withWall} from '../../kernel/prove.ts'
import {mcToLean} from '../../lean-kernel/emit.ts'
export function linearExportFixture():{hyps:C[],decls:CountDecl[],cert:CountCert}{
 const a=get('A',x('member')),b=get('B',x('member')),max:E={op:'max',a,b}
 const decls:CountDecl[]=[['SumA',a],['SumB',b],['SumMax',max]].map(([map,body])=>({map:map as string,j:'row',key:'member',below:n(3),body:body as E}))
 const reads:MapRead[]=[['a','SumA',n(0)],['b','SumB',n(0)],['maximum','SumMax',n(0)]]
 const sum=(left:E,right:E):E=>({op:'add',a:left,b:right}),twice=(a:E):E=>({op:'mul',k:2,a})
 const hyps:C[]=[{op:'<',a:twice(get('SumMax',n(0))),b:sum(get('SumA',n(0)),get('SumB',n(0)))}]
 return counted(fullRate,()=>withWall(performance.now()+3000,()=>{
  const auxiliary:Goal={name:'linear auxiliary',hyps:[{op:'<',a:x('member'),b:n(3)},{op:'<',a:sum(twice(max),n(0)),b:sum(a,sum(b,n(0)))}]}
  const proof=grow(auxiliary,new Map(),{nodes:0,until:clock()+500})
  if(!('tree'in proof))throw Error('no auxiliary proof')
  const cut:LinCut={when:[],pos:[[1,'a'],[1,'b']],neg:[[2,'maximum']],tree:proof.tree},counts=countsForReads(decls,reads)!
  if(!linOk(counts,cut))throw Error('linear cut rejected')
  const request={reads,insts:[]},goal=mcGoal(hyps,decls,request)!
  const result=grow(goal,framePath([],[],new Map(),[],[cut]),{nodes:0,until:clock()+500})
  if(!('tree'in result))throw Error('no main proof')
  const cert:CountCert={...request,tree:result.tree,lins:[cut]}
  if(!checkMC(hyps,decls,cert)||checkMC(hyps,decls,{...cert,lins:[]}))throw Error('linear cut is not checked and essential')
  return {hyps,decls,cert}
 }))
}
if(import.meta.main){
 const file=process.argv[2];if(!file)throw Error('output .lean path required')
 const f=linearExportFixture(),source='import CountMachine\nnamespace Kern\n'+mcToLean('linear_fixture',f.hyps,f.decls,f.cert)+'\nexample : checkMCF linear_fixture_hyps linear_fixture_decls linear_fixture_cert linear_fixture_frames [] [] = false := by decide +kernel\n#print axioms linear_fixture_check\n#print axioms linear_fixture\nend Kern\n'
 mkdirSync(dirname(file),{recursive:true});writeFileSync(file,source)
 console.log('LINEAR_EXPORT_FIXTURE '+JSON.stringify({file,bytes:Buffer.byteLength(source),lins:f.cert.lins!.length}))
}

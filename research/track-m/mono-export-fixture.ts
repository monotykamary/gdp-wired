// A small checked one-sided count cut for the goal-local Lean exporter.
import {mkdirSync,writeFileSync} from 'node:fs'
import {dirname} from 'node:path'
import {type C,get,n,same,x} from '../../core/machine.ts'
import {type CountCert,type CountDecl,type Goal,type MapRead,checkMC} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,withWall} from '../../kernel/prove.ts'
import {proveCountFrameGoal} from '../../core/count-frames.ts'
import {mcToLean} from '../../lean-kernel/emit.ts'
export function monoExportFixture():{hyps:C[],decls:CountDecl[],cert:CountCert}{
 const decls:CountDecl[]=[{map:'Total',j:'row',key:'member',below:n(2),body:get('Cells',x('member'))},{map:'Total#',j:'row',key:'member',below:n(2),body:{op:'if',c:same(x('action'),n(4)),then:n(0),else:get('Cells',x('member'))}}]
 const raw:Goal={name:'one-sided count',hyps:[{op:'<',a:get('Total',n(0)),b:get('Total#',n(0))},same(x('action'),n(4))]}
 const reads:MapRead[]=[['before','Total',n(0)],['after','Total#',n(0)]]
 const cert=counted(fullRate,()=>withWall(performance.now()+3000,()=>proveCountFrameGoal(raw,decls,{reads,insts:[]},{name:'action',value:4,values:[0,1,4]},new Set(['Total']),clock()+1000)))
 if(!cert||cert.monos?.length!==1||!checkMC(raw.hyps,decls,cert)||checkMC(raw.hyps,decls,{...cert,monos:[]}))throw Error('monotone fixture is not checked and essential')
 return {hyps:raw.hyps,decls,cert}
}
if(import.meta.main){
 const file=process.argv[2]
 if(!file)throw Error('output .lean path required')
 const f=monoExportFixture(),source='import CountMachine\nnamespace Kern\n'+mcToLean('mono_fixture',f.hyps,f.decls,f.cert)+'\nexample : checkMCF mono_fixture_hyps mono_fixture_decls mono_fixture_cert mono_fixture_frames [] = false := by decide +kernel\n#print axioms mono_fixture_check\n#print axioms mono_fixture\nend Kern\n'
 mkdirSync(dirname(file),{recursive:true});writeFileSync(file,source)
 console.log('MONO_EXPORT_FIXTURE '+JSON.stringify({file,bytes:Buffer.byteLength(source),monos:f.cert.monos!.length,frames:f.cert.frames!.length}))
}

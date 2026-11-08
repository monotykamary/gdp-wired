// Stop after candidate generation, then test one admission mechanism against that exact snapshot.
import {proveRule} from '../../core/dsl.ts'
import {type Law,type Machine} from '../../core/machine.ts'
import {admitCountedFamily,countSupportContext,countsDump} from '../../core/counts.ts'
import {readTuples} from '../../core/count-support.ts'
import {clock,counted,fullRate,withDeadline,withWall} from '../../kernel/prove.ts'
import {protocols} from '../protocols/ic3syn/models.ts'
const id=process.argv[2]!,p=protocols.find(p=>p.id===id)!,r=p.make(),callerNames=new Set([...r.kindLaws(),...p.laws(r)].map(l=>l.name)),stop=new Error('captured'),box:{data?:{machine:Machine,laws:Law[]}}={},old=countsDump.on
try{
 countsDump.on=event=>{const e=event as {phase?:string,machine?:Machine,laws?:Law[]};if(e.phase==='candidates'&&e.machine&&e.laws){box.data={machine:e.machine,laws:e.laws};throw stop}}
 try{proveRule(r,p.laws(r),{search:{ms:60000}})}catch(e){if(e!==stop)throw e}
}finally{countsDump.on=old}
if(!box.data)throw new Error('no candidate snapshot')
const {machine:m,laws:all}=box.data,caller=all.filter(l=>callerNames.has(l.name)),support=new Set(all.filter(l=>l.name.startsWith('carry:')||l.name.startsWith('scan-prefix:'))),hasCountSource=[...support].some(l=>readTuples(l.holds).some(([map])=>!!m.counts?.[map])),context=countSupportContext(m,caller,all,support),effective=process.argv[3]==='all'?support:context.support,trial=process.argv[3]==='all'?all:context.laws,started=performance.now()
const out=withWall(started+60000,()=>counted(fullRate,()=>{const until=clock()+60000;return withDeadline(until,()=>admitCountedFamily(m,caller,trial,effective,until))},true))
console.log(JSON.stringify({id,candidates:all.length,trial:trial.length,support:support.size,hasCountSource,effective:effective.size,checked:out.proven,why:out.why,ms:performance.now()-started,kept:out.laws.map(l=>l.name)}))

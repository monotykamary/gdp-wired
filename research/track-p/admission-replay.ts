// Exact production admission over a captured, unmodified candidate universe.
import {readFileSync} from 'node:fs'
import {type Law,type Machine} from '../../core/machine.ts'
import {admitCountedFamily,countSupportContext,countsDump,cprof} from '../../core/counts.ts'
import {clock,counted,fullRate,withDeadline,withWall} from '../../kernel/prove.ts'
import {protocols} from '../protocols/ic3syn/models.ts'
const dir=process.argv[2]!,data=JSON.parse(readFileSync(dir+'/production.json','utf8')) as {machine:Machine,laws:Law[]},omitted=new Set<string>(process.argv[3]?JSON.parse(readFileSync(dir+'/'+process.argv[3],'utf8')):[]),all=data.laws.filter(l=>!omitted.has(l.name)),m=data.machine,p=protocols.find(p=>p.id==='paxos_epr')!,r=p.make(),names=new Set([...r.kindLaws(),...p.laws(r)].map(l=>l.name)),caller=all.filter(l=>names.has(l.name)),support=new Set(all.filter(l=>l.name.startsWith('carry:')||l.name.startsWith('scan-prefix:')))
const context=countSupportContext(m,caller,all,support),old=countsDump.on,events:object[]=[],started=performance.now()
try{
 countsDump.on=e=>{if('phase'in e&&e.phase==='demand-attempt'){events.push(e);console.log(JSON.stringify(e))}}
 const out=withWall(started+60000,()=>counted(fullRate,()=>{const until=clock()+60000;return withDeadline(until,()=>admitCountedFamily(m,caller,context.laws,context.support,until))},true))
 console.log(JSON.stringify({summary:true,context:context.laws.length,support:context.support.size,checked:out.proven,why:out.why,ms:performance.now()-started,kept:out.laws.map(l=>l.name),events:events.length,cprof}))
}finally{countsDump.on=old}

// Research-only streaming capture; safe to combine with research/query/dump.ts.
import {appendFileSync,mkdirSync} from 'node:fs'
import {countsDump} from '../../core/counts.ts'
import {fieldAttemptObserver} from '../../core/count-recovery/field-demand.ts'
const dir=process.env.DUMP_DIR
if(dir){mkdirSync(dir,{recursive:true});let context:Record<string,unknown>={},serial=0
 const prior=countsDump.on;countsDump.on=e=>{prior?.(e);const v=e as any;if(v.law)context={law:v.law,pass:v.pass,goal:v.goal,phase:v.phase}}
 fieldAttemptObserver.on=e=>appendFileSync(`${dir}/field-attempts.jsonl`,JSON.stringify({id:serial++,...context,...e})+'\n')
}

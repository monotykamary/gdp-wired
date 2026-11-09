import {protocols} from '../protocols/ic3syn/models.ts';
import {readFileSync} from 'node:fs'; import {createHash} from 'node:crypto';
const file='research/verify-all/model-source-audit.md', text=readFileSync(file,'utf8');
for (const p of protocols) { const key='| `'+p.id+'` |'; if(text.split(key).length!==2) throw Error('missing/duplicate report row '+p.id); const m=p.make().machine;if(m.facts?.length) throw Error('unexpected facts '+p.id); }
for(const [path,hash] of [['research/protocols/ic3syn/models.ts','5d61b846a8331a9b7978b4809d53b88e5918135ded0fc6d527f2a6dc8fb3a601'],['research/protocols/ic3syn/common.ts','d84face9091688872b001f28d0ff31f1180590c57bf944efe6b32168651cd324'],['research/protocols/ic3syn/run.ts','a9fa1e966acf503db0804419f8af7b82cfec671f8fba528716ec5440ea70dd66']] as const) { const got=createHash('sha256').update(readFileSync(path)).digest('hex');if(got!==hash)throw Error('baseline hash changed '+path); }
if(text.includes('M:1007?'))throw Error('unresolved citation');
console.log(JSON.stringify({report:file,rows:protocols.length,baselineHashesMatch:true,sha256:createHash('sha256').update(text).digest('hex')}));

import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {columnTerm} from '../../kernel/kernel.ts'
import {shardControl as s} from './section13-control.ts'
const out=process.argv[3];if(!out)throw new Error('INPUT OUT required')
mkdirSync(out,{recursive:true});s.mode='capture'
const seen=new Set<string>()
s.capture=entry=>{const name=entry.packet.goal.name,label=name.startsWith('Inv2973')?'overlap':name.startsWith('Inv*')?'star':undefined;if(!label||seen.has(label))return;seen.add(label);const columns=[];for(let i=0;;i++){const t=columnTerm(`⟦${i}⟧`);if(t===undefined)break;columns.push(t)}writeFileSync(join(out,label+'.packet.json'),JSON.stringify({...entry,columns,revision:'5974b9165d6860f1157f3bed3cd66a7e1514e904'})+'\n');console.log(JSON.stringify({captured:label,goal:name,instances:entry.cert.insts.length,context:entry.context}))}
// The existing driver reads process.argv[2]; its bounded prefix/cache context is unchanged.
await import('./profile-family.ts')
if(seen.size!==2)throw new Error('both captured action entry packets required')
for(const label of seen)JSON.parse(readFileSync(join(out,label+'.packet.json'),'utf8'))

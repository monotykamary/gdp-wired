import {writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {entryProfile as p} from './entry-profile.ts'
import {diagnostic as d} from './section10-diagnostic.ts'
const [mode,input,out]=process.argv.slice(2);if(!['production','deadline-free'].includes(mode!)||!input||!out)throw new Error('MODE INPUT OUT required');mkdirSync(out,{recursive:true})
const begin=d.begin.bind(d),end=d.end.bind(d);let action:any
// Enable only Inv* op 3: normal mode retains every preceding production law.
d.begin=(kind,meta={})=>{if(kind==='action'&&meta.value===3&&d.label.startsWith('Inv*')){p.beginAction(meta);action=undefined}const f=begin(kind,meta);if(kind==='action'&&meta.value===3&&p.enabled)action=f;p.frame(kind,meta);return f}
d.end=(frame,result)=>{end(frame,result);if(frame===action){p.endAction();action=undefined}}
if(mode==='production'){process.argv=['bun','profile-family.ts',input];await import('./profile-family.ts')}
else{process.argv=['bun','section13-shard.ts',input,'3',join(out,'shard')];await import('./section13-shard.ts')}
const snapshot=p.snapshot();writeFileSync(join(out,mode+'.json'),JSON.stringify({mode,engine:'5974b9165d6860f1157f3bed3cd66a7e1514e904',researchOnly:true,measurement:'unchanged fullWork/fullRate; wall by monotonic realNow; nested exclusive and inclusive spans',...snapshot})+'\n');console.log(JSON.stringify({entryProfile:mode,actions:snapshot.actions,firstLeaf:snapshot.firstLeaf,branches:snapshot.branches,sites:Object.keys(snapshot.functions).length}))

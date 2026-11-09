// Disposable source reconstruction using the existing untrusted CDCL tree builder.
import {readFileSync,writeFileSync,renameSync} from 'node:fs'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux required')
const file='core/count-recovery/derivability-closure.ts',source=readFileSync(file,'utf8')
const before="if(independent){const out=grow(small,path,{nodes:0,until:limit,units:true});if('tree'in out)local=out.tree}"
const after="{const out=growCdcl(small,path,{nodes:0,until:limit},{point:true});if('tree'in out)local=out.tree}"
const oldImport="import {REFUTED} from '../../kernel/cdcl.ts'"
if(source.split(before).length!==2||source.split(oldImport).length!==2)throw Error('source CDCL anchors changed')
const next=source.replace(oldImport,"import {REFUTED,growCdcl} from '../../kernel/cdcl.ts'").replace(before,after).replace('Spend the existing 50+100 fallback envelope on the independent core,','Spend the existing 50+100 fallback envelope on a CDCL core tree,')
writeFileSync(file+'.tmp',next);renameSync(file+'.tmp',file)

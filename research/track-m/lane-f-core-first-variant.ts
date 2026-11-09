// Disposable scheduler worker only: reorder an existing source fallback.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.env.LAB_DISPOSABLE!=='1')throw Error('disposable worker required')
const path='core/count-recovery/derivability-closure.ts',source=readFileSync(path,'utf8')
const before="if(independent){const out=grow(small,path,{nodes:0,until:limit,units:true});if('tree'in out)local=out.tree}"
const after="{const out=grow(small,path,{nodes:0,until:limit,units:true});if('tree'in out)local=out.tree}"
if(source.split(before).length!==2)throw Error('source fallback anchor changed')
writeFileSync(path,source.replace(before,after))

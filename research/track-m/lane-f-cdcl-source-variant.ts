// Disposable source diagnostic: use the existing untrusted CDCL tree builder.
import {readFileSync,writeFileSync,renameSync} from 'node:fs'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux required')
const file='research/track-m/lane-f-source-query.ts',source=readFileSync(file,'utf8')
const before="if(mode.endsWith('boolean'))proof=booleanCore"
const after=`if(mode.endsWith('cdcl')){
     const r=growCdcl(small,scope,{nodes:0,until:coreEnd},{point:mode.includes('-point-')})
     if('tree'in r)proof=r.tree
     else events.push({stage:'core-cdcl',stuck:r.stuck,why:r.why})
    }else if(mode.endsWith('boolean'))proof=booleanCore`
if(source.split(before).length!==2||source.includes("import {growCdcl}"))throw Error('CDCL diagnostic anchor changed')
writeFileSync(file+'.tmp',"import {growCdcl} from '../../kernel/cdcl.ts'\n"+source.replace(before,after));renameSync(file+'.tmp',file)

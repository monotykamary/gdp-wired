import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
if(process.platform!=='linux'||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1')throw new Error('disposable Linux required')
const file='core/count-recovery/derivability-closure.ts',before=readFileSync(file,'utf8'),anchor='const saved:Saved[]=[],models:SourceModel[]=[]'
if(before.split(anchor).length!==2)throw new Error('unique root-seed anchor required')
const after="import {tierControl as __tier} from '../../research/track-m/section14-control.ts'\n"+before.replace(anchor,'const saved:Saved[]=__tier.initial(g),models:SourceModel[]=[]')
writeFileSync(file,after);const hash=(s:string)=>createHash('sha256').update(s).digest('hex');console.log(JSON.stringify({file,before:hash(before),after:hash(after),productionLocalDeadlines:true}))

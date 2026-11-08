import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
const files=['runs/REPORT.md','runs/track-gen-scheduler-blocker.md','runs/track-gen-final-replays-v1/generation-verified.json','runs/track-gen-final-replays-v1/probes-verified.json','runs/track-gen-prefix-check-v1/probes-verified.json','runs/track-gen-gates-v3/ic3syn/partial.json','runs/track-gen-gates-v2/broken/verified.json']
const manifest={status:'incomplete: final Paxos/IC3Syn and broken gates pending',baseline:'6a3874d3',parent:'3394e14c',engine:['6a8792d3','f00e3642','cd38afa5','d9345b9c','f51e8996'],files:files.map(path=>({path,sha256:createHash('sha256').update(readFileSync(path)).digest('hex')}))}
writeFileSync('runs/track-gen-progress-manifest.json',JSON.stringify(manifest,null,2)+'\n');console.log(JSON.stringify({status:manifest.status,files:files.length}))

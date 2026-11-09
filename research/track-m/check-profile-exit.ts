import {writeFileSync} from 'node:fs'
import {readCheckProfile} from './check-cost-profile.ts'
let written=false
function finish(){if(written)return;written=true;const row={observationOnly:true,checkProfile:readCheckProfile()};if(process.env.CHECK_PROFILE_OUT)writeFileSync(process.env.CHECK_PROFILE_OUT,JSON.stringify(row));console.log(JSON.stringify(row))}
process.once('exit',finish)
process.once('SIGTERM',()=>{finish();process.exit(124)})

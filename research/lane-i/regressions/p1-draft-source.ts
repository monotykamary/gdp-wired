// Restore the explicit p1 candidate, never the older paxos-fix.json candidate.
import {readFileSync} from 'node:fs'
import {resolve} from 'node:path'
import {createHash} from 'node:crypto'
const hashes:Record<string,string>=JSON.parse(readFileSync('frozen-paxos/checksums.json','utf8'))
for(const [path,hash]of Object.entries(hashes))if(createHash('sha256').update(readFileSync(path)).digest('hex')!==hash)throw Error('input hash mismatch: '+path)
const config=JSON.parse(readFileSync('p1-input/config.json','utf8')),dest=process.argv[2]
if(!dest||!dest.startsWith('/tmp/')||config.candidate!=='d3adf3c9589ec014a158b6f42ecfb091c999bb43')throw Error('explicit d3adf3c9 candidate and temporary destination required')
const {restore}=await import(resolve('research/verify-all/final-gate-common.ts'))
const meta=restore(resolve('paxos-input'),dest,config.candidate)
console.log('P1_DRAFT_SOURCE '+JSON.stringify(meta))

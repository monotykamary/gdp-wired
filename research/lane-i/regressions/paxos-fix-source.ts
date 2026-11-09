// Restore and verify the exact committed repair for remote validation only.
import {readFileSync} from 'node:fs'
import {resolve} from 'node:path'
import {createHash} from 'node:crypto'
const hashes:Record<string,string>=JSON.parse(readFileSync('frozen-paxos/checksums.json','utf8'))
for(const [path,hash]of Object.entries(hashes))if(createHash('sha256').update(readFileSync(path)).digest('hex')!==hash)throw Error('input hash mismatch: '+path)
const {restore,harnessHashes}=await import(resolve('research/verify-all/final-gate-common.ts'))
const {candidate}=JSON.parse(readFileSync('regression-driver/paxos-fix.json','utf8'))
const dest=process.argv[2]
if(!dest||!dest.startsWith('/tmp/'))throw Error('temporary destination required')
const meta=restore(resolve('paxos-input'),dest,candidate),actual=harnessHashes(dest),expected=JSON.parse(readFileSync('regression-driver/paxos-harness-hashes.json','utf8'))[candidate]
if(Object.keys(actual).length!==Object.keys(expected).length||Object.entries(expected).some(([path,hash])=>actual[path]!==hash))throw Error('protected source mismatch')
console.log('PAXOS_FIX_SOURCE '+JSON.stringify({meta,hashes:actual}))

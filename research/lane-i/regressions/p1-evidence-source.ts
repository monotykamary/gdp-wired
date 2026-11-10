import {readFileSync} from 'node:fs'
import {resolve} from 'node:path'
import {createHash} from 'node:crypto'
const hashes:Record<string,string>=JSON.parse(readFileSync('frozen-paxos/checksums.json','utf8'))
for(const [p,h]of Object.entries(hashes))if(createHash('sha256').update(readFileSync(p)).digest('hex')!==h)throw Error('input changed: '+p)
const config=JSON.parse(readFileSync('p1-input/config.json','utf8')),dest=process.argv[2]
if(!dest||!dest.startsWith('/tmp/')||config.fixed!=='f7c5b4bad58578d95684ca279e882f48fabd8525')throw Error('fixed source and temporary destination required')
const {restore}=await import(resolve('research/verify-all/final-gate-common.ts'))
console.log('P1_EVIDENCE_SOURCE '+JSON.stringify(restore(resolve('paxos-input'),dest,config.fixed)))

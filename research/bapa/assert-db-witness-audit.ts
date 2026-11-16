import {readFileSync} from 'node:fs'
import {join} from 'node:path'
const out=process.env.SUPERCOMPUTER_OUTPUT_DIR;if(!out)throw Error('output directory required')
const a=JSON.parse(readFileSync(join(out,'client_server_db_ae.json'),'utf8')),w=a.audit.witnesses?.[0]
if(a.ghostsQualified!==true||!a.noSearch||a.publicCalls!==0||!a.sourceUnchanged||a.proposed!==27||a.dropped!==0||a.witnessProposals!==1||a.witnessRefusals.length||a.fieldRowProposals!==0||w?.sourceVariables!==1||w?.targetVariables!==1||Object.keys(w?.ghostMaps??{}).length!==3||w?.trusted!==false)throw Error('DB witness restatement contract failed')
console.log(JSON.stringify({status:'ok',publicCalls:0,candidates:27,dropped:0,witnesses:1,ghostMaps:3}))

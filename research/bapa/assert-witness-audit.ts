// Assert only the no-search proposal contract, not protocol correctness.
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
const out=process.env.SUPERCOMPUTER_OUTPUT_DIR
if(!out)throw Error('output directory required')
const audit=JSON.parse(readFileSync(join(out,'sharded_kv_no_lost_keys.json'),'utf8'))
if(audit.noSearch!==true||audit.publicCalls!==0||audit.sourceUnchanged!==true||audit.proposed!==10||audit.dropped!==0||audit.witnessProposals!==1||audit.witnessRefusals.length!==0||audit.fieldRowProposals!==0)throw Error('incomplete exact witness proposal audit')
const w=audit.audit.witnesses[0]
if(w.status!=='proposed'||w.sourceVariables!==2||w.targetVariables!==4||Object.keys(w.ghostMaps).length!==3||w.trusted!==false||audit.audit.captureSha256!=='e41e37724663b689ed716c639694ff002c0be92e99ace6267f4ef8ad3cf8fe4f')throw Error('witness proposal identity mismatch')
console.log(JSON.stringify({status:'ok',noSearch:true,publicCalls:0,candidates:audit.proposed,ghostMaps:3,sourceVariables:2,targetVariables:4}))

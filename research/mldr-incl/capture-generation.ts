// Generation-only capture; run unchanged inside the chosen generator checkout.
import {brotliCompressSync,constants} from 'node:zlib'
import {writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {protocols} from '../protocols/ic3syn/models.ts'
import {candidates,guardLaws} from '../../core/counts.ts'
import {smallOf,trueSmall} from '../../core/exists.ts'
import {type Law} from '../../core/machine.ts'
import {clock,counted,fullRate,queryHook,withWall} from '../../kernel/prove.ts'
const protocol=protocols.find(p=>p.id===(process.argv[2]??'mldr'))!;if(!protocol)throw Error('protocol missing')
let queries=0;queryHook.on=()=>{queries++}
const start=performance.now(),r=protocol.make(),caller=[...r.kindLaws(),...protocol.laws(r)],g=guardLaws(r.machine),m={...r.machine,counts:{...r.machine.counts,...g.counts}},support=new Set<Law>()
smallOf(m,r.machine)
const laws=withWall(performance.now()+60000,()=>counted(fullRate,()=>{if(!caller.filter(l=>!l.some?.length).every(l=>trueSmall(m,[l])))throw Error('caller fails samples');return [...caller,...candidates(r.machine,m,caller,caller,g.laws,60000,clock()+60000,support)]},true))
if(queries)throw Error('generation issued a proof query')
const family={machine:m,laws,support:[...support].map(l=>l.name),caller:caller.map(l=>l.name),revision:process.env.GENERATOR_REV};if(process.env.MLDR_INCL_FAMILY_OUT)writeFileSync(process.env.MLDR_INCL_FAMILY_OUT,JSON.stringify(family));const files={'family-first.json':JSON.stringify(family)},bytes=brotliCompressSync(Buffer.from(JSON.stringify(files)),{params:{[constants.BROTLI_PARAM_QUALITY]:4}})
console.log(JSON.stringify({artifact:'mldr-incl-capture',generationOnly:true,revision:family.revision,lawCount:laws.length,names:laws.map(l=>l.name),queries,wallMs:performance.now()-start,files:1,omitted:0,sha256:createHash('sha256').update(bytes).digest('hex'),data:bytes.toString('base64')}))

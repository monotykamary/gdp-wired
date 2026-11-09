// Validate both process receipts before retaining a conditional certificate.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {brotliDecompressSync} from 'node:zlib'
const [root,out]=process.argv.slice(2)
if(!root||!out)throw Error('ROOT OUT required')
const archive=JSON.parse(brotliDecompressSync(readFileSync('research/mldr-incl/fixtures/e14-safety.br')).toString()),inputSha256=createHash('sha256').update(archive['stage-0.json']).digest('hex'),summary=[]
mkdirSync(out,{recursive:true})
for(const label of ['guarded','tight']){
 const control=label+'-domain',rows=readFileSync(`${root}/pointwise-${label}-certificate.log`,'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l)),producers=rows.filter(r=>r.artifact),verifiers=rows.filter(r=>!r.artifact&&typeof r.sha256==='string')
 if(producers.length!==1||verifiers.length!==1)throw Error('one producer and fresh-process verifier required')
 const p=producers[0],v=verifiers[0],bytes=Buffer.from(p.artifact.data,'base64'),sha256=createHash('sha256').update(bytes).digest('hex'),bundle=JSON.parse(brotliDecompressSync(bytes).toString())
 if(!p.proven||!p.checked||!v.checked||p.artifact.encoding!=='br'||p.artifact.sha256!==sha256||v.sha256!==sha256||p.control!==control||v.control!==control||bundle.control!==control||p.inputSha256!==inputSha256||v.inputSha256!==inputSha256||bundle.inputSha256!==inputSha256||bundle.kind!=='conditional-pointwise')throw Error('producer/verifier/input binding mismatch')
 writeFileSync(`${out}/${control}.br`,bytes)
 summary.push({scope:'conditional pointwise lemma; NOT safety',control,inputSha256,sha256,bytes:bytes.length,countedMs:p.countedMs,producerChecked:true,independentChecked:true,carried:p.carried,targetMap:p.targetMap})
}
writeFileSync(`${out}/index.json`,JSON.stringify(summary,null,2)+'\n');console.log(JSON.stringify(summary))

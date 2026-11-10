// A fresh process checks the saved conditional certificate, without the matcher.
import {readFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {brotliDecompressSync} from 'node:zlib'
import {checkMC} from '../../kernel/kernel.ts'
const bytes=readFileSync(process.argv[2]!),sha256=createHash('sha256').update(bytes).digest('hex')
if(process.argv[3]&&process.argv[3]!==sha256)throw Error('certificate hash mismatch')
const p=JSON.parse(brotliDecompressSync(bytes).toString())
if(p.kind!=='conditional-pointwise'||!checkMC(p.hyps,p.decls,p.cert))throw Error('conditional certificate rejected')
console.log(JSON.stringify({scope:'conditional pointwise lemma; NOT safety',checked:true,sha256,inputSha256:p.inputSha256,control:p.control,carried:p.carried,targetMap:p.targetMap}))

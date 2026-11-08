// Zero-search authentication of a saved raw MC goal and proof.
import {readFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {checkMC} from '../../kernel/kernel.ts'
import {work,costs} from '../../core/solver.ts'
const dir=process.argv[2]!,gb=readFileSync(dir+'/goal.json','utf8'),pb=readFileSync(dir+'/proof.json','utf8'),pack=JSON.parse(gb),cert=JSON.parse(pb)
const zero=()=>work.n===0&&Object.values(costs).every(n=>n===0)
if(!zero())throw Error('search already ran')
const checked=checkMC(pack.raw.hyps,pack.decls,cert),emptyTreeRejected=!checkMC(pack.raw.hyps,pack.decls,{...cert,tree:{leaf:[]}}),sha=(s:string)=>createHash('sha256').update(s).digest('hex')
console.log(JSON.stringify({checked,emptyTreeRejected,searchWork:work.n,zeroSearch:zero(),goalSHA256:sha(gb),proofSHA256:sha(pb)}))
if(!checked||!emptyTreeRejected||!zero())throw Error('authentication failed')

// Authentication only: this file never imports a prover or reconstructs a goal.
import {readFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {checkMC,type Goal,type CountDecl,type CountCert} from '../../kernel/kernel.ts'
import {work,costs} from '../../core/solver.ts'
const root=process.argv[2]??'runs/track-p-certs',sha=(b:string)=>createHash('sha256').update(b).digest('hex')
for(const id of ['c9','c11']){
 if(work.n!==0||Object.values(costs).some(n=>n!==0))throw Error('not zero-search')
 const gb=readFileSync(root+'/'+id+'/goal.json','utf8'),pb=readFileSync(root+'/'+id+'/proof.json','utf8')
 const pack=JSON.parse(gb) as {raw:Goal,decls:CountDecl[],gg:Goal},cert=JSON.parse(pb) as CountCert
 const checked=checkMC(pack.raw.hyps,pack.decls,cert),dropWitnessRejected=!checkMC(pack.raw.hyps,pack.decls,{...cert,insts:cert.insts.slice(1)})
 console.log(JSON.stringify({id,checked,dropWitnessRejected,rawHyps:pack.raw.hyps.length,encodedHyps:pack.gg.hyps.length,kernelSHA256:sha(readFileSync('kernel/kernel.ts','utf8')),goalSHA256:sha(gb),proofSHA256:sha(pb),searchWork:work.n,nonzeroSearchCosts:Object.fromEntries(Object.entries(costs).filter(([,n])=>n!==0))}))
 if(!checked||!dropWitnessRejected||work.n!==0||Object.values(costs).some(n=>n!==0))throw Error('authentication failed: '+id)
}

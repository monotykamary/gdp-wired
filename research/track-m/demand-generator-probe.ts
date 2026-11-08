// Diagnostic only: reconstruct the canonical 41-read focused packet, then ask
// the production demand wrapper for the missing union and both partitions.
import {readFileSync,writeFileSync,unlinkSync} from 'node:fs'
import {join} from 'node:path'
const input=process.argv[2];if(!input)throw new Error('usage: demand-generator-probe.ts input.json')
const source=readFileSync(join(import.meta.dir,'active-source-probe.ts'),'utf8'),marker='for(const [branch,path]of paths.entries()){',at=source.indexOf(marker)
if(at<0||source.indexOf(marker,at+1)>=0)throw new Error('changed canonical boundary')
const child=join(import.meta.dir,`.demand-${process.pid}.ts`)
const tail=`
const requested=new Set<string>();walkOnce(packet.goal.hyps.at(-1),(o:any)=>{if(o.op==='get')for(const r of packet.cert.reads)if(r[1]===o.map&&JSON.stringify(r[2])===JSON.stringify(o.key))requested.add(r[0])})
const counts=countsForReads(packet.decls,packet.cert.reads)!,sizes=counts.map(c=>{let size=0;walkOnce(c,()=>size++);return {id:c.v,size}})
const started=performance.now(),demand=demandCountCert(m,packet.decls,packet.cert,packet.goal.hyps.at(-1)!)
const signature=(terms:[number,string][])=>JSON.stringify([...terms].sort((a,b)=>a[1].localeCompare(b[1])))
const targets:Record<string,[number,string][]>= {R2:[[1,'r$9'],[1,'r$16'],[-1,'r$24'],[-1,'r$25'],[-1,'r$26']],R5X:[[1,'r$7'],[-1,'r$10'],[-1,'r$11']],R5S:[[1,'r$8'],[-1,'r$12'],[-1,'r$11']]}
for(const [name,terms]of Object.entries(targets))if(!demand.insts.some(q=>signature(q.terms)===signature(terms)))throw new Error('missing demanded '+name)
console.log(JSON.stringify({mode:'demand-generator',requested:[...requested],sizes,carried:counts.filter(c=>['r$7','r$8','r$9','r$15','r$16'].includes(c.v)).map(c=>({id:c.v,body:c.body})),reads:demand.reads.length,prior:packet.cert.insts.length,instances:demand.insts.length,structured:demand.insts.filter(q=>q.terms.length>=3).length,wallMs:performance.now()-started,matches:Object.fromEntries(Object.entries(targets).map(([name,terms])=>[name,{forward:demand.insts.filter(q=>signature(q.terms)===signature(terms)),reverse:demand.insts.filter(q=>signature(q.terms)===signature(terms.map(([k,id])=>[-k,id])))}]))}))
`
writeFileSync(child,"import {demandCountCert} from '../../core/count-focused.ts'\nimport {countsForReads} from '../../core/count-facts.ts'\n"+source.slice(0,at)+tail)
try{const p=Bun.spawnSync(['timeout','-s','KILL','20s',process.execPath,child,input,'Inv2973','5','all'],{stdout:'pipe',stderr:'pipe'});process.stdout.write(p.stdout);process.stderr.write(p.stderr);if(p.exitCode!==0)process.exitCode=1}finally{unlinkSync(child)}

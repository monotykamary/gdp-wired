// Diagnostic only: inspect field-order scopes on the canonical active packet.
import {readFileSync,writeFileSync,unlinkSync} from 'node:fs'
import {join} from 'node:path'
const input=process.argv[2];if(!input)throw new Error('usage: scalar-guard-probe.ts input.json')
const source=readFileSync(join(import.meta.dir,'active-source-probe.ts'),'utf8'),marker='for(const [branch,path]of paths.entries()){',at=source.indexOf(marker)
if(at<0||source.indexOf(marker,at+1)>=0)throw new Error('changed canonical boundary')
const child=join(import.meta.dir,`.scalar-${process.pid}.ts`)
const tail=`
const signature=(terms:[number,string][])=>JSON.stringify([...terms].sort((a,b)=>a[1].localeCompare(b[1])))
const targets:Record<string,[number,string][]>= {R2:[[1,'r$9'],[1,'r$16'],[-1,'r$24'],[-1,'r$25'],[-1,'r$26']],R4X:[[1,'r$4'],[-1,'r$11']],R4S:[[1,'r$5'],[-1,'r$12']],R4Reverse:[[1,'r$6'],[-1,'r$10']]}
for(const [name,terms]of Object.entries(targets)){
 const inst=packet.cert.insts.find(q=>signature(q.terms)===signature(terms))
 const guards=inst?countScalarGuards(m,packet.decls,packet.cert.reads,inst,paths[0]!,goal):[]
 console.log(JSON.stringify({mode:'scalar-guards',name,found:!!inst,terms,guards}))
 if(!inst)throw new Error('missing demanded '+name)
 if(name==='R2'&&!guards.length)throw new Error('R2 has no scalar-order scopes')
}
`
writeFileSync(child,"import {countScalarGuards} from '../../core/count-recovery/scalar-guards.ts'\n"+source.slice(0,at)+tail)
try{const p=Bun.spawnSync(['timeout','-s','KILL','30s',process.execPath,child,input,'Inv2973','5','all'],{stdout:'pipe',stderr:'pipe',env:{...process.env,LAB_DEMAND_PROPOSALS:'1'}});process.stdout.write(p.stdout);process.stderr.write(p.stderr);if(p.exitCode!==0)process.exitCode=1}finally{unlinkSync(child)}

// Reuse canonical packet preparation; replace only the diagnostic boundary.
import {readFileSync,writeFileSync,unlinkSync} from 'node:fs'
import {join} from 'node:path'
const input=process.argv[2]!,profile=process.argv[3]!
if(!input||!profile)throw new Error('usage: section6-run.ts input.json profile.log')
const source=readFileSync(join(import.meta.dir,'active-source-probe.ts'),'utf8'),marker='for(const [branch,path]of paths.entries()){',at=source.indexOf(marker)
if(at<0||source.indexOf(marker,at+1)>=0)throw new Error('changed canonical boundary')
const child=join(import.meta.dir,`.section6-${process.pid}.ts`)
const tail=`
if(law.name.startsWith('Inv*')){
 const path=paths[0];if(!path||paths.length!==1)throw new Error('unexpected active branches')
 const writer=activeWriteRow(m,path);if(!writer)throw new Error('no active writer')
 for(const row of rows){const a=linear(row,path)!,b=linear(x(writer),path)!,lin=sub(a,b),back=sub(b,a);path.set(canon(lin),{lin,holds:true});path.set(canon(back),{lin:back,holds:true})}
 const started=performance.now();withWall(started+10000,()=>counted(fullRate,()=>starTests(goal,packet.cert,path,process.env.LAB_SECTION6_PROFILE!),true))
}else{const started=performance.now();withWall(started+10000,()=>counted(fullRate,()=>generatorTest(packet.goal,packet.decls,packet.cert),true))}
`
writeFileSync(child,"import {starTests,generatorTest} from './section6-isolated.ts'\n"+source.slice(0,at)+tail)
try{for(const law of ['Inv*','Inv2973']){const p=Bun.spawnSync(['timeout','-s','KILL','20s',process.execPath,child,input,law,'5','all'],{env:{...process.env,LAB_SECTION6_PROFILE:profile},stdout:'pipe',stderr:'pipe'});process.stdout.write(p.stdout);process.stderr.write(p.stderr);if(p.exitCode!==0)process.exitCode=1}}finally{unlinkSync(child)}

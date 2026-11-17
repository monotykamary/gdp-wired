// Compile actual generated machine proofs using ONLY leanProject's shipped sources.
// No checkout oleans or sibling /tmp snapshots participate in this isolated gate.
import {mkdtempSync,readFileSync,writeFileSync,rmSync} from 'node:fs'
import {join} from 'node:path'
import {tmpdir} from 'node:os'
import {spawnSync} from 'node:child_process'
import {leanProject} from '../../lean-kernel/emit.ts'

const input=process.argv[2],out=process.env.SUPERCOMPUTER_OUTPUT_DIR
if(!input||!out)throw Error('usage: packaged-lean-gate.ts generated-machine-source')
const source=readFileSync(input,'utf8'),project=leanProject(source,{name:'PackagedProofs'})
for(const name of ['WordDivision.lean','WordDivisionBridge.lean'])
  if(!project[name])throw Error('missing shipped proof module '+name)
const root=mkdtempSync(join(tmpdir(),'gdp-packaged-lean-')),order:string[]=[],active=new Set<string>(),done=new Set<string>()
function visit(name:string):void{
  if(done.has(name))return
  if(active.has(name))throw Error('cyclic Lean module '+name)
  const body=project[name+'.lean']
  if(body===undefined)return // standard installed Lean/Std module
  active.add(name)
  for(const line of body.split('\n'))if(line.startsWith('import '))
    for(const dep of line.slice(7).trim().split(/\s+/))visit(dep)
  active.delete(name);done.add(name);order.push(name)
}
try{
  for(const [name,text]of Object.entries(project))writeFileSync(join(root,name),text)
  visit('PackagedProofs')
  let log=''
  for(const module of order){
    const result=spawnSync('lean',['-o',module+'.olean',module+'.lean'],{cwd:root,
      env:{...process.env,LEAN_PATH:root},encoding:'utf8',timeout:120_000,maxBuffer:8*1024*1024})
    log+=`\n## ${module}\n${result.stdout??''}${result.stderr??''}`
    writeFileSync(join(out,'dependency-lean.log'),log)
    // Audit the target's answers exactly once. Dependencies also print some of
    // these declarations, so concatenating both would falsely fail coverage.
    if(module==='PackagedProofs')writeFileSync(join(out,'lean.log'),(result.stdout??'')+(result.stderr??''))
    if(result.error||result.status!==0)throw Error(`packaged module ${module}: ${String(result.error)} status=${result.status}`)
  }
  console.log(JSON.stringify({packagedOnly:true,modules:order,sourceModules:Object.keys(project).filter(n=>n.endsWith('.lean')).length,
    note:'Only the actual proof dependency closure is compiled; not a claim that every optional library root was rebuilt.'}))
}finally{rmSync(root,{recursive:true,force:true})}

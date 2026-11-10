// The audit tooling is checked on an isolated a8 source tree; this is not a new gate.
import{readFileSync,mkdtempSync,mkdirSync,readdirSync,copyFileSync,rmSync}from'node:fs'
import{resolve,join}from'node:path'
import{createHash}from'node:crypto'
import{runResourceMeasured}from'./resource-run.ts'
const input=resolve(process.argv[2]??'audit-data'),frozen=resolve(process.argv[3]??'.'),{restore,command}=await import(resolve('research/verify-all/final-gate-common.ts')),root=mkdtempSync('/tmp/follow-up-tools-'),sha=(v:Uint8Array)=>createHash('sha256').update(v).digest('hex'),cfg=JSON.parse(readFileSync(join(frozen,'config.json'),'utf8'))
try{
 const sourceManifest=JSON.parse(readFileSync(join(input,'source-manifest.json'),'utf8'));for(const[p,h]of Object.entries(sourceManifest))if(sha(readFileSync(join(input,'source',p)))!==h)throw Error('audit source hash mismatch '+p)
 if(sha(readFileSync(join(input,'resource-run.ts')))!==sha(readFileSync(join(frozen,'driver/resource-run.ts'))))throw Error('resource runner differs from measured worker')
 restore(join(frozen,'gate-inputs'),root,cfg.revisions.candidate)
 const target=join(root,'research/lane-i/follow-up');mkdirSync(target,{recursive:true})
 for(const name of readdirSync(join(input,'source')).filter(n=>n.endsWith('.ts')))copyFileSync(join(input,'source',name),join(target,name))
 for(const[p,h]of Object.entries(cfg.sources.candidate))if(sha(readFileSync(join(root,p)))!==h)throw Error('candidate source changed '+p)
 command('bun',['install','--frozen-lockfile'],root)
 const checked=await runResourceMeasured('bun',['run','check'],root,'follow-up-tools-check',600)
 console.log('FOLLOW_TOOLS_CHECK '+JSON.stringify({exit:checked.status,signal:checked.signal,wallMs:checked.wallMs,resources:checked.resources,stdout:checked.stdout,stderr:checked.stderr}))
 if(checked.status!==0)throw Error('follow-up source check failed')
 if(command('git',['status','--porcelain','--untracked-files=no'],root))throw Error('tracked candidate source changed')
 console.log('FOLLOW_TOOLS_CLEAN '+JSON.stringify({candidate:cfg.revisions.candidate,sourceOverlay:'research/lane-i/follow-up only; original production sources unchanged'}))
}finally{rmSync(root,{recursive:true,force:true})}

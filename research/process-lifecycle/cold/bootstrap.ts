// Builtins-only bootstrap. No model, extractor, prover, or checker imports.
import {readFileSync,writeFileSync,writeSync,mkdirSync,mkdtempSync,copyFileSync,constants,rmSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {spawnSync} from 'node:child_process'
import {dirname,join,isAbsolute} from 'node:path'
import {fileURLToPath} from 'node:url'
import {tmpdir} from 'node:os'
const root=dirname(fileURLToPath(import.meta.url)),expected=process.argv[2],sha=(b:Buffer)=>createHash('sha256').update(b).digest('hex')
function emit(data:unknown){const b=Buffer.from('LIFECYCLE_COLD '+JSON.stringify(data)+'\n');let n=0;while(n<b.length)n+=writeSync(1,b.subarray(n))}
const start=Date.now();let stage=''
try{
 emit({event:'bootstrap-start',requestedSeconds:60,nativeSeconds:30,noInstall:true})
 const raw=readFileSync(join(root,'manifest.json'));if(sha(raw)!==expected)throw Error('manifest pin mismatch')
 const m=JSON.parse(raw.toString());stage=mkdtempSync(join(tmpdir(),'astra-lifecycle-cold-'))
 for(const f of m.files){
  if(isAbsolute(f.path)||f.path.split('/').includes('..'))throw Error('unsafe input path')
  const bytes=readFileSync(join(root,f.path));if(sha(bytes)!==f.sha256)throw Error('input drift '+f.path)
  const dst=join(stage,f.path);mkdirSync(dirname(dst),{recursive:true});copyFileSync(join(root,f.path),dst,constants.COPYFILE_EXCL)
  if(sha(readFileSync(dst))!==f.sha256)throw Error('copy mismatch '+f.path)
 }
 writeFileSync(join(stage,'manifest.json'),raw,{flag:'wx'})
 emit({event:'bootstrap-verified',manifestSha256:expected,inputCount:m.files.length,privateStage:true,elapsedMs:Date.now()-start})
 const remaining=Math.min(24000,27000-(Date.now()-start));if(remaining<=0)throw Error('setup consumed budget')
 const r=spawnSync('bun',['--no-install',join(stage,'check.ts'),expected],{cwd:stage,timeout:remaining,killSignal:'SIGKILL',stdio:['ignore','inherit','inherit'],env:{...process.env,PYTHONDONTWRITEBYTECODE:'1'}})
 emit({event:'worker-complete',code:r.status,signal:r.signal,error:r.error?String(r.error):null,elapsedMs:Date.now()-start})
 process.exitCode=!r.error&&!r.signal&&r.status===0?0:2
}catch(e){emit({event:'bootstrap-fatal',error:String(e)});process.exitCode=2}
finally{if(stage)rmSync(stage,{recursive:true,force:true})}

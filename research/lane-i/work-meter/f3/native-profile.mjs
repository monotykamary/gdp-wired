import {strict as assert} from 'node:assert'
import {readFileSync,writeFileSync,copyFileSync,mkdirSync,mkdtempSync,rmSync,appendFileSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {instrumentNativeCanon} from './native-instrument.ts'
const {restore,command}=await import(resolve('recovery-input/final-gate-common.ts'))
const hash=value=>createHash('sha256').update(value).digest('hex'),config=JSON.parse(readFileSync('native-profile-input/identity.json','utf8'))
const baseline=readFileSync('native-profile-input/baseline.log','utf8');assert.equal(hash(baseline),config.baselineSha256)
const prior=baseline.split('\n').filter(line=>line.startsWith('F3_SOLVER_RESULT ')).map(line=>JSON.parse(line.slice('F3_SOLVER_RESULT '.length)))
const off=prior.find(row=>row.monitor===false);assert(off);assert.equal(off.id,'mldr');assert.equal(off.work,15000000)
const root=mkdtempSync('/tmp/native-profile-')
try{
 restore(resolve('recovery-input'),root,config.base)
 const pack=readFileSync('native-profile-input/source.pack');assert.equal(hash(pack),config.packSha256)
 const p=spawnSync('git',['unpack-objects','-q'],{cwd:root,input:pack,timeout:120000});assert.equal(p.status,0)
 appendFileSync(join(root,'.git/shallow'),config.pin+'\n');command('git',['checkout','--detach',config.pin],root)
 assert.equal(command('git',['rev-parse','HEAD^{tree}'],root),config.tree)
 command('bun',['install','--frozen-lockfile'],root,180000)
 const tooling=join(root,'research/lane-i/f3'),out=join(root,'f3-output');mkdirSync(tooling,{recursive:true});mkdirSync(out)
 copyFileSync('native-profile-input/native-spans.ts',join(tooling,'native-spans.ts'))
 copyFileSync('native-profile-input/profile-archive.ts',join(tooling,'profile-archive.ts'))
 writeFileSync(join(tooling,'facade.ts'),readFileSync('native-profile-input/facade.source','utf8')+"\nexport {setNativeSpanBuffer} from './native-spans.ts'\n")
 const instrumentation=instrumentNativeCanon(root,process.argv.includes('--extended'))
 for(const file of ['native-solver-observer.mjs','native-observer-worker.mjs','profile-window.mjs'])copyFileSync('native-profile-input/'+file,join(out,file))
 command('bun',['build','./research/lane-i/f3/facade.ts','--target=node','--format=esm','--outfile=./f3-output/facade.mjs','--sourcemap=inline'],root,180000)
 command('bun',['build','./research/lane-i/f3/native-spans.ts','--target=node','--format=esm','--outfile=./f3-output/native-spans.mjs'],root,180000)
 command('bun',['build','./research/lane-i/f3/profile-archive.ts','--target=node','--format=esm','--outfile=./f3-output/profile-archive.mjs'],root,180000)
 console.log('F3_NATIVE_SOURCE '+JSON.stringify({config,instrumentation,helperSha256:hash(readFileSync('native-profile-input/native-spans.ts'))}))
 const child=spawnSync('node',['f3-output/native-solver-observer.mjs'],{cwd:root,encoding:'utf8',timeout:600000,maxBuffer:4*1024*1024})
 console.log('F3_NATIVE_PROCESS '+JSON.stringify({exit:child.status,signal:child.signal,error:String(child.error??'')}));console.log(child.stdout);if(child.stderr)console.error(child.stderr.slice(-12000))
 assert.equal(child.status,0,'external guard is not a solver verdict');assert.equal(child.signal,null)
 const lines=child.stdout.split('\n'),results=lines.filter(line=>line.startsWith('F3_NATIVE_SOLVER_RESULT ')).map(line=>JSON.parse(line.slice('F3_NATIVE_SOLVER_RESULT '.length)))
 assert.equal(results.length,1);const on=results[0];assert.equal(on.runtime,off.runtime);assert.deepEqual(on.result,off.result);assert.deepEqual(on.raw,off.raw)
 assert.deepEqual(Object.keys(on.phases).sort(),Object.keys(off.phases).sort());for(const key of Object.keys(off.phases))assert.deepEqual(on.phases[key].raw,off.phases[key].raw)
 for(const file of instrumentation.files)assert.equal(hash(readFileSync(join(root,file.path))),file.after)
 const windows=lines.filter(line=>line.startsWith('F3_NATIVE_RAW_SILENCE ')).map(line=>JSON.parse(line.slice('F3_NATIVE_RAW_SILENCE '.length)))
 const attributed=windows.filter(row=>row.native.attributed);for(const row of attributed){assert(row.stable&&row.profileWindow.valid&&row.native.profileWindow.valid);assert(row.native.before.id>0);assert.equal(row.native.before.sequence,row.native.after.sequence)}
 console.log('F3_NATIVE_COMPARISON '+JSON.stringify({passed:true,source:config.pin,sameRawAndVerdict:true,sameExclusivePhaseRaw:true,stableWindows:windows.length,attributedWindows:attributed.length,operations:attributed.map(row=>instrumentation.mapping.find(item=>item.id===row.native.before.id)),spanCount:on.spanCount,spanOverflow:on.spanOverflow,scope:'Node invocation-boundary diagnostic against a saved same-source baseline; no overhead, exact native-instruction, Bun F3, full F3 or W claim'}))
}finally{rmSync(root,{recursive:true,force:true})}

import {strict as assert} from 'node:assert'
import {readFileSync,writeFileSync,copyFileSync,mkdtempSync,mkdirSync,rmSync,appendFileSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
import {instrumentNativeCanon} from './native-instrument.ts'
const {restore,command}=await import(resolve('recovery-input/final-gate-common.ts'))
const base='b11e1f651618b3d3fcaf6cec66b4a8b0203cdcd3',pin='aeef60912e189573eb24e658af7e915109a971d2'
const root=mkdtempSync('/tmp/native-canon-check-')
try{
 restore(resolve('recovery-input'),root,base)
 const unpacked=spawnSync('git',['unpack-objects','-q'],{cwd:root,input:readFileSync('strategy-input/calibration-source.pack'),timeout:120000});assert.equal(unpacked.status,0)
 appendFileSync(join(root,'.git/shallow'),pin+'\n');command('git',['checkout','--detach',pin],root)
 command('git',['apply',resolve('native-input/candidate.patch')],root)
 command('git',['add','-A'],root);assert.equal(command('git',['write-tree'],root),'6d1453342ca15df8bf948465c13cbf9a1aedf8a2')
 command('bun',['install','--frozen-lockfile'],root,180000)
 const target=join(root,'research/lane-i/f3');mkdirSync(target,{recursive:true})
 copyFileSync('native-input/native-spans.ts',join(target,'native-spans.ts'))
 const probe=join(target,'native-canon-probe.ts');copyFileSync('native-input/native-canon-probe.source',probe)
 const run=(mode:string)=>{const text:string=command('bun',[probe,root,mode],root,120000);const line=text.split('\n').find(line=>line.startsWith('NATIVE_CANON_PROBE '));assert(line);return JSON.parse(line.slice('NATIVE_CANON_PROBE '.length))}
 const before=run('off'),instrumentation=instrumentNativeCanon(root),off=run('off'),on=run('on')
 for(const result of [off,on]){assert.deepEqual(result.results,before.results);assert.deepEqual(result.calls,before.calls);assert.deepEqual(result.raw,before.raw)}
 assert.equal(off.span.count,0);assert(on.span.count>0);assert(on.span.valid);assert.equal(on.span.id,0);assert.equal(on.span.depth,0)
 const record={passed:true,scope:'canonicalization call-boundary identity controls only; not a timed solver capture or full F3',cases:before.results.length,raw:before.raw,spans:on.span.count,instrumentation}
 writeFileSync(join(root,'native-check.json'),JSON.stringify(record))
 console.log('NATIVE_CANON_IDENTITY '+JSON.stringify(record))
}finally{rmSync(root,{recursive:true,force:true})}

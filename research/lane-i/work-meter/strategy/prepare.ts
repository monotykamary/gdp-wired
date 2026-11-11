import {strict as assert} from 'node:assert'
import {mkdtempSync,readFileSync,rmSync,appendFileSync,copyFileSync,mkdirSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {gzipSync} from 'node:zlib'
const {restore,command}=await import(resolve('recovery-input/final-gate-common.ts'))
const base='b11e1f651618b3d3fcaf6cec66b4a8b0203cdcd3',pin='aeef60912e189573eb24e658af7e915109a971d2',strategy='37d006af'
const root=mkdtempSync('/tmp/strategy-meter-merge-'),check=process.argv.includes('--check')
const partArg=process.argv.find(arg=>arg.startsWith('--export-part=')),part=partArg===undefined?undefined:Number(partArg.split('=')[1])
assert(part===undefined||(Number.isInteger(part)&&part>=0&&part<8))
try{
 restore(resolve('recovery-input'),root,base)
 const unpacked=spawnSync('git',['unpack-objects','-q'],{cwd:root,input:readFileSync('strategy-input/calibration-source.pack'),timeout:120000})
 assert.equal(unpacked.status,0,unpacked.stderr.toString())
 appendFileSync(join(root,'.git/shallow'),pin+'\n')
 command('git',['checkout','--detach',pin],root)
 assert.equal(command('git',['hash-object','core/work-ledger.ts'],root),'ed88401af1577ac0fc4e5cbb270ec305274ee3e0')
 const merged=spawnSync('git',['apply','--3way','--index',resolve('strategy-input/strategy.patch')],{cwd:root,encoding:'utf8',timeout:120000,maxBuffer:4*1024*1024})
 const conflicts=command('git',['diff','--name-only','--diff-filter=U'],root).split('\n').filter(Boolean)
 console.log('STRATEGY_MERGE_PROBE '+JSON.stringify({base,pin,strategy,exit:merged.status,conflicts,stdout:merged.stdout,stderr:merged.stderr}))
 if(!check&&part===undefined)for(const path of conflicts)console.log('STRATEGY_MERGE_CONFLICT '+JSON.stringify({path,text:readFileSync(join(root,path),'utf8')}))
 if(merged.status!==0&&!conflicts.length)throw Error('merge infrastructure error')
 if(check||part!==undefined){
  const {resolveStrategyConflicts}=await import(resolve('strategy-input/resolve.ts'))
  console.log('STRATEGY_RESOLUTIONS '+JSON.stringify(resolveStrategyConflicts(root)))
  // Lane B removed a legacy model module; retained lane A research imports still require it.
  command('git',['restore','--source='+pin,'--staged','--worktree','--','research/protocols/ic3syn/mldr.ts'],root)
  command('bun',['install','--frozen-lockfile'],root,180000)
  const tooling=join(root,'research/lane-i/strategy-tools');mkdirSync(tooling,{recursive:true})
  copyFileSync('strategy-input/instrument.ts',join(tooling,'instrument.ts'))
  copyFileSync('strategy-input/instrument-ast.ts',join(tooling,'constructors.ts'))
  copyFileSync('strategy-input/meter-fixture.source',join(tooling,'fixture.ts'))
  copyFileSync('strategy-input/path-coverage.source',join(tooling,'path-coverage.ts'))
  const {instrumentStrategies}=await import(join(tooling,'instrument.ts'))
  console.log('STRATEGY_METER_INSTRUMENTATION '+JSON.stringify(instrumentStrategies(root)))
  const prior=process.env.METER_INCREMENTAL;process.env.METER_INCREMENTAL='1'
  try{for(let pass=1;pass<=2;pass++){
   const text=command('bun',[join(tooling,'constructors.ts')],root,180000)
   const line=text.split('\n').find((line:string)=>line.startsWith('AST_CONSTRUCTOR_AUDIT '));assert(line)
   const audit=JSON.parse(line.slice('AST_CONSTRUCTOR_AUDIT '.length))
   if(pass===2)assert.equal(audit.sites,0,'incremental instrumentation must be idempotent')
   console.log('STRATEGY_CONSTRUCTORS '+JSON.stringify({pass,...audit}))
  }}finally{if(prior===undefined)delete process.env.METER_INCREMENTAL;else process.env.METER_INCREMENTAL=prior}
  const results:any[]=[],paths:any[]=[]
  if(check){
  console.log('STRATEGY_TYPECHECK '+command('bun',['run','typecheck'],root,300000))
  for(const mode of ['off','on']){
   const text=command('bun',[join(tooling,'fixture.ts'),mode],root,180000)
   const line=text.split('\n').find((line:string)=>line.startsWith('STRATEGY_METER_FIXTURE '));assert(line)
   const result=JSON.parse(line.slice('STRATEGY_METER_FIXTURE '.length));results.push(result)
   console.log('STRATEGY_FIXTURE_RESULT '+JSON.stringify({...result,events:result.events.length}))
  }
  assert.deepEqual(results[0].raw,results[1].raw);assert.deepEqual(results[0].result,results[1].result)
  for(const mode of ['off','on']){
   const text=command('bun',[join(tooling,'path-coverage.ts'),mode],root,180000)
   const line=text.split('\n').find((line:string)=>line.startsWith('PATH_COVERAGE_FIXTURE '));assert(line)
   const result=JSON.parse(line.slice('PATH_COVERAGE_FIXTURE '.length));paths.push(result)
   console.log('STRATEGY_PATH_COVERAGE '+JSON.stringify({...result,events:result.events.length}))
  }
  assert.deepEqual(paths[0].raw,paths[1].raw);assert.deepEqual(paths[0].cases,paths[1].cases)
  const tests=command('bun',['test','./core/count-strategies.test.ts','./core/count-case-compose.test.ts','./core/strategy-premises.test.ts','./core/work-ledger.test.ts','./kernel/frame-cut.test.ts'],root,300000)
  console.log('STRATEGY_SELECTED_TESTS '+tests)
  console.log('STRATEGY_SOURCE_CHECK '+command('bun',['run','lint'],root,300000))
  }
  command('git',['add','--','core','kernel','lean-kernel','scripts/test-shards.ts','research/protocols/ic3syn','research/track-m'],root)
  const patch=command('git',['diff','--cached','--binary','HEAD'],root)+'\n',raw=Buffer.from(patch),gzip=gzipSync(raw).toString('base64'),chunks=gzip.match(/.{1,12000}/g)??[]
  const receipt={passed:check,pin,strategy,ledger:command('git',['hash-object','core/work-ledger.ts'],root),sourceTree:command('git',['write-tree'],root),patchSha256:createHash('sha256').update(raw).digest('hex'),bytes:raw.length,chunks:chunks.length}
  if(part!==undefined)for(const [index,data]of chunks.entries())if(index%8===part)console.log('STRATEGY_SOURCE_CHUNK '+JSON.stringify({index,data}))
  if(check){
   const body=Buffer.from(JSON.stringify({schema:'strategy-meter-diagnostic/v1',...receipt,results,paths})),data=gzipSync(body).toString('base64')
   assert(data.length<=100000,'phase evidence requires explicit partitioning')
   console.log('STRATEGY_PHASE_DATA '+JSON.stringify({encoding:'gzip-base64',bytes:body.length,sha256:createHash('sha256').update(body).digest('hex'),data}))
  }
  console.log((check?'STRATEGY_METER_VALIDATED ':'STRATEGY_SOURCE_REBUILT ')+JSON.stringify({...receipt,part:part??null,parts:8}))
 }
 if(!conflicts.length)console.log('STRATEGY_MERGE_CLEAN '+JSON.stringify({ledger:command('git',['hash-object','core/work-ledger.ts'],root),strategy:command('git',['hash-object','core/count-strategies.ts'],root)}))
}finally{rmSync(root,{recursive:true,force:true})}

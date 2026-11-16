import {expect, test} from 'bun:test'
import {readFileSync} from 'node:fs'
import {defaultWork, installProfile, profile049, workBudget, outputFailure, writeReceipt, parseWorkerArgs, proofStatus} from './proof-worker.ts'
test('0.49 generous work profile has exact per-family defaults', () => {
  expect(defaultWork('consensus')).toBe(24_000_000_000)
  expect(defaultWork('mldr')).toBe(288_000_000_000)
  expect(workBudget(undefined, 'mldr')).toBe(defaultWork('mldr'))
  expect(workBudget('1', 'consensus')).toBe(1)
  for (const value of ['0', '-1', '1.5', 'NaN', 'Infinity', '9007199254740992', '01']) expect(() => workBudget(value, 'consensus')).toThrow()
})
test('exact flags installed before imports; inherited experimental knobs removed, unrelated environment untouched', () => {
  const env: NodeJS.ProcessEnv = {GDP_WORK_WEIGHTS: 'untrusted', GDP_WORK_STEPS: '1', JSC_useJIT: 'false', BUN_JSC_heapSize: '10', KEEP: 'yes'}
  const cleared = installProfile(env)
  expect(cleared).toEqual(['BUN_JSC_heapSize', 'GDP_WORK_STEPS', 'GDP_WORK_WEIGHTS', 'JSC_useJIT'])
  expect(env).toEqual({...profile049, KEEP: 'yes'})
  expect(Object.keys(profile049)).toHaveLength(22)
  expect(profile049.GDP_WORK_FULL).toBe('1')
  expect(profile049.GDP_WORK_STEPS).toBe('0')
})
test('post-return output failures preserve native verdicts and return a stdout fallback', () => {
  expect(outputFailure({proven:true,checked:true},Error('disk full'))).toEqual({proven:true,checked:true,outputError:'disk full'})
  const report=writeReceipt('/dev/null/receipt.json',{proven:true,checked:true,status:'not-verified'})
  expect(report.proven).toBe(true);expect(report.checked).toBe(true);expect(report.receiptWriteError).toBeDefined()
})
test('broken CLI uses the same default profile and cannot request a fanout', () => {
  expect(parseWorkerArgs(['--only','consensus','--broken'])).toEqual({id:'consensus',out:undefined,work:undefined,broken:true})
  expect(parseWorkerArgs(['--broken','--only','mldr','--out','artifact'])).toEqual({id:'mldr',out:'artifact',work:undefined,broken:true})
  expect(defaultWork(parseWorkerArgs(['--broken','--only','mldr']).id)).toBe(288_000_000_000)
  for(const args of [['--only','a,b'],['--only','a','--broken','--broken'],['--only','a','--only','b'],['--only','a','--work','0'],['--only','a','--broken','false']])expect(()=>parseWorkerArgs(args)).toThrow()
})
test('candidate manifest is explicit, single-use and separate from the work budget', () => {
  expect(parseWorkerArgs(['--only','sharded_kv','--seed-candidates','seed.json'])).toEqual({id:'sharded_kv',out:undefined,work:undefined,broken:false,seedManifest:'seed.json'})
  for(const args of [['--only','a','--seed-candidates'],['--only','a','--seed-candidates','a.json','--seed-candidates','b.json']]) expect(()=>parseWorkerArgs(args)).toThrow()
  expect(defaultWork('sharded_kv')).toBe(24_000_000_000)
})
test('model rounds are an explicit recorded opt-in, separate from the unchanged work profile',()=>{
 expect(parseWorkerArgs(['--only','sharded_kv','--model-rounds','12']).modelRounds).toBe(12)
 expect(parseWorkerArgs(['--only','sharded_kv','--model-rounds','progress']).modelRounds).toBe('progress')
 expect(parseWorkerArgs(['--only','sharded_kv']).modelRounds).toBeUndefined()
 expect(defaultWork('sharded_kv')).toBe(24_000_000_000)
 for(const value of ['-1','1.5','NaN','Infinity','9007199254740992','01'])expect(()=>parseWorkerArgs(['--only','a','--model-rounds',value])).toThrow()
 const env:NodeJS.ProcessEnv={GDP_MODEL_ROUNDS:'progress'}
 expect(installProfile(env)).toContain('GDP_MODEL_ROUNDS')
 expect(env.GDP_MODEL_ROUNDS).toBeUndefined()
})
test('a checked proof of the registered broken variant is never an accepted worker result', () => {
  const retention={complete:true,projection:{kind:'same-machine'}}
  expect(proofStatus({proven:true,checked:true},retention,true)).toBe('unexpected-broken-proof')
  expect(proofStatus({proven:false,checked:false},{complete:false},true)).toBe('not-verified')
  expect(proofStatus({proven:true,checked:true},retention,false)).toBe('captured')
  expect(proofStatus({proven:true,checked:true},{complete:true,projection:{kind:'unqualified'}},false)).toBe('captured-unqualified')
})
test('worker has one public call site, no given-helper or second-search fallback', () => {
  const source = readFileSync(new URL('./proof-worker.ts', import.meta.url), 'utf8')
  expect(source.match(/return proveRule\(/g)).toHaveLength(1)
  expect(source).not.toMatch(/\.human\s*\(|\.machine\s*[,;=]|\btoLean\s*\(|\binferLaws\s*\(/)
})

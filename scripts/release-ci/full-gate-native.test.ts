import {test, expect} from 'bun:test'
import {createHash} from 'node:crypto'
import {mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync, existsSync, symlinkSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {canonicalJobHash} from './full-gate-contract'
import {finalize} from './full-gate-native'

const sha = (s: Buffer | string) => createHash('sha256').update(s).digest('hex')
const json = (v: unknown) => JSON.stringify(v) + '\n'
function fixture(withKnownFailure = false) {
  const root = mkdtempSync(join(tmpdir(), 'native-test-')), input = join(root, 'input'), out = join(root, 'results')
  mkdirSync(input); mkdirSync(out)
  const runtime = {bun: {version: '1.4.3', sha256: 'd'.repeat(64)}}
  const suite = [{name:'one',cmd:withKnownFailure ? 'bun test inherited.test.ts' : 'true',runtime}, {name:withKnownFailure ? 'exists' : 'two',cmd:'echo ok',cwd:'scripts',runtime}], suiteBytes = json(suite)
  const policy = {schema:'gdp-known-failures/v1',baselineCommit:'c'.repeat(40),evidence:{triageSha256:'d'.repeat(64),comparisonSha256:'e'.repeat(64)},entries:[{job:'one',definitionSha256:canonicalJobHash(suite[0]!),exitCode:1,signature:{failedTests:['inherited test'],diagnostics:['error: assertion failed']}}],requiredPass:['exists']}
  if (withKnownFailure) writeFileSync(join(input, 'known-failures.json'), json(policy))
  const commit = 'a'.repeat(40), tree = 'b'.repeat(40), archive = Buffer.from('fixture archive bytes')
  writeFileSync(join(input, 'repo-0.tar'), archive)
  const manifest = {commit, tree, suiteSha256:sha(suiteBytes), repositories:[{path:'.',commit,tree,archive:'repo-0.tar',archiveSha256:sha(archive)}], definitions:Object.fromEntries(suite.map(j => [j.name, canonicalJobHash(j)])), ...(withKnownFailure ? {knownFailuresSha256:sha(json(policy))} : {})}
  const manifestBytes = json(manifest)
  writeFileSync(join(input, 'manifest.json'), manifestBytes); writeFileSync(join(input, 'canonical-suite.json'), suiteBytes)
  const rows: Record<string, any> = {}, attempts: any[] = []
  for (const job of suite) {
    const dir = join(out, job.name + '.files'); mkdirSync(dir)
    const files: Record<string, string> = {'PROVISIONED.json':json({commit,tree,suiteSha256:manifest.suiteSha256,provisioningSha256:sha(manifestBytes),vendorPins:{},definitionSha256:manifest.definitions[job.name]}), 'COMMAND-RESULT.json':json({name:job.name,command:job.cmd,cwd:job.cwd ?? '.',code:0,signal:null,error:null}), 'stdout.log':'hello\n','stderr.log':''}
    if (withKnownFailure) {
      files['LEAN-DIAGNOSTICS.json'] = json({schema:'gdp-lean-diagnostics/v1',logs:[]})
      if (job.name === 'one') {
        files['stderr.log'] = 'error: assertion failed\n(fail) inherited test [1ms]\n 1 fail\n'
        files['COMMAND-RESULT.json'] = json({name:job.name,command:job.cmd,cwd:job.cwd ?? '.',code:1,signal:null,error:null})
      }
    }
    const entries = Object.entries(files).map(([path, data]) => {writeFileSync(join(dir,path), data); return {path,version:1,sha256:sha(data),bytes:Buffer.byteLength(data),format:'file'}})
    const payload = json(entries), payloadPath = join(out, job.name+'.payload'); writeFileSync(payloadPath,payload)
    const launch = 'launch-'+job.name
    rows[job.name] = {name:job.name,run_name:job.name,batch:'batch',vm:'vm',boot_id:'boot',attempt:1,attempts:1,max_attempts:1,strict_once:true,terminal:true,launch_identity:launch,runtime_verified:true,runtime_verification:{ok:true,required:structuredClone(runtime)},status:withKnownFailure && job.name === 'one' ? 'FAILED' : 'SUCCEEDED',code:withKnownFailure && job.name === 'one' ? 1 : 0,output_files_ref:{version:1,format:'json',bytes:Buffer.byteLength(payload),sha256:sha(payload)},output_files_manifest:payloadPath,output_files_dir:dir}
    attempts.push({name:job.name,run_name:job.name,vm:'vm',boot_id:'boot',attempt:1,launch_identity:launch,cleanup_complete:true})
  }
  const results = {rows,cleanup:{image:'sc-real',cleanup_complete:true,cleanup_validation:{batch:true},batches:{batch:{batch:'batch',ok:true,complete:true,cleanup_complete:true,admission_closed:true,journals_retained:true,strict_once:true,max_attempts:1,attempts,pending:[] as string[],unlaunched:[] as string[]}}}}
  const pin = {ok:true,pin:{protected:true,images:['sc-real'],ref:'packet:release-123',protected_until:Date.now()/1000+3600}}
  const resultsPath = join(out,'results.json'), pinPath = join(root,'pin.json'), receiptPath = join(root,'receipt.json')
  const save = () => {writeFileSync(resultsPath,json(results)); writeFileSync(pinPath,json(pin))}
  save()
  const replaceArtifact = (name: string, artifact: string, data: string | null) => {
    const row = results.rows[name], payloadPath = row.output_files_manifest
    let entries = JSON.parse(readFileSync(payloadPath, 'utf8')) as {path:string,version:number,sha256:string,bytes:number,format:string}[]
    const path = join(row.output_files_dir, artifact)
    if (data === null) { rmSync(path); entries = entries.filter(entry => entry.path !== artifact) }
    else {
      writeFileSync(path, data)
      const entry = entries.find(item => item.path === artifact)
      if (!entry) throw Error('fixture artifact missing')
      entry.bytes = Buffer.byteLength(data); entry.sha256 = sha(data)
    }
    const payload = json(entries); writeFileSync(payloadPath, payload)
    row.output_files_ref = {version:1,format:'json',bytes:Buffer.byteLength(payload),sha256:sha(payload)}
  }
  return {root,input,out,results,pin,resultsPath,pinPath,receiptPath,save,replaceArtifact,run:() => finalize(input,resultsPath,pinPath,receiptPath)}
}
test('valid multi-job native receipt and exclusive write', () => {const f=fixture(); try {const summary=f.run(); expect(summary.cleanupComplete).toBe(true); expect(summary.receipt.jobs.length).toBe(2); expect(JSON.parse(readFileSync(f.receiptPath,'utf8'))).toEqual(summary.receipt); expect(() => f.run()).toThrow()} finally {rmSync(f.root,{recursive:true,force:true})}})
test('authenticated known failure remains natively FAILED, alongside required exists success', () => {
  const f = fixture(true)
  try {
    const summary = f.run()
    expect(summary.counts).toEqual({succeeded:1,knownFailures:1,total:2})
    expect(summary.knownFailures.map(job => job.name)).toEqual(['one'])
    expect(summary.receipt.jobs.find(job => job.name === 'one')?.status).toBe('FAILED')
    expect(f.results.rows.one.status).toBe('FAILED')
    expect(f.results.rows.one.code).toBe(1)
    expect(summary.cleanupComplete).toBe(true)
  } finally {rmSync(f.root,{recursive:true,force:true})}
})
for (const [name, mutate] of Object.entries({
  'an additional failed test': (f: ReturnType<typeof fixture>) => {f.replaceArtifact('one','stderr.log','error: assertion failed\n(fail) inherited test [1ms]\nerror: new\n(fail) new test [2ms]\n 2 fail\n')},
  'changed diagnostic': (f: ReturnType<typeof fixture>) => {f.replaceArtifact('one','stderr.log','error: changed\n(fail) inherited test [1ms]\n 1 fail\n')},
  'an unrecorded compiler failure': (f: ReturnType<typeof fixture>) => {f.replaceArtifact('one','LEAN-DIAGNOSTICS.json',json({schema:'gdp-lean-diagnostics/v1',logs:['Proofs.lean:1:1: error: new failure\n']}))},
  'missing diagnostic artifact': (f: ReturnType<typeof fixture>) => {f.replaceArtifact('one','LEAN-DIAGNOSTICS.json',null)},
  'failed required exists': (f: ReturnType<typeof fixture>) => {
    f.results.rows.exists.status='FAILED'; f.results.rows.exists.code=1
    const command = JSON.parse(readFileSync(join(f.out,'exists.files','COMMAND-RESULT.json'),'utf8')); command.code=1
    f.replaceArtifact('exists','COMMAND-RESULT.json',json(command))
  },
})) test(`known-failure policy still rejects ${name}`, () => {
  const f = fixture(true)
  try {mutate(f); f.save(); expect(() => f.run()).toThrow(); expect(existsSync(f.receiptPath)).toBe(false)}
  finally {rmSync(f.root,{recursive:true,force:true})}
})

for (const [name, mutate] of Object.entries({
  'missing job': (f: ReturnType<typeof fixture>) => {delete f.results.rows.two},
  'tampered archive': (f: ReturnType<typeof fixture>) => {writeFileSync(join(f.input, 'repo-0.tar'), 'changed')},
  'wrong policy hash': (f: ReturnType<typeof fixture>) => {const path=join(f.input,'manifest.json'), manifest=JSON.parse(readFileSync(path,'utf8')); manifest.knownFailuresSha256='0'.repeat(64); writeFileSync(path,json(manifest)); writeFileSync(join(f.input,'known-failures.json'),'{}')},
  'extra cleanup attempt': (f: ReturnType<typeof fixture>) => {f.results.cleanup.batches.batch.attempts.push({name:'extra',run_name:'extra',vm:'vm',boot_id:'boot',attempt:1,launch_identity:'extra',cleanup_complete:false})},
  'pending cleanup': (f: ReturnType<typeof fixture>) => {f.results.cleanup.batches.batch.pending.push('one')},
  'bad payload hash': (f: ReturnType<typeof fixture>) => {f.results.rows.one.output_files_ref.sha256='0'.repeat(64)},
  'tampered stdout': (f: ReturnType<typeof fixture>) => {writeFileSync(join(f.out,'one.files','stdout.log'),'tampered')},
  'unprotected pin': (f: ReturnType<typeof fixture>) => {f.pin.pin.protected=false},
  'wrong image': (f: ReturnType<typeof fixture>) => {f.pin.pin.images=['different']},
  'wrong cleanup identity': (f: ReturnType<typeof fixture>) => {f.results.cleanup.batches.batch.attempts[0].launch_identity='wrong'},
  'failed job without policy': (f: ReturnType<typeof fixture>) => {f.results.rows.one.status='FAILED'; f.results.rows.one.code=1},
  'missing runtime verification': (f: ReturnType<typeof fixture>) => {delete f.results.rows.one.runtime_verification},
  'wrong runtime binding': (f: ReturnType<typeof fixture>) => {f.results.rows.one.runtime_verification.required.bun.sha256='0'.repeat(64)},
  'duplicate launch': (f: ReturnType<typeof fixture>) => {f.results.rows.two.launch_identity=f.results.rows.one.launch_identity},
  'symlink artifact': (f: ReturnType<typeof fixture>) => {const p=join(f.out,'one.files','stdout.log'); rmSync(p); symlinkSync(join(f.out,'two.files','stdout.log'),p)},
})) test(`rejects ${name} without writing`, () => {const f=fixture(); try {mutate(f); f.save(); expect(() => f.run()).toThrow(); expect(existsSync(f.receiptPath)).toBe(false)} finally {rmSync(f.root,{recursive:true,force:true})}})

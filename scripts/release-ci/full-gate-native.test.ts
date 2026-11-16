import {test, expect} from 'bun:test'
import {createHash} from 'node:crypto'
import {mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync, existsSync, symlinkSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {canonicalJobHash} from './full-gate-contract'
import {finalize} from './full-gate-native'

const sha = (s: Buffer | string) => createHash('sha256').update(s).digest('hex')
const json = (v: unknown) => JSON.stringify(v) + '\n'
function fixture() {
  const root = mkdtempSync(join(tmpdir(), 'native-test-')), input = join(root, 'input'), out = join(root, 'results')
  mkdirSync(input); mkdirSync(out)
  const runtime = {bun: {version: '1.4.3', sha256: 'd'.repeat(64)}}
  const suite = [{name:'one',cmd:'true',runtime}, {name:'two',cmd:'echo ok',cwd:'scripts',runtime}], suiteBytes = json(suite)
  const commit = 'a'.repeat(40), tree = 'b'.repeat(40), archive = Buffer.from('fixture archive bytes')
  writeFileSync(join(input, 'repo-0.tar'), archive)
  const manifest = {commit, tree, suiteSha256:sha(suiteBytes), repositories:[{path:'.',commit,tree,archive:'repo-0.tar',archiveSha256:sha(archive)}], definitions:Object.fromEntries(suite.map(j => [j.name, canonicalJobHash(j)]))}
  const manifestBytes = json(manifest)
  writeFileSync(join(input, 'manifest.json'), manifestBytes); writeFileSync(join(input, 'canonical-suite.json'), suiteBytes)
  const rows: Record<string, any> = {}, attempts: any[] = []
  for (const job of suite) {
    const dir = join(out, job.name + '.files'); mkdirSync(dir)
    const files: Record<string, string> = {'PROVISIONED.json':json({commit,tree,suiteSha256:manifest.suiteSha256,provisioningSha256:sha(manifestBytes),vendorPins:{},definitionSha256:manifest.definitions[job.name]}), 'COMMAND-RESULT.json':json({name:job.name,command:job.cmd,cwd:job.cwd ?? '.',code:0,signal:null,error:null}), 'stdout.log':'hello\n','stderr.log':''}
    const entries = Object.entries(files).map(([path, data]) => {writeFileSync(join(dir,path), data); return {path,version:1,sha256:sha(data),bytes:Buffer.byteLength(data),format:'file'}})
    const payload = json(entries), payloadPath = join(out, job.name+'.payload'); writeFileSync(payloadPath,payload)
    const launch = 'launch-'+job.name
    rows[job.name] = {name:job.name,run_name:job.name,batch:'batch',vm:'vm',boot_id:'boot',attempt:1,attempts:1,max_attempts:1,strict_once:true,terminal:true,launch_identity:launch,runtime_verified:true,runtime_verification:{ok:true,required:structuredClone(runtime)},status:'SUCCEEDED',code:0,output_files_ref:{version:1,format:'json',bytes:Buffer.byteLength(payload),sha256:sha(payload)},output_files_manifest:payloadPath,output_files_dir:dir}
    attempts.push({name:job.name,run_name:job.name,vm:'vm',boot_id:'boot',attempt:1,launch_identity:launch,cleanup_complete:true})
  }
  const results = {rows,cleanup:{image:'sc-real',cleanup_complete:true,cleanup_validation:{batch:true},batches:{batch:{batch:'batch',ok:true,complete:true,cleanup_complete:true,admission_closed:true,journals_retained:true,strict_once:true,max_attempts:1,attempts,pending:[] as string[],unlaunched:[] as string[]}}}}
  const pin = {ok:true,pin:{protected:true,images:['sc-real'],ref:'packet:release-123',protected_until:Date.now()/1000+3600}}
  const resultsPath = join(out,'results.json'), pinPath = join(root,'pin.json'), receiptPath = join(root,'receipt.json')
  const save = () => {writeFileSync(resultsPath,json(results)); writeFileSync(pinPath,json(pin))}
  save()
  return {root,input,out,results,pin,resultsPath,pinPath,receiptPath,save,run:() => finalize(input,resultsPath,pinPath,receiptPath)}
}
test('valid multi-job native receipt and exclusive write', () => {const f=fixture(); try {const summary=f.run(); expect(summary.cleanupComplete).toBe(true); expect(summary.receipt.jobs.length).toBe(2); expect(JSON.parse(readFileSync(f.receiptPath,'utf8'))).toEqual(summary.receipt); expect(() => f.run()).toThrow()} finally {rmSync(f.root,{recursive:true,force:true})}})
for (const [name, mutate] of Object.entries({
  'missing job': (f: ReturnType<typeof fixture>) => {delete f.results.rows.two},
  'tampered archive': (f: ReturnType<typeof fixture>) => {writeFileSync(join(f.input, 'repo-0.tar'), 'changed')},
  'extra cleanup attempt': (f: ReturnType<typeof fixture>) => {f.results.cleanup.batches.batch.attempts.push({name:'extra',run_name:'extra',vm:'vm',boot_id:'boot',attempt:1,launch_identity:'extra',cleanup_complete:false})},
  'pending cleanup': (f: ReturnType<typeof fixture>) => {f.results.cleanup.batches.batch.pending.push('one')},
  'bad payload hash': (f: ReturnType<typeof fixture>) => {f.results.rows.one.output_files_ref.sha256='0'.repeat(64)},
  'tampered stdout': (f: ReturnType<typeof fixture>) => {writeFileSync(join(f.out,'one.files','stdout.log'),'tampered')},
  'unprotected pin': (f: ReturnType<typeof fixture>) => {f.pin.pin.protected=false},
  'wrong image': (f: ReturnType<typeof fixture>) => {f.pin.pin.images=['different']},
  'wrong cleanup identity': (f: ReturnType<typeof fixture>) => {f.results.cleanup.batches.batch.attempts[0].launch_identity='wrong'},
  'failed job': (f: ReturnType<typeof fixture>) => {f.results.rows.one.status='FAILED'},
  'missing runtime verification': (f: ReturnType<typeof fixture>) => {delete f.results.rows.one.runtime_verification},
  'wrong runtime binding': (f: ReturnType<typeof fixture>) => {f.results.rows.one.runtime_verification.required.bun.sha256='0'.repeat(64)},
  'duplicate launch': (f: ReturnType<typeof fixture>) => {f.results.rows.two.launch_identity=f.results.rows.one.launch_identity},
  'symlink artifact': (f: ReturnType<typeof fixture>) => {const p=join(f.out,'one.files','stdout.log'); rmSync(p); symlinkSync(join(f.out,'two.files','stdout.log'),p)},
})) test(`rejects ${name} without writing`, () => {const f=fixture(); try {mutate(f); f.save(); expect(() => f.run()).toThrow(); expect(existsSync(f.receiptPath)).toBe(false)} finally {rmSync(f.root,{recursive:true,force:true})}})

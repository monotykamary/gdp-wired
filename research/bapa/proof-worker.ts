// Native ONE-protocol worker. Run only inside a bounded supercomputer job.
// No trusted/given helpers, no second public search, no exporter during search.
// Optional retained candidates enter whole-family Houdini and are rechecked.
import {createHash, randomUUID} from 'node:crypto'
import {mkdirSync, readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {dirname, join, resolve} from 'node:path'
import {fileURLToPath} from 'node:url'
import type {CaptureIdentity} from './proof-capture.ts'

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..')
const profilePath = new URL('./profile-049.json', import.meta.url)
export const profile049 = JSON.parse(readFileSync(profilePath, 'utf8')) as Record<string, string>
const hash = (value: string | Uint8Array) => createHash('sha256').update(value).digest('hex')
const relevant = (key: string) => key.startsWith('GDP_') || key.startsWith('BUN_JSC_') || key.startsWith('JSC_')
export const defaultWork = (id: string): number => id === 'mldr' ? 288_000_000_000 : 24_000_000_000
export function workBudget(value: string | undefined, id: string): number {
  if (value !== undefined && !/^[1-9][0-9]*$/.test(value)) throw Error('work must be a positive safe integer')
  const n = value === undefined ? defaultWork(id) : Number(value)
  if (!Number.isSafeInteger(n) || n <= 0) throw Error('work must be a positive safe integer')
  return n
}
export function installProfile(env: NodeJS.ProcessEnv): string[] {
  // Modules snapshot GDP/JSC knobs on import. Clear inherited experimental knobs
  // BEFORE dynamic imports, and never print their values (or other environment).
  const cleared = Object.keys(env).filter(relevant).sort()
  for (const key of cleared) delete env[key]
  Object.assign(env, profile049)
  return cleared
}
function sourceManifest(): Record<string, string> {
  const files: Record<string, string> = {}
  const walk = (rel: string) => {
    for (const entry of readdirSync(join(root, rel), {withFileTypes: true}).sort((a, b) => a.name.localeCompare(b.name))) {
      const path = `${rel}/${entry.name}`
      if (entry.isDirectory()) walk(path)
      else if (entry.isFile() && /\.(?:ts|json)$/.test(entry.name)) files[path] = hash(readFileSync(join(root, path)))
    }
  }
  for (const path of ['core', 'kernel', 'research/bapa', 'research/protocols']) walk(path)
  return files
}
// Output errors never revoke the already returned native verdict.
export function outputFailure(verdict:{proven:boolean,checked:boolean}|undefined,error:unknown) {
  return {proven:verdict?.proven??false,checked:verdict?.checked??false,outputError:error instanceof Error?error.message:String(error)}
}
export function writeReceipt(path:string,report:Record<string,unknown>):Record<string,unknown> {
  try {writeFileSync(path,JSON.stringify(report,null,2)+'\n');return report}
  catch(error) {return {...report,status:'not-verified',receiptWriteError:error instanceof Error?error.message:String(error)}}
}
export function workerModelRounds(value: string | undefined): number | 'progress' | undefined {
  if (value === undefined || value === 'progress') return value
  const n = /^(0|[1-9][0-9]*)$/.test(value) ? Number(value) : NaN
  if (!Number.isSafeInteger(n)) throw Error('model rounds must be a nonnegative safe integer or progress')
  return n
}
export type WorkerOptions = {id: string, out: string, work?: string, broken?: boolean, seedManifest?: string, modelRounds?: number|'progress', sourceCommit: string, sourceTree: string}
export function proofStatus(verdict:{proven:boolean,checked:boolean}, retention:{complete:boolean,projection?:{kind:string}}, broken:boolean):string {
  if (broken && verdict.proven && verdict.checked) return 'unexpected-broken-proof'
  if (!verdict.proven || !verdict.checked || !retention.complete) return 'not-verified'
  return retention.projection?.kind === 'same-machine' ? 'captured' : 'captured-unqualified'
}
export function parseWorkerArgs(args:string[]):{id:string,out?:string,work?:string,broken:boolean,seedManifest?:string,modelRounds?:number|'progress'} {
  const known=new Set(['--only','--out','--work','--seed-candidates','--model-rounds']), values:Record<string,string>={}
  let broken=false
  for(let i=0;i<args.length;){
    const key=args[i++]!
    if(key==='--broken'){if(broken)throw Error('duplicate --broken');broken=true;continue}
    const value=args[i++]
    if(!known.has(key)||values[key]!==undefined||!value||value.startsWith('--'))throw Error('usage: proof-worker.ts --only ID [--out NEW_DIR] [--work DIAGNOSTIC_UNITS] [--broken] [--seed-candidates MANIFEST] [--model-rounds N|progress]')
    values[key]=value
  }
  const id=values['--only']
  if(!id||!/^[a-z][a-z0-9_]*$/.test(id))throw Error('one exact --only ID required; no fanout')
  workBudget(values['--work'],id)
  const modelRounds=workerModelRounds(values['--model-rounds'])
  return {id,out:values['--out'],work:values['--work'],broken,...(modelRounds === undefined ? {} : {modelRounds}),...(values['--seed-candidates'] ? {seedManifest:values['--seed-candidates']} : {})}
}
export async function runProofWorker(options: WorkerOptions): Promise<Record<string, unknown>> {
  if (!/^[a-z][a-z0-9_]*$/.test(options.id)) throw Error('one exact protocol ID required')
  if (options.broken !== undefined && typeof options.broken !== 'boolean') throw Error('broken must be boolean')
  for (const key of ['sourceCommit', 'sourceTree'] as const)
    if (!/^[0-9a-f]{40}$/.test(options[key])) throw Error(`launcher must supply ${key}`)
  const units = workBudget(options.work, options.id)
  const modelRounds = workerModelRounds(options.modelRounds === undefined ? undefined : String(options.modelRounds))
  mkdirSync(options.out, {recursive: false})
  const started = Date.now(), invocation = randomUUID()
  let cleared: string[] = [], returned: {proven:boolean,checked:boolean} | undefined
  let seedHash:string|undefined, seedSummary:Record<string,unknown>|undefined
  const nativeSeedAudits:unknown[] = []
  const receipt = (result: Record<string, unknown>) => {
    const report = {schema: 'bapa-search/v1', protocol: options.id, invocation, variant: options.broken ? 'broken' : 'positive',
      sourceReference: {commit: options.sourceCommit, tree: options.sourceTree, assurance: 'launcher-supplied; content manifest retained'},
      profile: modelRounds !== undefined ? '0.49-flags-model-rounds-override' : options.work === undefined ? '0.49-generous' : '0.49-flags-diagnostic-work-override',
      ...(modelRounds === undefined ? {} : {modelRounds}),
      workBudget: String(units), elapsedMs: Date.now() - started, clearedFlagNames: cleared,
      publicCalls: 1, givenHelpers: false, secondSearch: false,
      ...(seedHash ? {candidateSeeding:{manifestSha256:seedHash,...seedSummary,native:nativeSeedAudits}} : {}),
      leanExecuted: false, allSizesProven: false, sizeClaim: 'as encoded; not qualified by this worker', ...result}
    return writeReceipt(join(options.out, 'result.json'), report)
  }
  let publicCalls = 0
  try {
    cleared = installProfile(process.env)
    if (Bun.version !== '1.4.3') throw Error('worker requires Bun 1.4.3')
    const runtimeSha256 = hash(readFileSync(process.execPath))
    if (runtimeSha256 !== '7ce7d6b654eddeec20afddf2396317fba6dc19ab52788a27e894e1806bf8f24b') throw Error('worker Bun executable does not match the 0.49 runtime pin')
    const sources = sourceManifest()
    if(options.seedManifest) seedHash = hash(readFileSync(options.seedManifest))
    writeFileSync(join(options.out, 'source-files.json'), JSON.stringify(sources, null, 2) + '\n')
    const identity: CaptureIdentity = {protocol: options.id, invocation, sourceCommit: options.sourceCommit, sourceTree: options.sourceTree,
      driverSha256: hash(readFileSync(fileURLToPath(import.meta.url))), inputSha256: hash(JSON.stringify({id: options.id, variant: options.broken ? 'broken' : 'positive', sources,...(modelRounds === undefined ? {} : {modelRounds}),...(seedHash ? {candidateSeedSha256:seedHash} : {})})),
      runtimeSha256, profileSha256: hash(readFileSync(profilePath)), workBudget: String(units), flags: {...profile049}}
    writeFileSync(join(options.out, 'identity.json'), JSON.stringify(identity, null, 2) + '\n')
    // NOTHING from core/kernel/registry is imported before installProfile.
    const [{protocols}, {proveRule}, {captureFinalInvocation}, {workAdmissionSnapshot}] = await Promise.all([
      import('../protocols/ic3syn/models.ts'), import('../../core/dsl.ts'),
      import('./proof-capture-native.ts'), import('../../core/work-admission.ts'),
    ])
    const matches = protocols.filter(p => p.id === options.id)
    if (matches.length !== 1) throw Error(`expected one registered protocol: ${options.id}`)
    const p = matches[0]!
    if (options.broken && !p.bug) throw Error('registered broken variant is missing')
    const r = p.make(options.broken ? p.bug : undefined), laws = p.laws(r)
    let candidateSeeds:import('../../core/dsl.ts').ProveOptions['candidateSeeds']
    if(options.seedManifest) {
      // Candidate restatement may inspect a materialization; it never supplies
      // the authoritative source machine. Capture still uses the public event.
      const {loadCandidateSeedManifest} = await import('./candidate-seed-manifest.ts')
      const candidateTarget = r.machine
      const seeded = loadCandidateSeedManifest(options.seedManifest,candidateTarget,{kindLaws:r.kindLaws(),publicLaws:laws})
      if(seeded.audit.protocol !== options.id || seeded.audit.manifestSha256 !== seedHash) throw Error('candidate manifest identity mismatch')
      writeFileSync(join(options.out,'candidate-restatement.json'),JSON.stringify(seeded.audit,null,2)+'\n')
      writeFileSync(join(options.out,'candidate-proposals.json'),JSON.stringify({laws:seeded.laws,...(seeded.kind==='usual'?{witnesses:seeded.witnesses,ghosts:seeded.ghosts}:{counts:seeded.counts})},null,2)+'\n')
      seedSummary = {protocol:seeded.audit.protocol,captureSha256:seeded.audit.captureSha256,
        proposed:seeded.laws.length,dropped:seeded.audit.laws.filter(l=>l.status==='dropped').length}
      candidateSeeds = {kind:seeded.kind,laws:seeded.laws,...(seeded.kind === 'counted' ? {counts:seeded.counts} : {witnesses:seeded.witnesses,ghosts:seeded.ghosts}),report:audit=>nativeSeedAudits.push(audit)}
    }
    // Without candidates, do not materialize before the public call.
    // Recover the authoritative machine only through proveRule's output event.
    const before = workAdmissionSnapshot()
    const captured = captureFinalInvocation(join(options.out, 'closure'), identity, {laws}, () => {
      publicCalls++
      return proveRule(r, laws, {search: {work: units},...(modelRounds === undefined ? {} : {modelRounds}),...(candidateSeeds ? {candidateSeeds} : {})})
    })
    returned = captured.verdict
    const after = workAdmissionSnapshot()
    const deltas = Object.fromEntries(Object.entries(after.counters).map(([key, value]) => [key, String(BigInt(value) - BigInt(before.counters[key as keyof typeof before.counters]))]))
    writeFileSync(join(options.out, 'work.json'), JSON.stringify({before, after, counterDeltas: deltas}, null, 2) + '\n')
    writeFileSync(join(options.out, 'verdict.json'), JSON.stringify(captured.verdict, null, 2) + '\n')
    const status = proofStatus(captured.verdict, captured.retention, options.broken ?? false)
    return receipt({status,
      publicCalls, proven: captured.verdict.proven, checked: captured.verdict.checked, retention: captured.retention,
      safety: p.safety, source: p.source, publicLawNames: laws.map(l => l.name)})
  } catch (error) {
    return receipt({status: 'not-verified', publicCalls, ...outputFailure(returned, error)})
  }
}

if (import.meta.main) {
  const args = parseWorkerArgs(process.argv.slice(2))
  const out = args.out ?? (process.env.SUPERCOMPUTER_OUTPUT_DIR ? join(process.env.SUPERCOMPUTER_OUTPUT_DIR, args.id + (args.broken ? '-broken' : '')) : undefined)
  if (!out) throw Error('provide --out NEW_DIR or SUPERCOMPUTER_OUTPUT_DIR')
  const result = await runProofWorker({...args, out, sourceCommit: process.env.BAPA_SOURCE_COMMIT ?? '', sourceTree: process.env.BAPA_SOURCE_TREE ?? ''})
  console.log(JSON.stringify(result))
  if (result.status !== 'captured') process.exitCode = result.status === 'captured-unqualified' ? 2 : 1
}

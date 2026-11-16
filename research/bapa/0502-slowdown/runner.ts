import {createHash} from 'node:crypto'
import {mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {spawnSync} from 'node:child_process'
import {check} from '../../../core/cli.ts'

type BinderMetrics = {calls:number, collectVisits:number, generated:number, groups:number, generatedParts:number, collisionGroups:number, collisionAttempts:number, rewriteVisits:number}
type Observation = Record<string, unknown>
const now = () => performance.now()
const sha = (p: string) => createHash('sha256').update(readFileSync(p)).digest('hex')
const outDir = process.env.SLOWDOWN_OUTPUT ?? process.argv[5] ?? '.'
const mode = process.argv[2]
const label = process.argv[3] ?? 'unknown'
const phase = process.argv[4] ?? 'timing'
if (!mode || !label) throw Error('usage: bun runner.ts <policy|exists|count-policy> <label> <timing|counts> [out-dir]')

const emit = (x: Observation) => {
  mkdirSync(outDir, {recursive: true})
  const line = JSON.stringify(x)
  writeFileSync(join(outDir, 'observations.jsonl'), line + '\n', {flag: 'a'})
  console.log('SLOWDOWN_OBSERVATION ' + line)
}
const testFile = (caseId: string) => caseId === 'policy' ? 'research/security/policy-identity.test.ts' : 'core/exists-support.test.ts'
const target = (caseId: string) => caseId === 'policy'
  ? 'owned source policy identity cannot be renamed or weakened into a repair'
  : 'co-write provenance closes a renamed forwarding pipeline with nothing written'
const fixture = (name: string, guarded: boolean) => `public class OwnedPolicy {
  public int value = 0;
  public boolean guarded;
  public OwnedPolicy() { guarded = ${guarded}; }
  // gdp: law ${name}: value != old(value) implies allowed
  public void hit(boolean allowed) { if (guarded && !allowed) return; value++; }
}`
const binder = (): BinderMetrics | undefined => (globalThis as unknown as {__GDP_SLOWDOWN_BINDERS__?: BinderMetrics}).__GDP_SLOWDOWN_BINDERS__
const resetBinder = () => { (globalThis as unknown as {__GDP_SLOWDOWN_BINDERS__?: BinderMetrics}).__GDP_SLOWDOWN_BINDERS__ = {calls:0, collectVisits:0, generated:0, groups:0, generatedParts:0, collisionGroups:0, collisionAttempts:0, rewriteVisits:0} }

async function directPolicy(): Promise<Observation> {
  const root = mkdtempSync(join(tmpdir(), 'gdp-slowdown-policy-'))
  const file = join(root, 'OwnedPolicy.java')
  try {
    // Match the test's real first two calls: its original control warms extractor/prover
    // state, then its renamed policy is the critical check whose law.ms is compared.
    let ioWriteMs = 0
    let ioStart = now(); writeFileSync(file, fixture('only allowed changes', false)); ioWriteMs += now() - ioStart
    const warmStart = now()
    const warm = await check([file], {entry: 'OwnedPolicy', methods: ['hit'], propose: false, ms: 3000, check: {runs: 10, depth: 6, states: 20}})
    const warmupCheckWallMs = now() - warmStart
    const warmLaw = warm.rules[0]?.laws[0]
    if (!warmLaw || warmLaw.name !== 'only allowed changes') throw Error('policy warmup did not yield the exact original law')
    ioStart = now(); writeFileSync(file, fixture('renamed allowed changes', true)); ioWriteMs += now() - ioStart
    resetBinder()
    const start = now()
    const result = await check([file], {entry: 'OwnedPolicy', methods: ['hit'], propose: false, ms: 3000, check: {runs: 10, depth: 6, states: 20}})
    const checkWallMs = now() - start
    const law = result.rules[0]?.laws[0]
    if (!law || law.name !== 'renamed allowed changes' || law.expr !== 'value != old(value) implies allowed') throw Error('direct policy fixture did not yield the exact renamed law')
    if (!law.kernelProven || law.verdict !== 'unknown' || law.translation !== 'unchecked') throw Error('direct policy fixture changed the expected checked-but-source-unknown verdict')
    if (typeof law.ms !== 'number') throw Error('direct policy fixture did not expose raw law.ms')
    return {direct: {ioWriteMs, warmupCheckWallMs, warmupLawMs: warmLaw.ms, checkWallMs, lawMs: law.ms, loweringRenamingResidualMs: checkWallMs - law.ms, exit: result.exit, verdict: law.verdict, translation: law.translation, kernelProven: law.kernelProven, binder: binder()}}
  } finally { rmSync(root, {recursive: true, force: true}) }
}
function whole(caseId: string): Observation {
  const start = now()
  const child = spawnSync(process.execPath, ['test', testFile(caseId), '--test-name-pattern', `^${target(caseId)}$`], {encoding: 'utf8', timeout: caseId === 'policy' ? 120_000 : 90_000})
  const processWallMs = now() - start
  const stdout = child.stdout ?? '', stderr = child.stderr ?? '', combined = stdout + '\n' + stderr
  const passLine = combined.split('\n').find(line => line.includes('(pass)') && line.includes(target(caseId)))
  const hit = passLine ? /\[([0-9.]+)ms\]/.exec(passLine) : null
  const testMs = hit ? Number(hit[1]) : undefined
  const logStem = `${label}-${caseId}-${phase}`
  writeFileSync(join(outDir, `${logStem}.stdout.log`), stdout)
  writeFileSync(join(outDir, `${logStem}.stderr.log`), stderr)
  return {whole: {processWallMs, testMs, status: child.status, signal: child.signal, matchedPassLine: passLine ?? null, stdoutFile: `${logStem}.stdout.log`, stderrFile: `${logStem}.stderr.log`}}
}

const head = spawnSync('git', ['rev-parse', 'HEAD'], {encoding: 'utf8'}).stdout.trim()
const common = {schema: 'gdp-0502-slowdown-observation/v1', label, phase, head, bun: process.versions.bun, case: mode === 'exists' ? 'co-write-provenance' : 'policy-identity-renamed', testFile: testFile(mode === 'exists' ? 'exists' : 'policy'), testFileSha256: sha(testFile(mode === 'exists' ? 'exists' : 'policy')), internalBudgetMs: mode === 'exists' ? (head.startsWith('70b660443') ? 65000 : 60000) : (head.startsWith('70b660443') ? 7000 : 3000)}
if (mode === 'policy') {
  const direct = await directPolicy(); const full = whole('policy')
  if ((full.whole as {status:number | null}).status !== 0) throw Error(`policy assertion failed; retained ${JSON.stringify(full)}`)
  emit({...common, ...direct, ...full})
} else if (mode === 'exists') {
  const full = whole('exists')
  if ((full.whole as {status:number | null}).status !== 0) throw Error(`co-write assertion failed; retained ${JSON.stringify(full)}`)
  emit({...common, ...full})
} else if (mode === 'count-policy') {
  const direct = await directPolicy()
  emit({...common, ...direct})
} else throw Error(`unknown mode ${mode}`)

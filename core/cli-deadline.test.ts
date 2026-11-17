// Isolated deadline diagnostics: instrumentation only touches a temporary worker
// copy. Production clocks, proof acceptance and the checked source are unchanged.
import {expect, test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {check} from './cli.ts'
import {counted, clock, fullRate, wallDeadline, withDeadline, withWall} from '../kernel/prove.ts'
import {checkWall, WallExpired} from './wall.ts'
import {stoppedSearch, terminationWhy} from './search-termination.ts'

const hash = (s: string) => createHash('sha256').update(s).digest('hex')
const cleanEnv = () => Object.fromEntries(Object.entries(process.env).filter(([k]) => !k.startsWith('GDP_WORK_') && k !== 'GDP_STEP_WORK'))
const caught = (run: () => void) => { try { run() } catch (e) { if (e instanceof WallExpired) return e; throw e } return undefined }

test('cancellation provenance uses the captured clock domain, not WallExpired or text', () => {
  const real = caught(() => withWall(wallDeadline(performance.now() - 1, 'real'), () => checkWall('real control')))
  expect(real?.termination).toEqual({kind: 'wall-deadline', phase: 'real control', scope: 'search'})
  counted(fullRate, () => {
    // A real scheduling pause cannot consume a counted stage's allowance.
    withDeadline(clock() + 1, () => {
      Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 20)
      expect(caught(() => checkWall('counted pause'))).toBeUndefined()
    })
    const work = caught(() => withDeadline(clock() - 1, () => checkWall('counted control')))
    expect(work?.termination).toEqual({kind: 'work-exhausted', phase: 'counted control', scope: 'stage'})
    expect(terminationWhy(work!.termination!)).not.toContain('wall deadline')
  }, true)
  // An unstamped legacy exception is not evidence for either clock domain.
  expect(new WallExpired('time wall deadline work exhausted').termination).toBeUndefined()
  const initial = {proven: false, checked: false, stuck: 'sat', goal: 'same law @step', witness: {original: -2}}
  const stopped = stoppedSearch(initial, real!.termination!)
  expect(stopped.context).toEqual({stuck: 'sat', goal: 'same law @step', witness: {original: -2}})
  expect(stopped.witness).toEqual(initial.witness)
})

test('explicit CLI work validation rejects ambiguous or timed proposal budgets before extraction', async () => {
  for (const work of [-1, NaN, Infinity, 0.5, Number.MAX_SAFE_INTEGER + 1])
    expect(await check([], {work, propose: false}).then(() => 'accepted', e => (e as Error).message)).toContain('nonnegative safe integer')
  expect(await check([], {work: 1, ms: 1, propose: false}).then(() => 'accepted', e => (e as Error).message)).toContain('not both')
  expect(await check([], {work: 1}).then(() => 'accepted', e => (e as Error).message)).toContain('propose: false')
  expect(await check([], {work: 1, propose: false, security: true}).then(() => 'accepted', e => (e as Error).message)).toContain('security')
})

test('real CLI argv accepts work without synthesized ms, and rejects explicit mixed budgets', () => {
  const root = mkdtempSync(join(tmpdir(), 'gdp-cli-work-argv-'))
  try {
    const file = join(root, 'Argv.ts')
    writeFileSync(file, `export class Argv { value = 0;\n// gdp: law nonnegative: value >= 0\ntick() { this.value++; } }\n`)
    const cli = new URL('./cli.ts', import.meta.url).pathname
    const work = spawnSync(process.execPath, [cli, 'check', file, '--entry', 'Argv', '--no-propose', '--work', '0', '--json'], {env: cleanEnv(), encoding: 'utf8', timeout: 30000})
    expect(work.status, work.stderr).toBe(2)
    const result = JSON.parse(work.stdout) as Awaited<ReturnType<typeof check>>
    expect(result.rules[0]!.laws[0]).toMatchObject({verdict: 'unknown', stopped: true, termination: {kind: 'work-exhausted'}})
    const both = spawnSync(process.execPath, [cli, 'check', file, '--no-propose', '--work', '0', '--ms', '1', '--json'], {env: cleanEnv(), encoding: 'utf8', timeout: 30000})
    expect(both.status).toBe(2); expect(both.stdout).toContain('not both')
    const wall = spawnSync(process.execPath, [cli, 'check', file, '--entry', 'Argv', '--no-propose', '--work', '100000', '--watchdog-ms', '0', '--json'], {env: cleanEnv(), encoding: 'utf8', timeout: 30000})
    expect(wall.status, wall.stderr).toBe(2)
    const stopped = JSON.parse(wall.stdout) as Awaited<ReturnType<typeof check>>
    expect(stopped.rules[0]!.laws[0]).toMatchObject({verdict: 'unknown', stopped: true, termination: {kind: 'wall-deadline'}})
  } finally { rmSync(root, {recursive: true, force: true}) }
})

test('semantic unknown and native refusal do not acquire a deadline label', async () => {
  const root = mkdtempSync(join(tmpdir(), 'gdp-cli-semantic-'))
  try {
    const file = join(root, 'Semantic.ts')
    writeFileSync(file, `// gdp: law value stays zero: value == 0\nexport class Semantic { value = 0; helper = 0; tick() { this.value = this.helper; this.helper = 0; } }\n`)
    const semantic = await check([file], {entry: 'Semantic', from: 'any', propose: false, ms: 60000, check: {runs: 10, depth: 6, states: 20}})
    expect(semantic.exit, JSON.stringify(semantic)).toBe(2)
    expect(semantic.rules[0]!.laws[0]).toMatchObject({verdict: 'unknown'})
    expect(semantic.rules[0]!.laws[0]!.why).toBeDefined()
    expect(semantic.rules[0]!.laws[0]!.stopped).toBeUndefined()
    expect(semantic.rules[0]!.laws[0]!.termination).toBeUndefined()
    writeFileSync(file, `export class Semantic { value = 0;\n// gdp: law unparsed: definitely not a law\ntick() { this.value++; } }\n`)
    const refused = await check([file], {entry: 'Semantic', propose: false, ms: 60000})
    expect(refused.exit).toBe(2)
    expect(refused.rules[0]!.laws[0]).toMatchObject({verdict: 'not read'})
    expect(refused.rules[0]!.laws[0]!.stopped).toBeUndefined()
    expect(refused.rules[0]!.laws[0]!.termination).toBeUndefined()
  } finally { rmSync(root, {recursive: true, force: true}) }
}, 150000)

test('real wall interruption keeps constructor IDs and SAT context; completed native controls replay', () => {
  const root = mkdtempSync(join(tmpdir(), 'gdp-cli-deadline-')), worker = join(root, 'worker')
  const repo = new URL('../', import.meta.url).pathname
  const evidence = process.env.SUPERCOMPUTER_OUTPUT_DIR ? join(process.env.SUPERCOMPUTER_OUTPUT_DIR, 'cli-deadline') : undefined
  const source = (fixed: boolean) => `public class OwnedDeadline {
  public int value = 0;
  public boolean guarded;
  public OwnedDeadline() { guarded = ${fixed}; }
  public OwnedDeadline(boolean choice) { guarded = ${fixed}; }
  // gdp: law only allowed changes: value != old(value) implies allowed
  public void hit(boolean allowed) { if (guarded && !allowed) return; value++; }
}\n`
  // Keep inference through guarded only for the intentional SAT pause. The
  // direct guards below have the same behavior from either constructor, but
  // leave the short watchdog to exercise post-completion bookkeeping.
  const controlSource = (fixed: boolean) => `public class OwnedDeadline {
  public int value = 0;
  public OwnedDeadline() {}
  public OwnedDeadline(boolean choice) {}
  // gdp: law only allowed changes: value != old(value) implies allowed
  public void hit(boolean allowed) { ${fixed ? 'if (!allowed) return; ' : ''}value++; }
}\n`
  const driver = `public class ReplayDeadline {
  public static void main(String[] args) {
    OwnedDeadline x = args[0].equals("()") ? new OwnedDeadline() : new OwnedDeadline(Boolean.parseBoolean(args[1]));
    boolean broken = false;
    for (int i=2; i<args.length; i++) { int old=x.value; boolean allowed=Boolean.parseBoolean(args[i]); x.hit(allowed); if (x.value!=old && !allowed) broken=true; }
    System.out.println(broken);
  }
}\n`
  try {
    mkdirSync(worker)
    for (const dir of ['core', 'kernel', 'interchange', 'lean-kernel']) cpSync(join(repo, dir), join(worker, dir), {recursive: true, filter: p => !/\.(?:olean|ilean)$/.test(p)})
    for (const dir of ['node_modules', 'vendor']) symlinkSync(join(repo, dir), join(worker, dir))
    cpSync(join(repo, 'package.json'), join(worker, 'package.json'))
    // Arm only once the initial SAT verdict already exists. Observe withWall's
    // normalized domain/end AFTER capture, before entering the stage. This is
    // not a replacement clock and never edits the production checkout.
    const edits: {path: string, before: string, after: string, anchor: string, inserted: string}[] = []
    const inject = (path: string, anchor: string, inserted: string) => {
      const p = join(worker, path), before = readFileSync(p, 'utf8')
      expect(before.split(anchor).length).toBe(2)
      const after = before.replace(anchor, anchor + inserted); writeFileSync(p, after)
      edits.push({path, before: hash(before), after: hash(after), anchor, inserted})
      if (evidence) {
        mkdirSync(evidence, {recursive: true})
        const name = path.replaceAll('/', '-')
        writeFileSync(join(evidence, `${name}.before`), before); writeFileSync(join(evidence, `${name}.after`), after)
        const diff = spawnSync('diff', ['-u', join(evidence, `${name}.before`), join(evidence, `${name}.after`)], {encoding: 'utf8', timeout: 5000})
        expect(diff.status).toBe(1); writeFileSync(join(evidence, `${name}.patch`), diff.stdout)
      }
    }
    inject('core/dsl.ts', 'function searchedIn(r: Rule<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>, laws: Law[], stepLaws: StepLaw[], v: Verdict, opts: ProveOptions): Verdict {', '\n  ;(globalThis as any).__deadlineArm?.(v)')
    inject('kernel/prove.ts', "  if(domain==='counted')return withDeadline(Math.min(budgetEnd(),end),f)", '\n  ;(globalThis as any).__deadlineObserve?.({domain,end})')
    inject('core/search-watchdog.ts', '    const out = run()', '\n    ;(globalThis as any).__watchdogAfter?.(out, ms)')
    const runner = `
import {writeFileSync} from 'node:fs';
import {check} from './core/cli.ts';
let armed=false, latePaused=false; const observations=[];
globalThis.__deadlineArm=(v)=>{armed=v.stuck==='sat'&&!v.run;};
globalThis.__deadlineObserve=(deadline)=>{
 if(armed&&process.env.DEADLINE_MODE==='pause'&&deadline.domain==='real'&&Number.isFinite(deadline.end)){
  armed=false; observations.push({deadline, point:'withWall normalized real endpoint'});
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)),0,0,3200);
 }
};
globalThis.__watchdogAfter=(out,ms)=>{
 if(!latePaused&&ms===5000&&process.env.DEADLINE_MODE.startsWith('late')&&((out.proven&&out.checked)||out.run)){
  latePaused=true; observations.push({point:'after completed public callback',proven:out.proven,checked:out.checked,run:!!out.run});
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)),0,0,5100);
 }
};
const result=await check([process.env.DEADLINE_SOURCE],{entry:'OwnedDeadline',methods:['hit'],propose:false,ms:process.env.DEADLINE_MODE==='pause'?3000:60000,watchdogMs:process.env.DEADLINE_MODE.startsWith('late')?5000:undefined,check:{runs:10,depth:6,states:20}});
writeFileSync(process.env.DEADLINE_RESULT,JSON.stringify({result,observations},null,2));
process.exitCode=result.exit;
`
    writeFileSync(join(worker, 'diagnostic.ts'), runner)
    if (evidence) { mkdirSync(evidence, {recursive: true}); writeFileSync(join(evidence, 'instrumentation.json'), JSON.stringify(edits, null, 2)); writeFileSync(join(evidence, 'runner.ts'), runner) }
    type Result = Awaited<ReturnType<typeof check>>
    const results: {mode: string, sourceHash: string, nativeExit: number | null, result: Result, observations: {deadline: {domain: string, end: number}}[]}[] = []
    for (const [version, fixed] of [['broken', false], ['fixed', true]] as const) {
      for (const mode of fixed ? ['completed', 'pause', 'late-proven'] : ['completed', 'late-broken']) {
        const dir = join(root, `${version}-${mode}`); mkdirSync(dir)
        const file = join(dir, 'OwnedDeadline.java'), text = mode === 'pause' ? source(fixed) : controlSource(fixed)
        writeFileSync(file, text); writeFileSync(join(dir, 'ReplayDeadline.java'), driver)
        const compile = spawnSync('javac', [file, join(dir, 'ReplayDeadline.java')], {encoding: 'utf8', timeout: 30000})
        expect(compile.status, compile.stderr).toBe(0)
        const resultFile = join(root, `${version}-${mode}.json`)
        const child = spawnSync(process.execPath, [join(worker, 'diagnostic.ts')], {cwd: worker, env: {...cleanEnv(), DEADLINE_MODE: mode, DEADLINE_SOURCE: file, DEADLINE_RESULT: resultFile}, encoding: 'utf8', timeout: 150000})
        expect(child.signal, child.stderr).toBeNull()
        const receipt = JSON.parse(readFileSync(resultFile, 'utf8')) as {result: Result, observations: {deadline: {domain: string, end: number}}[]}
        results.push({mode: `${version}-${mode}`, sourceHash: hash(text), nativeExit: child.status, ...receipt})
        if (evidence) {
          writeFileSync(join(evidence, 'results.json'), JSON.stringify(results, null, 2))
          writeFileSync(join(evidence, `${version}-${mode}.stdout`), child.stdout)
          writeFileSync(join(evidence, `${version}-${mode}.stderr`), child.stderr)
          writeFileSync(join(evidence, `${version}-${mode}.java`), text)
          writeFileSync(join(evidence, 'ReplayDeadline.java'), driver)
        }
        expect(child.status, child.stderr).toBe(mode === 'pause' ? 2 : fixed ? 0 : 1)
        expect(receipt.result.exit).toBe(child.status!)
        expect(receipt.result.rules.map(r => r.ctor).sort((a, b) => (a ?? '').localeCompare(b ?? ''))).toEqual(['()', '(boolean)'])
        for (const r of receipt.result.rules) {
          expect(r.entry).toBe('OwnedDeadline'); expect(r.ok).toBe(true); expect(r.checked).toBeDefined()
          const law = r.laws[0]!
          expect(law.name).toBe('only allowed changes'); expect(law.expr).toBe('value != old(value) implies allowed'); expect(law.where).toBeDefined()
          expect(law.translation).toBe('sampled')
          if (mode === 'pause') {
            expect(receipt.observations.length).toBeGreaterThan(0)
            expect(receipt.observations.every(o => o.deadline.domain === 'real')).toBe(true)
            expect(law).toMatchObject({verdict: 'unknown', stopped: true, termination: {kind: 'wall-deadline'}})
            expect(law.why).toContain('wall deadline')
            expect(law.context?.stuck).toBe('sat'); expect(law.context?.witness).toBeDefined()
            expect(law.run).toBeUndefined(); expect(law.cert).toBeUndefined()
          } else {
            if (mode.startsWith('late')) expect(receipt.observations.length).toBeGreaterThan(0)
            expect(law.verdict).toBe(fixed ? 'proven' : 'broken')
            expect(law.stopped).toBeUndefined(); expect(law.termination).toBeUndefined()
            if (fixed) expect(law.translationChecks).toBeGreaterThan(0)
            else {
              const lines = [...law.run!], constructor = /^made with choice = (true|false)$/.exec(lines[0] ?? '')
              expect(!!constructor).toBe(r.ctor === '(boolean)'); if (constructor) lines.shift()
              const inputs = lines.map(line => { const m = /^hit\(allowed=(true|false)\)$/.exec(line); expect(m).not.toBeNull(); return m![1]! })
              expect(inputs.length).toBeGreaterThan(0)
              const replay = spawnSync('java', ['-cp', dir, 'ReplayDeadline', r.ctor!, constructor?.[1] ?? 'false', ...inputs], {encoding: 'utf8', timeout: 10000})
              expect(replay.status, replay.stderr).toBe(0); expect(replay.stdout.trim()).toBe('true')
            }
          }
        }
        expect(readFileSync(file, 'utf8')).toBe(text)
      }
    }
    if (evidence) writeFileSync(join(evidence, 'results.json'), JSON.stringify(results, null, 2))
  } finally { rmSync(root, {recursive: true, force: true}) }
}, 420000)

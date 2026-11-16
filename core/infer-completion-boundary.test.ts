// Internal result-construction diagnostics. All instrumentation is confined to
// a temporary worker copy. Real checked proofs/runs are never fabricated. The
// single failed-candidate injection tests diagnostic context only, explicitly.
import {expect, test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'

const digest = (text: string) => createHash('sha256').update(text).digest('hex')

test('completed inference survives owned internal bookkeeping stops, not ancestor or rejected-work cancellation', () => {
  const root = mkdtempSync(join(tmpdir(), 'gdp-infer-completion-')), worker = join(root, 'worker')
  const repo = new URL('../', import.meta.url).pathname
  const artifacts = process.env.SUPERCOMPUTER_OUTPUT_DIR ? join(process.env.SUPERCOMPUTER_OUTPUT_DIR, 'infer-completion-boundary') : undefined
  try {
    mkdirSync(worker)
    for (const dir of ['core', 'kernel', 'interchange', 'lean-kernel']) cpSync(join(repo, dir), join(worker, dir), {recursive: true, filter: p => !/\.(?:olean|ilean)$/.test(p)})
    for (const dir of ['node_modules', 'vendor']) symlinkSync(join(repo, dir), join(worker, dir))
    mkdirSync(join(worker, 'examples')); cpSync(join(repo, 'examples/infer.ts'), join(worker, 'examples/infer.ts'))
    cpSync(join(repo, 'package.json'), join(worker, 'package.json'))
    const changes: {path: string, before: string, after: string, anchor: string, inserted: string, beforeAnchor: boolean}[] = []
    const inject = (path: string, anchor: string, inserted: string, beforeAnchor = false) => {
      const file = join(worker, path), before = readFileSync(file, 'utf8')
      expect(before.split(anchor).length, `unique diagnostic anchor: ${path}`).toBe(2)
      const after = before.replace(anchor, beforeAnchor ? inserted + anchor : anchor + inserted); writeFileSync(file, after)
      changes.push({path, before: digest(before), after: digest(after), anchor, inserted, beforeAnchor})
    }
    inject('core/search-watchdog.ts', '  if (ms !== undefined) watchdogEnd = Math.min(outer, performance.now() + ms)', '\n  if (ms !== undefined) (globalThis as any).__inferDeadline?.({domain: "real", end: watchdogEnd})')
    inject('core/search-watchdog.ts', "export function checkWatchdog(phase: string): void {", '\n  ;(globalThis as any).__inferWatchdogPoll?.(phase, watchdogEnd)')
    inject('core/search-watchdog.ts', '    const out = run()', '\n    ;(globalThis as any).__inferAfterCallback?.(out, ms)')
    inject('core/infer.ts', '  observed.context = () => searchContext(first)', '\n  ;(globalThis as any).__inferFirst?.(first)')
    inject('core/infer.ts', '  const stats = (samples: number, candidates: number, alive: number) => {', '\n    if ((first.proven && first.checked) || first.run) (globalThis as any).__inferBoundary?.("first", observed.completed ?? first)')
    inject('core/infer.ts', '    last = withTrees(() => search([...given, ...chosen.map(lawFor)]))', '\n    last = (globalThis as any).__diagnosticFailedCandidate?.(last) ?? last')
    inject('core/infer.ts', '    const took = now() - began', '\n    ;(globalThis as any).__inferChecked?.(last, observed.completed)')
    inject('core/infer.ts', '  for (const f of opts.minimize === false || enumProof ? [] : [...chosen].reverse()) {', '\n    ;(globalThis as any).__inferBoundary?.("minimization", observed.completed ?? last)')
    inject('core/infer.ts', "  trace('end', {proven: true, stopped: stop(), found: chosen.map(f => textOf(f)).join('; ')})", '  ;(globalThis as any).__inferBoundary?.("final", observed.completed ?? last)\n', true)
    inject('core/infer.ts', '      observed.last ??= observed.snapshot?.(); observed.lastContext ??= observed.context?.()', '\n      ;(globalThis as any).__inferInterruption?.({resultAssigned: result !== undefined, error: (error as Error).name})')
    const runner = `
import {writeFileSync} from 'node:fs';
import {rule,proveRule} from './core/dsl.ts';
import {inferLaws} from './core/infer.ts';
import {accounts,accountsLaw,pool,poolLaw} from './examples/infer.ts';
import {BudgetExpired,checkWorkAdmission,remainingWork,withBudget} from './kernel/prove.ts';
import {checkWatchdog,withSearchWatchdog} from './core/search-watchdog.ts';
import {proofOutput,publishProof} from './core/proof-output.ts';
import {toInterchange} from './interchange/format.ts';
import {checkDocument} from './interchange/check.ts';
const mode=process.env.INFER_BOUNDARY_MODE, receipt={mode,events:[],polls:[],interruptions:[],diagnosticOnly:mode==='context'};
let deadline, expired=false;
globalThis.__inferDeadline=d=>{deadline=d;};
globalThis.__inferWatchdogPoll=(phase,end)=>{if(expired)receipt.polls.push({phase,end});};
globalThis.__inferFirst=first=>{receipt.first={proven:first.proven,checked:first.checked,goal:first.goal,stuck:first.stuck,witness:first.witness,run:first.run};};
globalThis.__inferInterruption=e=>receipt.interruptions.push(e);
const expire=point=>{
 if(expired)return;
 if(!deadline||deadline.domain!=='real'||!Number.isFinite(deadline.end))throw Error('missing captured real endpoint');
 const delay=Math.max(0,deadline.end-performance.now()+5);
 if(delay>6000)throw Error('diagnostic pause exceeds bound');
 receipt.events.push({point,deadline,delay});
 Atomics.wait(new Int32Array(new SharedArrayBuffer(4)),0,0,delay);expired=true;
};
globalThis.__inferAfterCallback=(out,ms)=>{
 if(mode!=='ancestor-work'||ms!==5000||expired)return;
 if(!out.proven||!out.checked)throw Error('mixed priority fixture did not complete');
 receipt.boundary={point:'after callback',proven:out.proven,checked:out.checked};
 try{checkWorkAdmission(remainingWork()+1,'diagnostic denied ancestor admission');throw Error('expected ancestor admission refusal');}
 catch(e){if(!(e instanceof BudgetExpired))throw e;receipt.rejectedActualWork=true;}
 expire('after callback ancestor work');
};
globalThis.__diagnosticFailedCandidate=last=>{
 if(mode!=='context')return last;
 receipt.injected={originalProven:last.proven,originalChecked:last.checked,diagnosticOnly:true};
 return {proven:false,checked:false,goal:'diagnostic failed candidate @step',stuck:'unknown',witness:{diagnosticLater:777}};
};
globalThis.__inferChecked=(last,completed)=>{receipt.lastCapture=completed?{proven:completed.proven,checked:completed.checked,found:completed.found.map(f=>f.text)}:undefined;receipt.later={proven:last.proven,checked:last.checked,goal:last.goal,stuck:last.stuck,witness:last.witness};};
globalThis.__inferBoundary=(point,completed)=>{
 const wanted=mode==='final'?'final':mode==='minimization'?'minimization':'first';
 if(point!==wanted||mode==='context'||mode==='progress'||mode==='ancestor-work'||expired)return;
 if(!completed||!((completed.proven&&completed.checked)||completed.run))throw Error('boundary reached without completed evidence');
 receipt.boundary={point,proven:completed.proven,checked:completed.checked,run:completed.run,found:completed.found?.map(f=>f.text)??[]};
 if(mode==='rejected'||mode==='rejected-then-wall'){
  try{checkWorkAdmission(remainingWork()+1,'diagnostic rejected actual work');throw Error('expected admission refusal');}
  catch(e){if(!(e instanceof BudgetExpired))throw e;receipt.rejectedActualWork=true;if(mode==='rejected')throw e;}
 }
 expire(point);
};
const simple=rule('owned completed boundary').state({value:0}).step(({value})=>({value:value.plus(1)}));
const simpleLaw=simple.law(mode==='first-run'?'stays zero':'nonnegative',({value})=>mode==='first-run'?value.eq(0):value.atLeast(0));
const usePool=['minimization','progress','context'].includes(mode);
const r=mode==='final'?accounts():usePool?pool():simple, laws=mode==='final'?[accountsLaw(r)]:usePool?[poolLaw(r)]:[simpleLaw];
const expectedFirst=mode==='context'?proveRule(r,laws,{search:false}):undefined;
let capsule;
proofOutput.on=e=>{capsule=e.proof;};
let childReturned=false;
const invoke=()=>{
 receipt.childEntered=true;
 const result=inferLaws(r,laws,[],{work:1000000,watchdogMs:5000,join:usePool?0:undefined,minimize:mode==='final'?false:undefined,progress:(phase,info)=>{
  if(phase!=='proof')return;
  receipt.proofProgress={...info};
  if(mode==='context'){
   if(!receipt.injected||info.goal!=='diagnostic failed candidate @step'||info.stuck!=='unknown')throw Error('diagnostic failed candidate was not observed');
   expire('diagnostic incomplete proof progress');checkWatchdog('diagnostic incomplete proof progress');
  }
  if(mode==='progress'&&receipt.later?.proven&&receipt.later?.checked){expire('completed proof progress');checkWatchdog('completed proof progress');}
 }});
 childReturned=true;return result;
};
try{
 const result=mode==='ancestor'?withSearchWatchdog(1000,invoke):mode==='ancestor-work'?withBudget(1000000,invoke):invoke();
 receipt.result=result;
 if(result.proven&&result.checked){
  publishProof(result,r.machine,laws);
  const usual=node=>node?.kind==='usual'?node:node?.kind==='derived'?node.parents.map(usual).find(Boolean):undefined;
  const saved=usual(capsule);if(!saved)throw Error('completed capsule lost');
  receipt.proofLaws=saved.laws.map(law=>law.name);
  receipt.interchange=JSON.parse(JSON.stringify(toInterchange({kind:'laws',machine:saved.machine,laws:saved.laws,proof:saved.proof})));
  receipt.replay=checkDocument(receipt.interchange);
 }
 if(mode==='context')receipt.expectedFirst={goal:expectedFirst.goal,stuck:expectedFirst.stuck,witness:expectedFirst.witness};
}catch(e){receipt.error={name:e.name,message:e.message,termination:e.termination};}
finally{proofOutput.on=undefined;receipt.childReturned=childReturned;writeFileSync(process.env.INFER_BOUNDARY_RESULT,JSON.stringify(receipt,null,2));}
`
    writeFileSync(join(worker, 'boundary.ts'), runner)
    if (artifacts) {
      mkdirSync(artifacts, {recursive: true})
      writeFileSync(join(artifacts, 'instrumentation.json'), JSON.stringify(changes, null, 2)); writeFileSync(join(artifacts, 'runner.ts'), runner)
      writeFileSync(join(artifacts, 'infer.instrumented.ts'), readFileSync(join(worker, 'core/infer.ts'), 'utf8'))
      writeFileSync(join(artifacts, 'watchdog.instrumented.ts'), readFileSync(join(worker, 'core/search-watchdog.ts'), 'utf8'))
    }
    const env = Object.fromEntries(Object.entries(process.env).filter(([key]) => !key.startsWith('GDP_WORK_') && key !== 'GDP_STEP_WORK'))
    for (const mode of ['first-proof', 'first-run', 'final', 'minimization', 'progress', 'ancestor', 'ancestor-work', 'rejected', 'rejected-then-wall', 'context']) {
      const file = join(root, `${mode}.json`)
      const child = spawnSync(process.execPath, [join(worker, 'boundary.ts')], {cwd: worker, env: {...env, INFER_BOUNDARY_MODE: mode, INFER_BOUNDARY_RESULT: file}, encoding: 'utf8', timeout: 45000})
      expect(child.status, child.stderr).toBe(0)
      const receipt = JSON.parse(readFileSync(file, 'utf8'))
      if (artifacts) writeFileSync(join(artifacts, `${mode}.json`), JSON.stringify(receipt, null, 2))
      if (mode === 'ancestor') {
        expect(receipt.boundary?.point).toBe('first'); expect(receipt.error?.name).toBe('WatchdogExpired')
        expect(receipt.childReturned, 'ancestor must propagate before child returns, not only at owner completion').toBe(false)
      } else if (mode === 'ancestor-work') {
        expect(receipt.childEntered).toBe(true); expect(receipt.childReturned, 'live ancestor work refusal must propagate before child returns').toBe(false)
        expect(receipt.boundary?.point).toBe('after callback'); expect(receipt.rejectedActualWork).toBe(true)
        expect(receipt.error?.name).toBe('BudgetExpired')
        expect(receipt.polls.some((poll: {phase: string}) => poll.phase === 'search result')).toBe(true)
      } else if (mode === 'rejected' || mode === 'rejected-then-wall') {
        expect(receipt.boundary?.proven).toBe(true); expect(receipt.rejectedActualWork).toBe(true)
        expect(receipt.error).toBeUndefined(); expect(receipt.result).toMatchObject({proven: false, checked: false, stopped: true, termination: {kind: 'work-exhausted'}})
      } else if (mode === 'context') {
        expect(receipt.diagnosticOnly).toBe(true); expect(receipt.injected?.diagnosticOnly).toBe(true)
        expect(receipt.proofProgress).toMatchObject({goal: 'diagnostic failed candidate @step', stuck: 'unknown'})
        expect(receipt.result).toMatchObject({proven: false, checked: false, stopped: true, termination: {kind: 'wall-deadline'}})
        expect(receipt.first.stuck).toBe('sat'); expect(receipt.result.context).toEqual(receipt.expectedFirst)
        expect(receipt.result.context.witness).not.toEqual(receipt.later.witness)
        expect(receipt.replay).toBeUndefined()
      } else {
        expect(receipt.error, JSON.stringify(receipt)).toBeUndefined()
        expect(receipt.result.stopped).toBeUndefined(); expect(receipt.result.termination).toBeUndefined()
        expect(receipt.result.stats.stopped).toBe(false); expect(receipt.result.stats.termination).toBeUndefined()
        expect(receipt.interruptions).toEqual([{resultAssigned: false, error: 'WatchdogExpired'}])
        if (mode === 'first-run') { expect(receipt.result.run).toEqual(receipt.boundary.run); expect(receipt.result.run.trace.length).toBeGreaterThan(0) }
        else {
          expect(receipt.result).toMatchObject({proven: true, checked: true}); expect(receipt.replay?.accepted).toBe(true)
          const originalLaw = mode === 'final' ? 'a <= total' : ['progress', 'minimization'].includes(mode) ? 'released <= acquired' : 'nonnegative'
          expect(receipt.proofLaws).toContain(originalLaw)
          for (const found of receipt.result.found) expect(receipt.proofLaws).toContain(found.law.name)
        }
        if (mode === 'final' || mode === 'minimization') {
          expect(receipt.boundary?.point).toBe(mode); expect(receipt.result.found.length).toBeGreaterThan(0)
          expect(receipt.result.found.map((f: {text: string}) => f.text)).toEqual(receipt.boundary.found)
        }
        if (mode === 'progress') {
          expect(receipt.proofProgress).toBeDefined(); expect(receipt.lastCapture).toMatchObject({proven: true, checked: true})
          expect(receipt.result.found.map((f: {text: string}) => f.text)).toEqual(receipt.lastCapture.found)
        }
        expect(receipt.events.length).toBeGreaterThan(0)
        expect(receipt.polls.some((poll: {phase: string}) => poll.phase === (mode === 'progress' ? 'completed proof progress' : 'inference poll'))).toBe(true)
      }
    }
  } finally { rmSync(root, {recursive: true, force: true}) }
}, 240000)

import {expect, test} from 'bun:test'
import {proveSteps, rule} from '../core/dsl.ts'
import {extract} from '../core/extract.ts'
import {buildLaw} from '../core/laws.ts'
import {attachNativeLaw, attachSource, rememberNative, type NativeObservation} from '../core/source-check.ts'
import {toLean} from './emit.ts'

const observation: NativeObservation = {
  where: 'unit control', before: {}, after: {}, params: {}, inputs: {}, bindings: {}, args: [], result: undefined, failed: false,
}

// These are explicitly unit-bound provenance controls. They exercise only the
// public export boundary; native extractor evidence remains covered elsewhere.
function sourceBound(evaluate: (o: NativeObservation) => boolean) {
  const r = rule('source export control').state({value: 0}).step(({value}) => ({value}))
  const evidence = {}
  rememberNative(evidence, {enabled: true, complete: true, scope: 'exhaustive', observations: [observation]})
  attachSource(r, evidence, [])
  const law = r.law('value remains nonnegative', ({value}) => value.atLeast(0))
  attachNativeLaw(r, law, law.name, undefined, evaluate)
  return {r, law}
}

test('toLean refuses a source-marked machine whose private provenance was lost', () => {
  const r = rule('unknown source export').state({value: 0}).step(({value}) => ({value}))
  Object.defineProperty(r, Symbol.for('gdp-wired.source-proof.v1'), {value: true})
  // A serialized field is not proof authority; only the private bound journal is.
  const machine = r.machine
  Object.assign(machine, {translation: 'sampled'})
  const law = r.law('value remains nonnegative', ({value}) => value.atLeast(0))
  expect(() => toLean([{id: 'unknown_source_export', machine, laws: [law]}]))
    .toThrow('source translation unchecked')
})

test('toLean refuses a source law that its native interpretation rejects', () => {
  const {r, law} = sourceBound(() => false)
  expect(() => toLean([{id: 'failed_source_export', machine: r.machine, laws: [law]}]))
    .toThrow('translation error')
})

test('toLean rejects a copied source machine with lost private custody', () => {
  const {r, law} = sourceBound(() => true)
  expect(() => toLean([{id:'copied_source',machine:{...r.machine},laws:[law]}])).toThrow('source translation unchecked')
})

test('toLean rechecks current source evidence rather than caching an earlier success', () => {
  let valid=true
  const {r, law}=sourceBound(()=>valid)
  expect(toLean([{id:'before_change',machine:r.machine,laws:[law]}])).toContain('before_change_laws')
  valid=false
  expect(()=>toLean([{id:'after_change',machine:r.machine,laws:[law]}])).toThrow('translation error')
})

test('toLean refuses an actual source law after the public native check rejects it',()=>{
  const x=extract('export function decide(a: boolean, b: boolean): boolean { return a && b; }', {entry:'decide',mode:'standalone',check:{runs:1,depth:1,states:0,probes:false}})
  expect(x.ok).toBe(true)
  const built=buildLaw(x,{name:'not equivalent',expr:'result == a',method:'decide'})
  if(built.kind!=='step')throw Error('expected a step law')
  // Deliberate lowering mutant: the model tautology must not hide a false source law.
  built.law.then={op:'<=',a:{op:'const',value:0},b:{op:'const',value:0}}
  expect(proveSteps(x.rule!,x.invariants??[],[built.law],{from:'any',search:false})).toMatchObject({proven:false,checked:false,translation:'error'})
  expect(()=>toLean([{id:'rejected_native',machine:x.rule!.machine,laws:x.invariants??[],stepLaws:[built.law]}])).toThrow('translation error')
})

test('toLean refuses a true source law when native checking was explicitly disabled',()=>{
  const x=extract('export function decide(a: boolean): boolean { return a; }', {entry:'decide',mode:'standalone',check:{runs:1,depth:1,states:0,probes:false,lawCrossCheck:false}})
  expect(x.ok).toBe(true)
  const built=buildLaw(x,{name:'identity result',expr:'result == a',method:'decide'})
  if(built.kind!=='step')throw Error('expected a step law')
  expect(()=>toLean([{id:'unchecked_native',machine:x.rule!.machine,laws:x.invariants??[],stepLaws:[built.law]}])).toThrow('source translation unchecked')
})

test('toLean keeps ordinary typed DSL exports unchanged', () => {
  const r = rule('plain export').state({value: 0}).step(({value}) => ({value}))
  const law = r.law('value remains nonnegative', ({value}) => value.atLeast(0))
  expect(toLean([{id: 'plain_export', machine: r.machine, laws: [law]}])).toContain('plain_export_laws')
})

test('toLean accepts a current source-native-bound law after rechecking its journal', () => {
  const {r, law} = sourceBound(() => true)
  expect(toLean([{id: 'bound_source_export', machine: r.machine, laws: [law]}])).toContain('bound_source_export_laws')
})

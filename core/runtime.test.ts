import {expect, test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {bool, decimal, fn, fun, int, maybe, modBy, nat, oneOf, record} from './dsl.ts'

test('function runtimes preserve output kinds, parameters and repeated calls', () => {
  const decision = fun('structured runtime').params({threshold: nat})
    .inputs({enabled: bool, delta: int, price: decimal(2), mode: oneOf('left', 'right'), optional: maybe(bool), rec: record({ok: bool})})
    .returns(({enabled, delta, price, mode, optional, rec, threshold}) => ({enabled, delta: delta.plus(1), price: price.plus(1), mode, optional, nested: {ok: rec.ok}, enough: threshold.atLeast(2)}))
  const inputs = {enabled: true, delta: -2, price: 1.25, mode: 'right', optional: null, rec: {ok: true}}
  const expected = {enabled: true, delta: -1, price: 2.25, mode: 'right', optional: null, nested: {ok: true}, enough: true} as const
  const compiled = decision.compiled()
  expect(decision.compiled()).toBe(compiled)
  for (let i = 0; i < 3; i++) {
    expect(decision.run(inputs, {threshold: 2})).toEqual(expected)
    expect(compiled(inputs, {threshold: 2})).toEqual(expected)
  }
  expect(decision.run({...inputs, optional: false}, {threshold: 1}).optional).toBe(false)
  expect(compiled({...inputs, optional: true}, {threshold: 1}).optional).toBe(true)
})

test('both function runtimes enforce assumptions and exact arithmetic', () => {
  const f = fun('exact').inputs({n: nat}).assume(({n}) => n.atLeast(1)).returns(({n}) => ({out: n.plus(1)}))
  for (const run of [f.run.bind(f), f.compiled()]) {
    expect(() => run({n: 0})).toThrow('assumption')
    expect(() => run({n: Number.MAX_SAFE_INTEGER})).toThrow()
    expect(run({n: 2})).toEqual({out: 3})
  }
})

test('declared helper source needs explicit compilation, including callbacks and arithmetic helpers', () => {
  for (const [helper, expected] of [[fn(1, 'x => x + 1'), 4], [fn(1, (x: number) => x + 1), 4], [modBy(2), 1]] as const) {
    const f = fun('helper').fns({helper}).inputs({n: nat}).returns(({n, helper}) => ({out: helper(n)}))
    expect(() => f.run({n: 3})).toThrow('does not compile declared helper source')
    expect(f.compiled()({n: 3}).out).toBe(expected)
  }
})

test('fresh import and default arithmetic runtime work with Function blocked before construction', () => {
  const url = new URL('./dsl.ts', import.meta.url).href
  const source = `
let attempts = 0;
globalThis.Function = new Proxy(globalThis.Function, {construct() { attempts++; throw Error('dynamic code blocked'); }, apply() { attempts++; throw Error('dynamic code blocked'); }});
const {bool, fn, fun, nat, oneOf, when} = await import(${JSON.stringify(url)});
const f = fun('csp').inputs({n:nat, enabled:bool, mode:oneOf('left','right')}).returns(({n,enabled,mode}) => ({q:n.divBy(2),r:n.modBy(2),rounded:n.ceilTo(2),enabled,mode,selected:when(enabled,n,0)}));
const got = f.run({n:5,enabled:true,mode:'right'});
const helper = fun('blocked helper').inputs({n:nat}).fns({inc:fn(1,'x => x + 1')}).returns(({n,inc})=>({out:inc(n)}));
let refused=false;try{helper.run({n:1})}catch(e){refused=String(e).includes('does not compile declared helper source')}
if(attempts || !refused || JSON.stringify(got)!==JSON.stringify({q:2,r:1,rounded:6,enabled:true,mode:'right',selected:5})) throw Error(JSON.stringify({attempts,refused,got}));
console.log('CSP default passed');
`
  const result = spawnSync(process.execPath, ['--eval', source], {encoding: 'utf8', timeout: 15000})
  expect({status: result.status, stderr: result.stderr}).toEqual({status: 0, stderr: ''})
  expect(result.stdout.trim()).toBe('CSP default passed')
})

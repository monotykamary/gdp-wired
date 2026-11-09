import {expect, test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {bool, decimal, divBy, fn, fun, int, maybe, min, modBy, nat, oneOf, record, recur, rule, type FnDef} from './dsl.ts'
import {fnCall, fnValue, interpret, sourceFreeFn, type Fn} from './machine.ts'

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

test('user helper source needs explicit compilation, including callbacks', () => {
  for (const [helper, expected] of [[fn(1, 'x => x + 1'), 4], [fn(1, (x: number) => x + 1), 4]] as const) {
    const f = fun('helper').fns({helper}).inputs({n: nat}).returns(({n, helper}) => ({out: helper(n)}))
    expect(() => f.run({n: 3})).toThrow('compiled()')
    expect(f.compiled()({n: 3}).out).toBe(expected)
    expect(() => f.run({n: 3})).toThrow('compiled()')
  }
})

test('rule interpreter helper compilation needs an explicit opt-in', () => {
  const r = rule('helper').fns({inc: fn(1, 'x => x + 1')}).state({n: 0}).step(({n, inc}) => ({n: inc(n)}))
  expect(() => r.interpreter()).toThrow('{compileHelpers: true}')
  const run = r.interpreter({compileHelpers: true})
  expect(run.step({}, run.init({}), {}).scalars.n).toBe(1)
})

test('recurrences with transitive custom helpers retain explicit compilation', () => {
  for (const source of ['x => x + 2', (x: number) => x + 2]) {
    const inner = recur('inner', {fns: {custom: fn(1, source)}, zero: 0, next: (_, p, {custom}) => custom(p)})
    const outer = recur('outer', {args: ['a'], fns: {inner}, zero: ({a}) => a, next: (x, p, {inner}) => p.plus(inner(x))})
    const r = rule('transitive').fns({outer}).inputs({x: nat}).state({v: 0}).step(({x, outer}) => ({v: outer(x, 5)}))
    expect(() => r.interpreter()).toThrow('{compileHelpers: true}')
    for (const run of [r.interpreter({compileHelpers: true}), r.compiled()]) {
      expect(run.step({}, run.init({}), {x: 4}).scalars.v).toBe(17)
    }
    const f = fun('transitive').fns({outer}).inputs({x: nat}).returns(({x, outer}) => ({v: outer(x, 5)}))
    expect(() => f.run({x: 4})).toThrow('compiled()')
    expect(f.compiled()({x: 4})).toEqual({v: 17})
    expect(() => f.run({x: 4})).toThrow('compiled()')
  }
})

test('overridden library JS is custom source, including after a native value was cached', () => {
  const definitions = [divBy(2), modBy(3), recur('override', {zero: 0, next: (_, p) => p.plus(1)})]
  for (const definition of definitions) {
    const unchanged = fun('unchanged').fns({q: definition}).inputs({n: nat}).returns(({n, q}) => ({out: q(n), literal: q(4)}))
    unchanged.run({n: 4}) // Populate the definition's native constant-value cache first.
    for (const source of ['x => x + 1', (x: number) => x + 1]) {
      const q = {...definition, js: source}
      const f = fun('overridden').fns({q}).inputs({n: nat}).returns(({n, q}) => ({out: q(n), literal: q(4)}))
      expect(() => f.run({n: 4})).toThrow('compiled()')
      expect(f.compiled()({n: 4})).toEqual({out: 5, literal: 5})
      const r = rule('overridden').fns({q}).inputs({n: nat}).state({out: 0}).step(({n, q}) => ({out: q(n)}))
      expect(() => r.interpreter()).toThrow('{compileHelpers: true}')
      for (const run of [r.interpreter({compileHelpers: true}), r.compiled(), interpret(JSON.parse(JSON.stringify(r.machine)))]) {
        expect(run.step({}, run.init({}), {n: 4}).scalars.out).toBe(5)
      }
    }
    definition.js = 'x => x + 1'
    const changed = fun('mutated definition').fns({q: definition}).returns(({q}) => ({out: q(4)}))
    expect(() => changed.run({})).toThrow('compiled()')
    expect(changed.compiled()({})).toEqual({out: 5})
  }
})

test('overridden library arity is custom even when its JS is unchanged', () => {
  // The built-in facts take one argument too; this custom signature must supply its own facts.
  const q = {...divBy(2), arity: 2, facts: undefined}
  const f = fun('arity override').fns({q}).inputs({a: nat, b: nat}).returns(({a, b, q}) => ({out: q(a, b)}))
  expect(() => f.run({a: 26, b: 9})).toThrow('compiled()')
  expect(f.compiled()({a: 26, b: 9})).toEqual({out: 13})
  const r = rule('arity override').fns({q}).inputs({a: nat, b: nat}).state({out: 0}).step(({a, b, q}) => ({out: q(a, b)}))
  expect(() => r.interpreter()).toThrow('{compileHelpers: true}')
  for (const run of [r.interpreter({compileHelpers: true}), r.compiled(), interpret(JSON.parse(JSON.stringify(r.machine)))]) {
    expect(run.step({}, run.init({}), {a: 26, b: 9}).scalars.out).toBe(13)
  }
})

test('low-level source, arity, call and descriptor overrides cannot use cached native code', () => {
  const r = rule('metadata').fns({q: divBy(2)}).inputs({n: nat}).state({out: 0}).step(({n, q}) => ({out: q(n)}))
  const original = r.machine.fns!.q!
  const copy = (): Fn => JSON.parse(JSON.stringify(original))
  for (const mutation of [
    (q: Fn) => { q.js = 'x => x + 1' },
    (q: Fn) => { q.arity = 2; q.call = '(x, y) => x + y' },
    (q: Fn) => { if (q.direct?.kind === 'div') q.direct.divisor = 4 },
    (q: Fn) => { (q.direct as {kind: string}).kind = 'unknown' },
    (q: Fn) => { (q.direct as {kind: string}).kind = 'recur' }, // Missing recurrence fields fail closed.
  ]) {
    const q = copy()
    expect(sourceFreeFn(q)).toBe(true)
    expect(fnValue(q, 4)).toBe(2)
    expect(fnCall(q, [4])).toBe(2)
    mutation(q)
    expect(sourceFreeFn(q)).toBe(false)
    expect(fnValue(q, 4)).toBe(q.js === original.js ? 2 : 5)
    expect(fnCall(q, [4, 9])).toBe(q.call ? 13 : q.js === original.js ? 2 : 5)
  }
  const q = copy()
  q.call = 'x => x + 1'
  expect(sourceFreeFn(q)).toBe(false)
  expect(fnCall(q, [4])).toBe(5)
})

test('cyclic native metadata fails closed without evaluating source', () => {
  const q = recur('cycle', {zero: 0, next: (_, p) => p.plus(1)})
  if (q.direct?.kind !== 'recur') throw new Error('missing recurrence metadata')
  q.direct.uses.cycle = {js: String(q.js), direct: q.direct}
  expect(sourceFreeFn(q)).toBe(false)
  const f = fun('cycle metadata').fns({q}).inputs({n: nat}).returns(({n, q}) => ({out: q(n)}))
  expect(() => f.run({n: 4})).toThrow('compiled()')
})

test('mutated recurrence metadata is custom while its unchanged source still computes the original result', () => {
  for (const mutate of [
    (q: FnDef) => { if (q.direct?.kind === 'recur') q.direct.args.push('extra') },
    (q: FnDef) => { if (q.direct?.kind === 'recur') q.direct.zero = {op: 'const', value: 99} },
    (q: FnDef) => { if (q.direct?.kind === 'recur') q.direct.next = {op: 'const', value: 99} },
    (q: FnDef) => { if (q.direct?.kind === 'recur' && q.direct.uses.h?.direct?.kind === 'div') q.direct.uses.h.direct.divisor = 99 },
  ]) {
    const q = recur('metadata', {fns: {h: divBy(2)}, zero: 0, next: (_, p, {h}) => p.plus(h(2))})
    mutate(q)
    expect(sourceFreeFn(q)).toBe(false)
    const f = fun('metadata').fns({q}).inputs({n: nat}).returns(({n, q}) => ({out: q(n)}))
    expect(() => f.run({n: 4})).toThrow('compiled()')
    expect(f.compiled()({n: 4})).toEqual({out: 4})
  }
})

test('default guards inspect current recurrence dependencies, not only captured native helpers', () => {
  for (const replace of [false, true]) {
    const child = divBy(2)
    const outer = recur('outer', {fns: {child}, zero: 0, next: (_, p, {child}) => p.plus(child(2))})
    const warm = fun('warm').fns({outer}).returns(({outer}) => ({out: outer(4)}))
    expect(warm.run({})).toEqual({out: 4})
    if (replace) outer.uses!.child = fn(1, 'x => x + 1')
    else child.js = 'x => x + 1'
    const f = fun('current dependency').fns({outer}).returns(({outer}) => ({out: outer(4)}))
    expect(() => f.run({})).toThrow('compiled()')
    expect(f.compiled()({})).toEqual({out: 4}) // recur retains its originally generated/inlined source.
    const r = rule('current dependency').fns({outer}).state({out: 0}).step(({outer}) => ({out: outer(4)}))
    expect(() => r.interpreter()).toThrow('{compileHelpers: true}')
    for (const run of [r.interpreter({compileHelpers: true}), r.compiled()]) expect(run.step({}, run.init({}), {}).scalars.out).toBe(4)
  }
})

test('unchanged copied builders and JSON machines retain native implementations', () => {
  const q = {...divBy(2)}, r = {...modBy(3)}
  const inner = recur('inner', {args: ['a'], zero: ({a}) => a, next: (_, p) => p.plus(1)})
  const total = {...recur('total', {args: ['a'], fns: {inner, q}, zero: ({a}) => a, next: (x, p, {inner, q}) => p.plus(inner(x, q(4)))})}
  const f = fun('unchanged').fns({q, r, total}).inputs({n: nat}).returns(({n, q, r, total}) => ({q: q(n), r: r(n), total: total(n, 3)}))
  expect(f.run({n: 4})).toEqual({q: 2, r: 1, total: 17})
  expect(f.compiled()({n: 4})).toEqual(f.run({n: 4}))
  const m = JSON.parse(JSON.stringify(f.rule.machine))
  expect(Object.values(m.fns as Record<string, Fn>).every(sourceFreeFn)).toBe(true)
  const run = interpret(m)
  expect(run.step({}, run.init({}), {n: 4}).scalars['out.total']).toBe(17)
})

test('recurrence arguments reject JavaScript keywords and shadowed runtime globals without compiling', () => {
  for (const name of ['Math', 'Number', 'RangeError', 'class', 'return', 'await', 'arguments', 'eval']) {
    expect(() => recur('shadow', {args: [name], zero: 0, next: (_, p, env) => min(p.plus(1), env[name]!)})).toThrow("can't name an argument")
    const q = recur(name, {zero: 0, next: (_, p) => p.plus(1)})
    const f = fun('safe alias').fns({q}).inputs({n: nat}).returns(({n, q}) => ({out: q(n)}))
    expect(f.run({n: 4})).toEqual({out: 4})
    expect(f.compiled()({n: 4})).toEqual({out: 4})
  }
  // Map is captured outside the generated argument scope; unlike Math/Number it is safe as an argument.
  const mapped = recur('mapArgument', {args: ['Map'], zero: ({Map}) => Map, next: (_, p) => p.plus(1)})
  const mapArg = fun('safe Map argument').fns({mapped}).inputs({n: nat}).returns(({n, mapped}) => ({out: mapped(n, 3)}))
  expect(mapArg.run({n: 4})).toEqual({out: 7})
  expect(mapArg.compiled()({n: 4})).toEqual({out: 7})
  const q = recur('aliased', {fns: {Math: divBy(2)}, zero: 0, next: (_, p, {Math}) => p.plus(Math(2))})
  const f = fun('safe helper alias').fns({q}).inputs({n: nat}).returns(({n, q}) => ({out: q(n)}))
  expect(f.run({n: 4})).toEqual({out: 4})
  expect(f.compiled()({n: 4})).toEqual({out: 4})
})

test('fresh import, builtins and recurrences work with Function blocked before construction', () => {
  const url = new URL('./dsl.ts', import.meta.url).href
  const source = `
let attempts = 0;
globalThis.Function = new Proxy(globalThis.Function, {construct() { attempts++; throw Error('dynamic code blocked'); }, apply() { attempts++; throw Error('dynamic code blocked'); }});
const {bool, divBy, fn, fun, min, modBy, nat, oneOf, record, recur, rule, when} = await import(${JSON.stringify(url)});
const {fnValue, interpret} = await import(new URL('./machine.ts', ${JSON.stringify(url)}).href);
const f = fun('csp').inputs({n:nat, enabled:bool, mode:oneOf('left','right')}).returns(({n,enabled,mode}) => ({q:n.divBy(2),r:n.modBy(2),rounded:n.ceilTo(2),enabled,mode,selected:when(enabled,n,0)}));
const got = f.run({n:5,enabled:true,mode:'right'});
const arithmeticMachine = JSON.parse(JSON.stringify(f.rule.machine)), arithmeticRun = interpret(arithmeticMachine);
const arithmeticState = arithmeticRun.step({},arithmeticRun.init({}),{n:5,enabled:1,mode:1});
if(arithmeticState.scalars['out.q']!==2 || arithmeticState.scalars['out.r']!==1) throw Error('serialized arithmetic');
const q = divBy(2), r = modBy(3);
const inner = recur('inner', {args:['a'], zero:({a})=>a, next:(_,p)=>p.plus(1)}, {'at least a':(_,p,{a})=>p.atLeast(a)});
const many = recur('many', {args:['a','b','c','d'], fns:{q,r,inner}, zero:({a,q,r})=>q(a).plus(r(a)), next:(x,p,{b,c,d,inner})=>p.plus(inner(x,b)).plus(min(c,d))});
const built = fun('builtins').fns({q,r,many}).inputs({n:nat}).returns(({n,q,r,many})=>({q:q(n),r:r(n),v:many(n,1000,2000,3000,999),constant:many(2,1000,2000,3000,999)}));
const builtResult = built.run({n:3});
if(JSON.stringify(builtResult)!==JSON.stringify({q:1,r:0,v:9501,constant:6500})) throw Error(JSON.stringify(builtResult));
const rr = rule('builtin rule').fns({q,r,many}).inputs({n:nat}).state({quotient:0,remainder:0,v:0}).step(({n,q,r,many})=>({quotient:q(n),remainder:r(n),v:many(n,1000,2000,3000,999)}));
const machine = rr.machine; // Materialization, as well as construction and execution, is inside the CSP block.
for(const run of [rr.interpreter(), interpret(JSON.parse(JSON.stringify(machine)))]) {
  let st = run.init({});
  for(const [n,v] of [[3,9501],[1,3500],[4,12503]]) {
    st=run.step({},st,{n});
    if(st.scalars.v!==v || st.scalars.quotient!==Math.floor(n/2) || st.scalars.remainder!==n%3) throw Error(JSON.stringify(st.scalars));
  }
}
const unary = rule('unary').fns({inc:recur('inc',{zero:0,next:(_,p)=>p.plus(1)})}).state({v:0}).step(({inc})=>({v:inc(7)}));
if(fnValue(JSON.parse(JSON.stringify(unary.machine.fns.inc)),9)!==9) throw Error('unary fnValue');
// List-fold induction constructs its own constant data helpers; these are source-free too.
const list = rule('list csp').carriesList('Lines', record({amount:nat}), {total:{from:0,step:(acc,l)=>acc.plus(l.amount)}}, {'natural':({total})=>total.atLeast(0)})
  .state({v:0}).step(({Lines})=>({v:Lines.fold.total}));
const lists = list.interpreter(), listInput = list.encodeInput({Lines:[{amount:3},{amount:4}]});
if(lists.step({},lists.init({}),listInput).scalars.v!==7) throw Error('list helper');
// Modified library metadata must be rejected without trying Function, including literal folding.
for(const change of [q=>{q.js='x => x + 1'},q=>{q.arity=2},q=>{q.direct.divisor=4}]) {
  const q=divBy(2); change(q);
  const changed=fun('changed').fns({q}).returns(({q})=>({out:q(...Array(q.arity).fill(4))}));
  let blocked=false;
  try { changed.run({}) } catch(e) { blocked=String(e).includes('compiled()') }
  if(!blocked) throw Error('changed metadata used a native implementation');
}
for(const replace of [false,true]) {
  const child=divBy(2),outer=recur('changedChild',{fns:{child},zero:0,next:(_,p,{child})=>p.plus(child(2))});
  if(replace) outer.uses.child=fn(1,'x=>x+1'); else child.js='x=>x+1';
  let refused=0;
  try { fun('current child').fns({outer}).returns(({outer})=>({out:outer(4)})).run({}) } catch(e) { if(String(e).includes('compiled()')) refused++ }
  try { rule('current child').fns({outer}).state({out:0}).step(({outer})=>({out:outer(4)})).interpreter() } catch(e) { if(String(e).includes('{compileHelpers: true}')) refused++ }
  if(refused!==2) throw Error('actual child source was not refused before compilation');
}
for(const name of ['Math','Number','class']) {
  let blocked=false;
  try { recur('shadow',{args:[name],zero:0,next:(_,p,e)=>min(p.plus(1),e[name])}) } catch(e) { blocked=true }
  if(!blocked) throw Error('unsafe recurrence name accepted');
}
let refused=0;
for(const source of ['x => x + 1', x=>x+1, x=>Function('x','return x + 1')(x), 'this is not JavaScript']) {
  const custom=fn(1,source);
  const wrapped=recur('wrapped',{fns:{custom},zero:({custom})=>custom(0),next:(_,p,{custom})=>custom(p)});
  const outer=recur('outer',{fns:{wrapped},zero:0,next:(x,_,{wrapped})=>wrapped(x)});
  for(const inc of [custom,wrapped,outer]) {
    const helper=fun('blocked helper').inputs({n:nat}).fns({inc}).returns(({inc})=>({out:inc(1)}));
    try{helper.run({n:1})}catch(e){if(String(e).includes('compiled()')) refused++}
    try{rule('csp helper').fns({inc}).state({n:0}).step(({inc})=>({n:inc(1)})).interpreter()}catch(e){if(String(e).includes('{compileHelpers: true}')) refused++}
  }
}
if(attempts || refused!==24 || JSON.stringify(got)!==JSON.stringify({q:2,r:1,rounded:6,enabled:true,mode:'right',selected:5})) throw Error(JSON.stringify({attempts,refused,got}));
console.log('CSP default passed');
`
  const result = spawnSync(process.execPath, ['--eval', source], {encoding: 'utf8', timeout: 15000, env: {...process.env, GDP_CYCLIC_LOG: '0'}})
  expect({status: result.status, stderr: result.stderr}).toEqual({status: 0, stderr: ''})
  expect(result.stdout.trim()).toBe('CSP default passed')
})

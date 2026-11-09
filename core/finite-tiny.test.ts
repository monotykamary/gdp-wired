import {test, expect} from 'bun:test'
import {type Machine, type Law, all, any, atMost, get, n, not, plus, same, times, x, interpret, less, ite, tuple} from './machine.ts'
import {tinyFiniteCandidates} from './finite-tiny.ts'
import {finiteEvaluator} from './finite-houdini.ts'
import {withWall} from '../kernel/prove.ts'
import {checkWall, WallExpired} from './wall.ts'
const counter = (): Machine => ({name: 'anonymous', params: [], inputs: [], state: {value: n(0)}, counts: {unused: {j: 'unusedRow', key: 'k', below: n(1), body: n(0)}}, step: {state: {value: plus(x('value'), n(1))}}})
test('proposals cross the independent full-family/interpreter trust boundary', () => {
  const source = counter(), law: Law = {name: 'arbitrary', holds: atMost(x('value'), n(0))}, test = finiteEvaluator(source), run = interpret(source)
  let accepted = 0
  const stats = tinyFiniteCandidates(source, source, [law], {}, (pre, request, violated) => {
    expect(test(law, {}, pre)).toBe(true)
    expect(test(law, {}, run.step({}, pre, request))).toBe(false)
    expect(violated).toEqual([law]); accepted++; return true
  })
  expect(accepted).toBe(1); expect(stats.exhausted).toBe(false); expect(stats.unsupported).toEqual([])
})
test('whole family constrains pre, not just the proposed target', () => {
  const source = counter(), a: Law = {name: 'a', holds: same(x('value'), n(0))}, b: Law = {name: 'b', holds: same(x('value'), n(1))}
  const stats = tinyFiniteCandidates(source, source, [a, b], {}, () => { throw Error('impossible full-family pre') })
  expect(stats.candidates).toBe(0); expect(stats.exhausted).toBe(true)
})
test('row strides come from lifted count bodies; identifiers have no meaning', () => {
  const source: Machine = {name: 'unrelated', params: ['width'], inputs: [], state: {}, maps: {table: 0}, step: {maps: {table: {key: n(17), value: n(1)}}}}
  const m: Machine = {...source, counts: {count: {j: 'r', key: 'c', below: x('width'), body: get('table', plus(times(17, x('r')), x('c')))}}}
  const law: Law = {name: 'empty', forall: 'z', holds: any(not(less(x('z'), x('width'))), same(get('count', x('z')), n(0)))}
  const stats = tinyFiniteCandidates(source, m, [law], {width: 2}, (pre, request) => {
    const evaluate = finiteEvaluator(m)
    expect(evaluate(law, {width: 2}, pre)).toBe(true)
    expect(evaluate(law, {width: 2}, interpret(source).step({width: 2}, pre, request))).toBe(false)
  })
  expect(stats.scope.cells.table).toEqual([0, 1, 17, 18]); expect(stats.candidates).toBe(1)
})
test('unsupported external function never establishes exhaustion', () => {
  const source = {...counter(), fns: {opaque: {js: 'x => x'}}}, law: Law = {name: 'opaque', holds: same(get('opaque', x('value')), n(0))}
  const stats = tinyFiniteCandidates(source, source, [law], {}, () => { throw Error('unsupported') })
  expect(stats.unsupported).toContain('external function'); expect(stats.exhausted).toBe(false)
})
test('expired wall returns honest interruption and never extends the parent', () => {
  const stats = withWall(performance.now() - 1, () => tinyFiniteCandidates(counter(), counter(), [], {}, () => {}))
  expect(stats.timedOut).toBe(true); expect(stats.exhausted).toBe(false)
  expect(() => withWall(performance.now() - 1, () => checkWall('parent'))).toThrow(WallExpired)
})
test('a rejected proposal resumes rather than stopping or dropping', () => {
  const source = counter(), law: Law = {name: 'not zero', holds: not(same(x('value'), n(1)))}
  let proposals = 0
  const stats = tinyFiniteCandidates(source, source, [law], {}, () => { proposals++; return false })
  expect(proposals).toBe(1); expect(stats.exhausted).toBe(false)
})
test('dispatch slicing and irrelevant-coordinate quotienting use syntax, not names', () => {
  const source: Machine = {...counter(), inputs: ['selector', 'unread'], assume: less(x('selector'), n(2)), step: {flags: {idle: same(x('selector'), n(0)), change: same(x('selector'), n(1))}, state: {value: ite({op:'flag', name:'change'}, n(1), x('value'))}}}
  const law: Law = {name: 'preserve', holds: same(x('value'), n(0))}
  const stats = tinyFiniteCandidates(source, source, [law], {}, (pre, request) => {
    expect(request).toEqual({selector:1, unread:0})
    expect(finiteEvaluator(source)(law, {}, interpret(source).step({}, pre, request))).toBe(false)
  })
  expect(stats.candidates).toBe(1)
})
test('native tuple rows are inferred without a row-name convention', () => {
  const source: Machine = {name:'tuple rows', params:[], inputs:[], state:{}, maps:{R:0}, step:{maps:{R:{key:tuple([n(1),n(1)]),value:n(1)}}}}
  const m: Machine = {...source, counts:{c:{j:'u',key:'v',below:n(2),body:get('R',tuple([x('u'),x('v')]))}}}
  const law: Law = {name:'empty',forall:'u0',holds:any(not(less(x('u0'),n(2))),same(get('c',x('u0')),n(0)))}
  const stats=tinyFiniteCandidates(source,m,[law],{},(pre,request)=>{
    const evaluate=finiteEvaluator(m)
    expect(evaluate(law,{},pre)).toBe(true)
    expect(evaluate(law,{},interpret(source).step({},pre,request))).toBe(false)
  })
  expect(stats.scope.cells.R).toEqual([0,1,2,4]); expect(stats.candidates).toBe(1)
})
test('the callback, not a screen, must enforce lifted preconditions and facts', () => {
  const source=counter(), law:Law={name:'zero',holds:same(x('value'),n(0))}
  const m:Machine={...source, pre:same(n(0),n(1)), facts:[{name:'all facts',holds:same(n(1),n(0))}]}
  let proposals=0, certified=0
  const stats=tinyFiniteCandidates(source,m,[law],{},(pre,request,violated)=>{
    proposals++
    const evaluate=finiteEvaluator(m), required=[law,...m.facts!,{name:'pre',holds:m.pre!}]
    if(!required.every(l=>evaluate(l,{},pre)===true)) return false
    const post=interpret(source).step({},pre,request)
    if(violated.some(l=>evaluate(l,{},post)===false)) certified++
    return certified>0
  })
  expect(proposals).toBeGreaterThan(0); expect(certified).toBe(0); expect(stats.exhausted).toBe(false)
})
test('one shared transition may propose several independently checked helpers',()=>{
  const source=counter(),a:Law={name:'a',holds:atMost(x('value'),n(0))},b:Law={name:'b',holds:same(x('value'),n(0))}
  let proposals=0
  const stats=tinyFiniteCandidates(source,source,[a,b],{},(pre,request,violated)=>{
    proposals++;expect(violated).toEqual([a,b])
    const evaluate=finiteEvaluator(source),post=interpret(source).step({},pre,request)
    expect([a,b].every(l=>evaluate(l,{},pre)===true&&evaluate(l,{},post)===false)).toBe(true)
  })
  expect(proposals).toBe(1);expect(stats.candidates).toBe(1)
})
test('inactive flags cannot prune an unconditional update elsewhere',()=>{
  const source:Machine={...counter(),state:{value:n(0),other:n(0)},step:{flags:{inactive:same(n(0),n(1))},state:{value:ite({op:'flag',name:'inactive'},n(1),x('value')),other:plus(x('other'),n(1))}}}
  const law:Law={name:'other remains zero',holds:same(x('other'),n(0))}
  const stats=tinyFiniteCandidates(source,source,[law],{},(pre,request,violated)=>{
    const evaluate=finiteEvaluator(source),post=interpret(source).step({},pre,request)
    expect(violated).toEqual([law]);expect(evaluate(law,{},pre)).toBe(true);expect(evaluate(law,{},post)).toBe(false)
  })
  expect(stats.candidates).toBe(1);expect(stats.completed).toBe(true)
})
test('partial atoms preserve all finite pre-states through both polarities', () => {
  const source: Machine = {...counter(), counts: {unused: {j: 'row', key: 'k', below: n(1), body: n(0)}},
    state: {a: n(0), b: n(0)}, step: {state: {a: plus(x('b'), n(1)), b: x('a')}}}
  const a = x('a'), b = x('b'), choose = ite(less(a, b), plus(a, n(1)), b)
  const predicates = [same(a, b), not(same(a, b)), less(a, b), atMost(choose, b), same(choose, n(1)),
    all(not(same(a, n(0))), any(same(b, n(0)), less(a, b))),
    not(any(less(a, b), same(a, n(0))))]
  const evaluate = finiteEvaluator(source), run = interpret(source)
  for (const holds of predicates) {
    const law: Law = {name: 'finite polarity case', holds}, actual: string[] = [], expected: string[] = []
    for (const av of [0, 1, 2]) for (const bv of [0, 1, 2]) {
      const pre: import('./machine.ts').State = {scalars: {a: av, b: bv}, maps: {}}
      if (evaluate(law, {}, pre) === true && evaluate(law, {}, run.step({}, pre, {})) === false) expected.push(`${av},${bv}`)
    }
    const stats = tinyFiniteCandidates(source, source, [law], {}, pre => {
      actual.push(`${pre.scalars.a},${pre.scalars.b}`)
      return false // Observe every proposal, not just the first target.
    }, {valueDomain: [0, 1, 2]})
    expect(stats.completed).toBe(true)
    expect(stats.unsupported).toEqual([])
    expect(actual.sort()).toEqual(expected.sort())
  }
})
test('request atoms wait for every conditional-term dependency', () => {
  const source: Machine = {...counter(), inputs: ['left', 'right'],
    assume: all(atMost(x('left'), n(2)), atMost(x('right'), n(2)),
      not(same(ite(less(x('left'), x('right')), x('right'), x('left')), n(0)))),
    step: {state: {value: plus(x('left'), x('right'))}}}
  const law: Law = {name: 'zero', holds: same(x('value'), n(0))}, actual: string[] = []
  const stats = tinyFiniteCandidates(source, source, [law], {}, (pre, request) => {
    expect(finiteEvaluator(source)(law, {}, interpret(source).step({}, pre, request))).toBe(false)
    const {left, right} = request
    if (typeof left !== 'number' || typeof right !== 'number') throw new Error('expected scalar request')
    actual.push(`${left},${right}`)
    return false
  })
  expect(stats.completed).toBe(true)
  expect(actual.sort()).toEqual(['0,1', '0,2', '1,0', '1,1', '1,2', '2,0', '2,1', '2,2'])
})
test('large logical predicates split at the native-body cap without losing proposals', () => {
  const source = counter(), law: Law = {name: 'many equalities', holds: all(...Array.from({length: 4096}, () => same(x('value'), n(0))))}
  let proposals = 0
  const stats = tinyFiniteCandidates(source, source, [law], {}, (pre, request) => {
    proposals++
    const evaluate = finiteEvaluator(source)
    expect(evaluate(law, {}, pre)).toBe(true)
    expect(evaluate(law, {}, interpret(source).step({}, pre, request))).toBe(false)
  })
  expect(stats.unsupported).toEqual([])
  expect(stats.completed).toBe(true)
  expect(proposals).toBe(1)
})
test('state-only no-op has no proposals in the recorded finite scope', () => {
  const source = counter(); source.step = {}
  const law: Law = {name: 'zero or one', holds: all(atMost(x('value'), n(1)))}
  const stats = tinyFiniteCandidates(source, source, [law], {}, () => { throw Error('no-op') })
  expect(stats.candidates).toBe(0); expect(stats.exhausted).toBe(true)
})

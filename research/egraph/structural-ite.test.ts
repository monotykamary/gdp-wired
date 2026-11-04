import {expect,test} from 'bun:test'
import {get,n,x,same,not,type E} from '../../core/machine.ts'
import {Meter} from './match.ts'
import {IndexedEGraph} from './indexed-match.ts'
import {IteEGraph} from './ite.ts'
const native=()=>new IndexedEGraph(new Meter(100000),512,true)
test('native ITE and encoded ITE agree on whole-expression and nested-guard bindings',()=>{
  const cases:E[]=[
    {op:'if',c:{op:'<',a:x('a'),b:n(3)},then:x('b'),else:n(4)},
    {op:'if',c:{op:'and',xs:[not(same(x('a'),n(2))),{op:'or',xs:[]}]},then:x('b'),else:n(4)}
  ]
  for(const term of cases){
    if(term.op!=='if')throw Error('expected ITE fixture')
    const a=new IteEGraph(new Meter(100000),512,(m,k)=>new IndexedEGraph(m,k)),b=native()
    a.seed([same(get('F',term),n(9))]);b.seed([same(get('F',term),n(9))])
    expect(b.match([get('F',x('whole'))],['whole'])).toEqual(a.match([get('F',x('whole'))],['whole']))
    expect(b.match([get('F',term)],[])).toEqual(a.match([get('F',term)],[]))
    expect(b.match([get('F',{...term,else:n(5)})],[])).toEqual([])
    expect(b.match([get('F',{...term,then:term.else,else:term.then})],[])).toEqual([])
  }
})
test('native guard structure is not simplified, reordered or allowed to escape as an E binding',()=>{
  const a=same(x('a'),n(1)),b=same(x('b'),n(2)),g=native()
  const term:E={op:'if',c:{op:'and',xs:[a,b]},then:n(1),else:n(0)}
  g.seed([same(get('F',term),n(7))])
  expect(g.match([get('F',{...term,c:{op:'and',xs:[b,a]}})],[])).toEqual([])
  expect(g.match([get('F',{...term,c:{op:'or',xs:[a,b]}})],[])).toEqual([])
  for(const binding of g.match([x('whole')],['whole']))expect(['and','or','not','=','<','<='].includes(binding.whole!.op)).toBe(false)
})
test('native guard congruence preserves equal children and unsupported guards fail closed',()=>{
  const g=native(),term:E={op:'if',c:same(x('a'),n(1)),then:x('a'),else:n(0)}
  g.seed([same(x('a'),x('b')),same(get('F',term),n(2))])
  expect(g.match([get('F',{...term,c:same(x('b'),n(1)),then:x('b')})],[])).toEqual([{}])
  expect(()=>native().add({op:'if',c:{op:'flag',name:'p'},then:n(1),else:n(0)})).toThrow('unsupported ITE')
  expect(()=>new IndexedEGraph(new Meter(10000),2,true).add(term)).toThrow('node limit')
})

import {expect,test} from 'bun:test'
import {get,n,x,same,not,type C,type E} from '../../core/machine.ts'
import {IndexedEGraph} from './indexed-match.ts'
import {TriggerIndex} from './trigger-index.ts'
import {Meter} from './match.ts'
const pattern=get('Vote',x('k'))
test('trigger index scans every hypothesis and agrees with full closure on selected bindings',()=>{
  for(const late of [false,true]){
    const eq=same(get('F',x('a')),get('F',x('b'))),cs:C[]=[{op:'<',a:get('Other',x('z')),b:n(9)},same(get('Vote',get('F',x('a'))),n(1)),same(get('Vote',get('F',x('b'))),n(1))]
    if(late)cs.push(eq);else cs.unshift(eq)
    const full=new IndexedEGraph(new Meter(100000),512,true),small=new TriggerIndex(new Meter(100000),[pattern])
    full.seed(cs);small.seed(cs)
    const norm=(xs:Record<string,E>[])=>xs.map(b=>full.root(full.add(b.k!))).sort((a,b)=>a-b)
    expect(norm(small.match([pattern],['k']))).toEqual(norm(full.match([pattern],['k'])))
    expect(small.stats.hypothesesCompleted).toBe(cs.length)
    expect(small.stats.positiveEqualities).toBe(3)
  }
})
test('trigger index never asserts negated, disjunctive or ITE-guard equalities',()=>{
  const eq=same(x('a'),x('b')),pair:E={op:'tup',a:x('a'),b:x('b')},p=get('Vote',{op:'tup',a:x('q'),b:x('q')})
  for(const c of [not(eq),{op:'or',xs:[eq,same(x('a'),n(1))]} as C,same({op:'if',c:eq,then:n(1),else:n(0)},n(1))]){
    const g=new TriggerIndex(new Meter(100000),[p]);g.seed([c,same(get('Vote',pair),n(7))]);expect(g.match([p],['q'])).toEqual([])
  }
})
test('irrelevant observations are scanned but not materialized; selected children remain charged nodes',()=>{
  const g=new TriggerIndex(new Meter(100000),[pattern],8)
  const cs:C[]=Array.from({length:20},(_,i)=>({op:'<',a:get('Other'+i,x('a'+i)),b:n(9)}))
  cs.push({op:'<',a:get('Vote',x('actual')),b:n(9)});g.seed(cs)
  expect(g.stats.hypothesesCompleted).toBe(21);expect(g.graph.size).toBe(2);expect(g.match([pattern],['k'])).toEqual([{k:x('actual')}])
  const small=new TriggerIndex(new Meter(100000),[pattern],2)
  expect(()=>small.seed([{op:'<',a:get('Vote',{op:'tup',a:x('a'),b:x('b')}),b:n(9)}])).toThrow('node limit')
  expect(()=>small.match([pattern],['k'])).toThrow('incomplete')
})
test('unsupported irrelevant syntax and scan fuel cannot be bypassed',()=>{
  const g=new TriggerIndex(new Meter(100000),[pattern]);expect(()=>g.seed([same(get('Vote',n(1)),n(1)),{op:'flag',name:'p'}])).toThrow('unsupported')
  expect(()=>g.match([pattern],['k'])).toThrow('incomplete')
  const h=new TriggerIndex(new Meter(3),[pattern]);expect(()=>h.seed([{op:'<',a:get('Other',x('a')),b:n(9)}])).toThrow('budget')
  expect(()=>new TriggerIndex(new Meter(100),[x('p')])).toThrow('read-headed')
})

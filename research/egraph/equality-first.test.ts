import {expect,test} from 'bun:test'
import {get,n,x,same,not,type C,type E} from '../../core/machine.ts'
import {IndexedEGraph} from './indexed-match.ts'
import {Meter} from './match.ts'
const f=(name:string,a:E)=>get(name,a)
const graph=()=>new IndexedEGraph(new Meter(100000),512,true)
test('early equalities match late equalities modulo the same asserted equivalence classes',()=>{
  const a=graph(),b=graph(),cs:C[]=[same(f('G',f('F',x('a'))),n(1)),same(x('b'),x('a')),same(f('G',f('F',x('b'))),n(2))]
  a.seed(cs);b.seed(cs,true)
  const normalize=(matches:Record<string,E>[])=>matches.map(m=>Object.entries(m).map(([k,v])=>[k,a.root(a.add(v))])).sort((u,v)=>JSON.stringify(u).localeCompare(JSON.stringify(v)))
  for(const patterns of [[f('F',x('q'))],[f('G',x('q'))]])expect(normalize(b.match(patterns,['q']))).toEqual(normalize(a.match(patterns,['q'])))
  expect(a.root(a.add(n(1)))).toBe(a.root(a.add(n(2))))
  expect(b.root(b.add(n(1)))).toBe(b.root(b.add(n(2))))
  expect(b.stats.hypothesesCompleted).toBe(cs.length)
  expect(b.stats.rebuildPasses).toBeGreaterThan(0)
})
test('early scheduling does not assert equalities from disjunction, negation, or an ITE guard',()=>{
  const eq=same(x('a'),x('b')),term:E={op:'tup',a:x('a'),b:x('b')}
  for(const c of [not(eq),{op:'or',xs:[eq,same(x('a'),n(1))]} as C,same({op:'if',c:eq,then:n(1),else:n(0)},n(1))]){
    const g=graph();g.seed([c,same(get('R',term),n(7))],true)
    expect(g.match([get('R',{op:'tup',a:x('q'),b:x('q')})],['q'])).toEqual([])
  }
})
test('early scheduling charges traversal/rebuilds and retains the same node cap',()=>{
  const meter=new Meter(8),g=new IndexedEGraph(meter,512,true)
  expect(()=>g.seed([same(x('a'),x('b')),same(f('F',x('a')),n(1))],true)).toThrow('budget')
  expect(meter.used).toBe(8)
  const h=new IndexedEGraph(new Meter(100000),2,true)
  expect(()=>h.seed([same(x('a'),x('b')),same(x('c'),x('d'))],true)).toThrow('node limit')
  expect(h.size).toBe(2)
})

import {expect,test} from 'bun:test'
import {get,n,x,same,not,type C,type E} from '../../core/machine.ts'
import {tuple} from '../../kernel/kernel.ts'
import {EGraph,Exhausted,Meter} from './match.ts'
import {IndexedEGraph} from './indexed-match.ts'
import {IteEGraph} from './ite.ts'
const f=(name:string,...args:E[])=>get(name,tuple(args))
const indexed=()=>new IndexedEGraph(new Meter(1_000_000))
test('indexed matching agrees with full-scan matching across positive/negative equality contexts',()=>{
  for(let mask=0;mask<16;mask++){
    const eq=same(x('a'),x('b'))
    const cs:C[]=[same(f('R',f('F',x('a')),f('F',x('b'))),n(1)),same(f('S',x('a'),x('c')),n(1)),same(f('S',x('d'),x('b')),n(1))]
    if(mask&1)cs.push(eq);if(mask&2)cs.push(not(eq));if(mask&4)cs.push({op:'or',xs:[eq,same(x('a'),x('c'))]});if(mask&8)cs.push(same(f('S',x('a'),x('b')),n(1)))
    const a=new EGraph(new Meter(1_000_000)),b=indexed();a.seed(cs);b.seed(cs)
    for(const [patterns,keys]of [[[f('R',x('z'),x('z'))],['z']],[[f('S',x('u'),x('v')),f('S',x('v'),x('u'))],['u','v']],[[f('F',x('u'))],['u']],[[x('u')],['u']]] as [E[],string[]][]){expect(b.match(patterns,keys)).toEqual(a.match(patterns,keys))}
  }
})
test('indexed congruence reaches a fixed point and invalidates indexes on incremental seed',()=>{
  const g=indexed();g.seed([same(f('G',f('F',x('a'))),n(1)),same(f('G',f('F',x('b'))),n(2))])
  expect(g.match([f('F',x('u'))],['u'])).toHaveLength(2)
  g.seed([same(x('a'),x('b'))]);expect(g.match([f('F',x('u'))],['u'])).toHaveLength(1)
  expect(g.root(g.add(n(1)))).toBe(g.root(g.add(n(2))))
  const count=g.size;g.add(f('G',f('F',x('b'))));expect(g.size).toBe(count)
})
test('indexed join correlates bindings and refuses unbound keys and symbol collisions',()=>{
  const g=indexed();g.seed([same(f('R',x('a'),x('b')),n(1)),same(f('S',x('a'),x('c')),n(1)),same(f('S',x('d'),x('b')),n(1))])
  expect(g.match([f('R',x('u'),x('v')),f('S',x('u'),x('v'))],['u','v'])).toEqual([])
  expect(g.match([f('R',x('u'),x('v'))],['u','v','w'])).toEqual([])
  expect(g.match([f('absent',x('u'))],['u'])).toEqual([])
  expect(g.match([f('R',x('u'),x('v'))],['u','v'],0)).toEqual([])
})
test('indexed cyclic classes, deterministic caps and repeated merging terminate',()=>{
  const g=indexed();g.seed([same(x('a'),f('F',x('a')))]);expect(g.match([f('F',f('F',x('u')))],['u'],1)).toHaveLength(1)
  expect(g.merge(g.add(x('a')),g.add(x('a')))).toBe(false)
  const h=indexed();h.add(f('F',x('a')));h.add(f('F',x('b')));expect(h.match([f('F',x('u'))],['u'],1)).toEqual([{u:x('a')}])
})
test('indexed work/node/deadline limits and unsupported inputs fail closed',()=>{
  const m=new Meter(2);expect(()=>new IndexedEGraph(m).add(f('F',x('a')))).toThrow(Exhausted);expect(m.used).toBe(2)
  expect(()=>new IndexedEGraph(new Meter(100),0).add(x('a'))).toThrow('node limit')
  expect(()=>new IndexedEGraph(new Meter(100,performance.now()-1)).add(x('a'))).toThrow(Exhausted)
  expect(()=>indexed().seed([{op:'flag',name:'p'}])).toThrow('unsupported')
  expect(()=>indexed().add({op:'if',c:same(n(0),n(0)),then:n(1),else:n(2)})).toThrow('unsupported')
  expect(()=>new IndexedEGraph(new Meter(10),-1)).toThrow('invalid')
})
test('same ITE adapter with indexed backend preserves guards, both branches and reserved namespace refusal',()=>{
  const make=()=>new IteEGraph(new Meter(1_000_000),512,(m,k)=>new IndexedEGraph(m,k))
  const v:E={op:'if',c:{op:'and',xs:[not(same(x('a'),n(2))),{op:'or',xs:[]}]},then:x('b'),else:n(3)}
  const g=make();g.seed([same(get('F',v),n(9))]);expect(g.match([get('F',x('v'))],['v'])).toEqual([{v}])
  expect(g.match([get('F',{...v,else:n(4)})],[])).toEqual([])
  expect(()=>make().seed([same(get('\u0000astra-ite:if',x('a')),n(0))])).toThrow('reserved')
})

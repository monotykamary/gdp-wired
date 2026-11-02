import {expect, test} from 'bun:test'
import {holdsAt} from './exists.ts'
import {type Law, type Machine, type State, carriedView, evalC, n, x} from './machine.ts'

// The previous interpreter implementation is the differential oracle.
function direct(m: Machine, law: Law, p: Record<string, number>, st: State, b: number): boolean {
  const view = carriedView(m, st, {}, undefined, p)
  const keys = [law.forall, ...(law.keys ?? [])].filter((k): k is string => !!k)
  const go = (env: Record<string, number>, ks: string[]): boolean => ks.length
    ? Array.from({length:b}, (_, k) => k).every(k => go({...env, [ks[0]!]:k}, ks.slice(1)))
    : evalC(law.holds, {...env, ...st.scalars}, view, m)
  return go({...p}, keys)
}

test('sample laws match interpreter tuple order, shadowing, duplicate names and empty domains', () => {
  const m: Machine = {name:'sample law differential', params:['p'], inputs:[], state:{s:n(0)}, maps:{A:0}, step:{}}
  const laws: Law[] = []
  for (const name of ['i', 's', '__proto__']) for (const keys of [[], ['j'], [name], ['j',name]]) {
    laws.push({name:'bounded',forall:name,keys,holds:{op:'<=',a:x(name),b:x('p')}})
    laws.push({name:'cell',forall:name,keys,holds:{op:'=',a:{op:'get',map:'A',key:x(name)},b:n(0)}})
  }
  laws.push({name:'short circuit',holds:{op:'or',xs:[{op:'=',a:n(0),b:n(0)},{op:'=',a:x('missing'),b:n(0)}]}})
  for (let value=0; value<4; value++) for (const b of [0,1,3]) {
    const st: State = {scalars:{s:value},maps:{A:new Map([[1,value]])}}
    const p={p:value}
    for (const law of laws) expect(holdsAt(m,law,p,st,b),JSON.stringify({law:law.name,forall:law.forall,keys:law.keys,value,b})).toBe(direct(m,law,p,st,b))
    expect(st.scalars).toEqual({s:value})
    expect(p).toEqual({p:value})
  }
})

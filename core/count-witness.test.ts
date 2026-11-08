import {expect, test} from 'bun:test'
import {certFor} from './counts.ts'
import {all, get, ite, n, not, same, tuple, x} from './machine.ts'
import {checkMC, mcGoal} from '../kernel/kernel.ts'
import {clock, grow} from '../kernel/prove.ts'

const decls = [{map: 'RowCount', j: 'row', key: 'member', below: n(2), body: ite(same(get('Rows', tuple([x('row'), x('member')])), n(1)), n(1), n(0))}]
const goal = (row: number) => ({name: 'one known member rules out an empty count', hyps: [same(get('Rows', tuple([n(row), n(1)])), n(1)), same(get('RowCount', n(0)), n(0))]})

test('counted tuple members yield a singleton pick, checked by the normal kernel', () => {
  const g = goal(0), full = certFor(g, decls, true)
  expect(full.picks.some(([, terms]) => terms.length === 1 && JSON.stringify(terms[0]) === JSON.stringify(n(1)))).toBe(true)
  const cert = {reads: full.reads, insts: [], picks: full.picks}
  const q = mcGoal(g.hyps, decls, cert)!
  const proof = grow({name: g.name, hyps: q.hyps}, new Map(), {nodes: 0, until: clock() + 1500})
  expect('tree' in proof).toBe(true)
  if ('tree' in proof) expect(checkMC(g.hyps, decls, {...cert, tree: proof.tree})).toBe(true)
})

test('the wide pool proposes a checked three-count partition identity', () => {
  const member = x('member'), inside = same(get('Inside', member), n(1)), whole = same(get('Whole', member), n(1))
  const base = {j: 'unused', key: 'member', below: n(3)}
  const ds = [
    {...base, map: 'All', body: ite(whole, n(1), n(0))},
    {...base, map: 'In', body: ite(all(whole, inside), n(1), n(0))},
    {...base, map: 'Out', body: ite(all(whole, not(inside)), n(1), n(0))},
  ]
  const hyps = ['All', 'In', 'Out'].map(map => same(get(map, n(0)), n(1)))
  const cert = certFor({hyps}, ds, true, 1000)
  expect(cert.insts.some(i => i.terms.length === 3)).toBe(true)
  const q = mcGoal(hyps, ds, cert)!
  const proof = grow({name: 'partition contradicts three ones', hyps: q.hyps}, new Map(), {nodes: 0, until: clock() + 1500})
  expect('tree' in proof).toBe(true)
  if ('tree' in proof) expect(checkMC(hyps, ds, {...cert, tree: proof.tree})).toBe(true)
})

test('structured count identities preserve the frozen legacy witness prefix', () => {
  const k=x('member'), a=same(get('Whole',k),n(1)), b=same(get('Inside',k),n(1)), base={j:'unused',key:'member',below:n(3)}
  const ds=[{...base,map:'All',body:ite(a,n(1),n(0))},{...base,map:'In',body:ite(all(a,b),n(1),n(0))},
    {...base,map:'Out',body:ite(all(a,not(b)),n(1),n(0))},{...base,map:'Fourth',body:ite(same(get('Flag',k),n(1)),n(1),n(0))}]
  const hyps=ds.map(d=>same(get(d.map,n(0)),n(1))), cert=certFor({hyps},ds,true,16)
  // These indices and units are frozen from the unextended legacy pool.
  const meetings=[[0,1],[0,2],[0,3],[1,2],[1,3],[2,3]]
  const differences=[[0,1],[0,2],[0,3],[1,0],[1,2],[1,3],[2,0],[2,1],[2,3],[3,0]]
  expect(JSON.stringify(cert.insts.map(i=>[i.terms,i.unit]))).toBe(JSON.stringify([
    ...meetings.map(([i,j])=>[[[1,`r$${i}`],[1,`r$${j}`]],-1]),
    ...differences.map(([i,j])=>[[[1,`r$${i}`],[-1,`r$${j}`]],0]),
  ]))
})

test('structured identities remain available after an explicit legacy-first proposal', () => {
  const member=x('member'), whole=same(get('Whole',member),n(1)), inside=same(get('Inside',member),n(1))
  const base={j:'unused',key:'member',below:n(3)}, ds=[
    {...base,map:'All',body:ite(whole,n(1),n(0))},
    {...base,map:'In',body:ite(all(whole,inside),n(1),n(0))},
    {...base,map:'Out',body:ite(all(whole,not(inside)),n(1),n(0))},
  ], hyps=ds.map(d=>same(get(d.map,n(0)),n(1)))
  const legacy=certFor({hyps},ds,true,1000,undefined,false), expanded=certFor({hyps},ds,true,1000,undefined,true)
  expect(legacy.insts.some(i=>i.terms.length>=3)).toBe(false)
  expect(expanded.insts.some(i=>i.terms.length>=3)).toBe(true)
  expect(expanded.insts.slice(0,legacy.insts.length)).toEqual(legacy.insts)
})

test('a key from another row is only a proposal and cannot certify a false count', () => {
  const g = goal(1), full = certFor(g, decls, true)
  const q = mcGoal(g.hyps, decls, {reads: full.reads, insts: [], picks: full.picks})!
  const proof = grow({name: g.name, hyps: q.hyps}, new Map(), {nodes: 0, until: clock() + 1500})
  expect('tree' in proof).toBe(false)
})

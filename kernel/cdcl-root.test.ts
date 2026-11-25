import {expect,test} from 'bun:test'
import {type Goal,type Path,canon,check,framePath} from './kernel.ts'
import {clock} from './prove.ts'
import {cdclCandHook, growCdcl} from './cdcl.ts'

for(const holds of [true,false])test(`duplicate root aliases retain ${holds?'positive':'negative'} orientation`,()=>{
 const lin={rootX:1,'1':-1},root:Path=new Map([[canon(lin),{lin,holds}],['@0',{lin,holds}]])
 const goal:Goal={name:'duplicate root',hyps:[holds?{op:'<=',a:{op:'const',value:2},b:{op:'var',name:'rootX'}}:{op:'<=',a:{op:'var',name:'rootX'},b:{op:'const',value:1}}]}
 const before=JSON.stringify([...root]),q=growCdcl(goal,root,{nodes:0,until:clock()+100})
 expect(JSON.stringify([...root])).toBe(before)
 expect('tree'in q).toBe(true)
 if('tree'in q)expect(check(goal,q.tree,root)).toBe(true)
})

test('duplicate frame-cut rows remain checked at their original root',()=>{
 const frame={post:'post',pre:'pre',when:[]},root=framePath([frame,frame],[],new Map())
 expect([...root.keys()].some(k=>k.startsWith('@'))).toBe(true)
 const goal:Goal={name:'duplicate frame',hyps:[{op:'<',a:{op:'var',name:'pre'},b:{op:'var',name:'post'}}]}
 const q=growCdcl(goal,root,{nodes:0,until:clock()+100})
 expect('tree'in q).toBe(true)
 if('tree'in q)expect(check(goal,q.tree,root)).toBe(true)
})

test('incremental openCellsLive preserves exact candidate stream with root decisions and multi-cell maps', () => {
  const v = (name: string) => ({op: 'var' as const, name})
  const n = (value: number) => ({op: 'const' as const, value})
  const get = (map: string, key: any) => ({op: 'get' as const, map, key})
  const goal: Goal = {
    name: 'root-cells-stream',
    hyps: [
      {op: 'or', xs: [{op: '=', a: get('M', v('a')), b: n(0)}, {op: '=', a: get('M', v('b')), b: n(1)}]},
      {op: 'or', xs: [{op: '=', a: get('M', v('b')), b: n(0)}, {op: '=', a: get('M', v('c')), b: n(1)}]},
      {op: '=', a: get('M', v('a')), b: n(1)},
      {op: '=', a: get('M', v('c')), b: n(0)},
      {op: '=', a: v('a'), b: v('b')},
      {op: '=', a: v('b'), b: v('c')},
    ],
  }
  const rootLin = {a: 1, b: -1}
  const root: Path = new Map([[canon(rootLin), {lin: rootLin, holds: true}]])
  const stream: string[] = []
  const prevVerify = cdclCandHook.verify
  const prevOn = cdclCandHook.on
  try {
    cdclCandHook.verify = true
    cdclCandHook.on = (cands, openLen) => {
      stream.push(`${openLen}:${cands.join(',')}`)
    }
    const q = growCdcl(goal, root, {nodes: 0, until: clock() + 500})
    expect('tree' in q).toBe(true)
    if ('tree' in q) expect(check(goal, q.tree, root)).toBe(true)
    expect(stream.length).toBeGreaterThan(0)
  } finally {
    cdclCandHook.verify = prevVerify
    cdclCandHook.on = prevOn
  }
})

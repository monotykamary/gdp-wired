import {expect,test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {readFileSync} from 'node:fs'
import {type Goal,type Path,leafConstraints} from '../kernel/kernel.ts'
import {atMost,get,n,x} from './machine.ts'
import {reuseNativeScopeRows} from './count-scope-row-reuse.ts'
import {ExactPathIdentity} from './count-recovery/path-identity.ts'
import {canon} from '../kernel/kernel.ts'

// Each child sees the same cold native/proposer caches, then the same warm
// calls. Running two collectors successively in one process would not test
// equal memo history or equal counted work.
test('capture reuse is byte/order/work/refusal identical to source48 in isolated cold and warm controls',()=>{
 const worker=new URL('../research/capture-row-reuse/reference-worker.ts',import.meta.url)
 const run=(mode:string)=>{
  const child=spawnSync(process.execPath,[worker.pathname,mode],{encoding:'utf8',env:{...process.env,GDP_WORK_FULL:'1',GDP_ROWS_SHARED:'1'},timeout:60000,maxBuffer:8*1024*1024})
  expect(child.status,child.stderr).toBe(0)
  expect(child.signal).toBeNull()
  return JSON.parse(child.stdout)
 }
 const reference=run('reference'),reuse=run('reuse')
 expect(reuse).toEqual(reference)
 expect(reuse).toHaveLength(18)
 expect(reuse.slice(0,11).every((x:any)=>x.valid&&x.rowsEqual&&x.error===null&&x.refs.length===2)).toBe(true)
 expect(reuse.slice(11).some((x:any)=>x.error?.name==='BudgetExpired'&&x.error.capacity?.reason==='quantum')).toBe(true)
})
test('identity cache preserves exact true/false hits, misses and work order of source48',()=>{
 const worker=new URL('../research/capture-row-reuse/cache-worker.ts',import.meta.url)
 const run=(mode:string)=>{const r=spawnSync(process.execPath,[worker.pathname,mode],{encoding:'utf8',env:{...process.env,GDP_WORK_FULL:'1',GDP_ROWS_SHARED:'1'},timeout:60000,maxBuffer:2*1024*1024});expect(r.status,r.stderr).toBe(0);return JSON.parse(r.stdout)}
 const old=run('reference'),next=run('reuse')
 expect(next).toEqual(old)
 expect(next.outputs.some((x:any)=>x.delta.leafHits===1&&x.answer===false)).toBe(true)
 expect(next.outputs.some((x:any)=>x.delta.leafHits===1&&x.answer===true)).toBe(true)
 expect(next.interruptions.some((x:any)=>x.error?.name==='BudgetExpired')).toBe(true)
 expect(next.interruptions.every((x:any)=>x.recovered===true)).toBe(true)
})
test('580-atom prefixes are shared by exact identities, including key/order/false distinctions',()=>{
 const ids=new ExactPathIdentity(),prefix:Path=new Map()
 for(let i=0;i<580;i++){const lin={['cut'+i]:1};prefix.set(canon(lin),{lin,holds:true})}
 const base=ids.get(prefix),equivalent:Path=new Map([...prefix].map(([k,a])=>[k,{lin:{...a.lin},holds:a.holds}]))
 expect(ids.get(equivalent)).toBe(base)
 const terminals:object[]=[]
 for(let i=0;i<64;i++){const branch:Path=new Map(prefix);branch.set('branch'+i,{lin:{['branch'+i]:1},holds:true});terminals.push(ids.get(branch))}
 expect(new Set(terminals).size).toBe(64)
 expect(ids.shape()).toEqual({atoms:644,nodes:645})
 const falsePath:Path=new Map(prefix);falsePath.set('extra',{lin:{cut0:1},holds:false})
 expect(ids.get(falsePath)).not.toBe(base)
 expect(ids.get(new Map([...prefix].reverse()))).not.toBe(base)
 const changed:Path=new Map(prefix);changed.set('alias',{lin:{cut0:1},holds:true})
 expect(ids.get(changed)).not.toBe(base)
 // Live terminals own ancestors; roots have only weak child edges. No strong
 // root-to-terminal history remains when a leaf cache releases its key.
 const terminal=terminals[0] as {parent?:object},root=(ids as unknown as {root:{next:unknown}}).root
 expect(terminal.parent).toBeDefined();expect(root.next).toBeInstanceOf(WeakMap)
 expect(new ExactPathIdentity().get(prefix)).not.toBe(base)
 expect(ids.get(new Map())).toBe(ids.get(new Map()))
})
test('reuse returns the existing full row array without replacing a row or certificate',()=>{
 const goal:Goal={name:'table identity',hyps:[atMost(get('M',x('i')),n(3)),atMost(get('M',x('j')),n(4))]},path:Path=new Map()
 const rows=leafConstraints(goal,path),before=JSON.stringify(rows),members=rows.slice()
 expect(reuseNativeScopeRows(goal,path,rows)).toBe(rows)
 expect(rows.every((row,i)=>row===members[i])).toBe(true)
 expect(JSON.stringify(rows)).toBe(before)
})
test('the differential oracle is a frozen source48 collector, not the optimized helper',()=>{
 const text=readFileSync(new URL('../research/capture-row-reuse/reference-count-scope-hyps.ts',import.meta.url),'utf8')
 expect(text).toContain('const rows=leafConstraints(goal,actual)')
 expect(text).not.toContain('reuseNativeScopeRows')
})

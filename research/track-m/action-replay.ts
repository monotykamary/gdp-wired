// Diagnostic: split first on a finite-valued scalar found in the goal's equality
// tests. Paths are proof-tree splits, never extra assumptions in the final claim.
import {type Goal, type Path, type Tree, canon, check} from '../../kernel/kernel.ts'
import {type C, walkOnce} from '../../core/machine.ts'
import {clock, counted, fullRate, fullWork, grow, widen, withWall} from '../../kernel/prove.ts'
import {prepareCaptured} from './replay-setup.ts'
const [file, input, mode = 'raw'] = process.argv.slice(2), {goal}: {goal: Goal} = prepareCaptured(file!, input!, mode)
const values = new Map<string, Set<number>>()
walkOnce(goal.hyps, (o: any) => {
  const c = o as C
  if (c.op !== '=') return
  const [a,b] = c.a.op === 'var' ? [c.a,c.b] : [c.b,c.a]
  if (a.op !== 'var' || b.op !== 'const') return
  const vs = values.get(a.name) ?? new Set<number>(); vs.add(b.value); values.set(a.name,vs)
})
const scalar = [...values].filter(([,v])=>v.size>2).sort((a,b)=>b[1].size-a[1].size)[0]
if (!scalar) throw new Error('No finite-choice scalar in this goal')
const [name, vs] = scalar, cuts = [...vs].sort((a,b)=>a-b), trees: (Tree|undefined)[] = []
const ms = Number(process.env.LAB_CASE_MS ?? 1000), path: Path = new Map(), root = process.env.LAB_CASE_ROOT === '1'
const conditions: C[] = []
let total = 0
for (const value of [...cuts, undefined]) {
  const split = value === undefined ? undefined : {[name]:1,'1':-value}
  if (split) path.set(canon(split),{lin:split,holds:true})
  const start=performance.now(), before=fullWork()
  const cut: C|undefined = value === undefined ? undefined : {op:'<=',a:{op:'var',name},b:{op:'const',value}}
  const part: Goal = root ? {...goal,hyps:[...conditions,...cut?[cut]:[],...goal.hyps]} : goal
  const out=withWall(start+2*ms,()=>counted(fullRate,()=>grow(part,root?new Map():path,{nodes:0,until:clock()+ms}),true))
  const cost=Math.round((fullWork()-before)/fullRate); total+=cost
  const tree = 'tree' in out ? (root ? widen(part,goal,out.tree,{},new Map(),path) : out.tree) : undefined
  trees.push(tree)
  console.log(JSON.stringify({file,mode,name,value:value??'rest',hyps:goal.hyps.length,counted:cost,wall:Math.round(performance.now()-start),root,outcome:'tree' in out?'tree':out.stuck,checked:!!tree&&check(goal,tree,path)}))
  if (split) { path.set(canon(split),{lin:split,holds:false}); conditions.push({op:'not',x:cut!}) }
}
let combined=trees.at(-1)
for(let i=cuts.length-1;i>=0;i--) combined=combined&&trees[i]?{split:{[name]:1,'1':-cuts[i]!},yes:trees[i]!,no:combined}:undefined
console.log(JSON.stringify({file,mode,total,complete:!!combined&&check(goal,combined)}))

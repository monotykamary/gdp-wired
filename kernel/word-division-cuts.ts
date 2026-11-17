// Untrusted local lemmas: every branch and the final tree use the ordinary checker.
// Avoid combining four radix columns into an unsafe 2^64 intermediate by proving
// c_i = multiplicationCarry_i + additionCarry_i one column at a time.
import {walkOnce, type E} from '../core/machine.ts'
import {add, scale, type Lin} from '../core/solver.ts'
import {canon, check, linear, type Goal, type Path, type Tree} from './kernel.ts'
import {parseWordDivisionName, wordDivisionArgs, wordDivisionName} from './word-division.ts'

type Prove = (goal: Goal, path: Path) => Tree | undefined
type Widen = (part: Goal, whole: Goal, tree: Tree, opaque: Record<string,E>, pp: Path, wp: Path) => Tree | undefined
export function wordDivisionCuts(goal: Goal, prove: Prove, widen: Widen): Tree | undefined {
  let found: Extract<E,{op:'get'}> | undefined, modular = false
  walkOnce(goal.hyps.at(-1), o => {
    const e = o as E
    if (e.op !== 'get') return
    if (e.map === 'mod$65536') modular = true
    if (parseWordDivisionName(e.map)?.width === 64) found ??= e
  })
  if (!found || !modular) return
  const key = found.key, args = wordDivisionArgs(key,64)
  if (!args) return
  const zero: E = {op:'const',value:0}
  const sum = (xs:E[]):E => xs.reduce((a,b)=>({op:'add',a,b}),zero)
  const get = (part:'q'|'r'|'c',i:number):E => ({op:'get',map:wordDivisionName(64,part,i),key})
  const call = (map:string,key:E):E => ({op:'get',map,key})
  let mp: E = zero, ap: E = zero
  const cuts: {a:E,b:E,lin:Lin}[] = []
  for (let i=0;i<4;i++) {
    const col = sum([mp,...Array.from({length:i+1},(_,j):E=>({op:'prod',a:get('q',j),b:args[4+i-j]!}))])
    const digit = call('mod$65536',col)
    mp = call('div$65536',col)
    ap = call('div$65536',sum([digit,get('r',i),ap]))
    const a = get('c',i+1), b = sum([mp,ap]), la = linear(a,new Map()), lb = linear(b,new Map())
    if (!la || !lb) return
    cuts.push({a,b,lin:add(la,scale(lb,-1))})
  }
  const branch = (p:Path,lin:Lin,holds:boolean):Path => new Map(p).set(canon(lin),{lin,holds})
  const ordinary = (g:Goal,p:Path):Tree|undefined => {
    const tree = prove(g,p)
    return tree && check(g,tree,p) ? tree : undefined
  }
  const walk = (i:number,p:Path):Tree|undefined => {
    if (i===cuts.length) return ordinary(goal,p)
    const cut = cuts[i]!, l = cut.lin, neg = scale(l,-1)
    if (p.has(canon(l)) || p.has(canon(neg)) || Object.keys(l).every(k=>k==='1')) return
    const part:Goal = {name:`word carry ${i+1}`,hyps:[...goal.hyps.slice(0,-1),{op:'not',x:{op:'=',a:cut.a,b:cut.b}}]}
    const noP = branch(p,l,false), yesP = branch(p,l,true), lowP = branch(yesP,neg,false), eqP = branch(yesP,neg,true)
    const no = ordinary(part,noP), low = ordinary(part,lowP)
    if (!no || !low) return
    const noWide = widen(part,goal,no,{},noP,noP), lowWide = widen(part,goal,low,{},lowP,lowP)
    if (!noWide || !lowWide) return
    const rest = walk(i+1,eqP)
    return rest ? {split:l,yes:{split:neg,yes:rest,no:lowWide},no:noWide} : undefined
  }
  const d = linear(sum(args.slice(4)),new Map())
  if (!d) return
  const nonzero = add({'1':1},scale(d,-1)), yesP = branch(new Map(),nonzero,true), noP = branch(new Map(),nonzero,false)
  const yes = walk(0,yesP), no = ordinary(goal,noP)
  const tree:Tree|undefined = yes && no ? {split:nonzero,yes,no} : undefined
  return tree && check(goal,tree) ? tree : undefined
}

import './paxos-law20-localize.ts'
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {check,leafConstraints,canon,facts} from '../../kernel/kernel.ts'
import {encode} from '../../lean-kernel/emit.ts'
const dir='runs/verify-all/paxos-law20-work/'
const original=readFileSync(dir+'localize.lean','utf8')
const leaves=JSON.parse(readFileSync(dir+'leaves.json','utf8'))
for(const route of ['YYYYN','N']){const l=leaves.find((x:any)=>x.route===route);console.log('EXACT_FAILURE',JSON.stringify({route,path:l.path,tree:l.tree,used:l.tree.leaf.filter((s:any)=>s.kind==='input').map((s:any)=>({index:s.index,row:l.base[s.index]}))}))}
const atom:any={op:'<',a:{op:'var',name:'x'},b:{op:'var',name:'y'}},singleton:any={op:'or',xs:[atom]},not:any={op:'not',x:atom},split={x:1,y:-1,'1':1}
const goal={name:'singleton-or-unsat-probe',hyps:[singleton,not]},tree:any={split,yes:{leaf:[{kind:'input',index:2}]},no:{leaf:[{kind:'input',index:1}]}}
const control={...goal,hyps:[atom,not]},roundtrip=JSON.parse(JSON.stringify({goal,tree}))
const en=encode({name:roundtrip.goal.name,goal:roundtrip.goal,tree:roundtrip.tree})
console.log('TINY_SERIALIZED_TS_ACCEPTS',check(roundtrip.goal,roundtrip.tree),'TINY_UNWRAPPED_CONTROL_TS_ACCEPTS',check(control,tree))
const p=new Map([[canon(split),{lin:split,holds:false}]])
console.log('TINY_NO_PATH_ROWS',JSON.stringify(leafConstraints(goal,p)),'TINY_OR_FACTS',JSON.stringify(facts(singleton,p)),'TINY_ATOM_FACTS',JSON.stringify(facts(atom,p)))
writeFileSync(dir+'tiny-probe.json',JSON.stringify(roundtrip,null,2));writeFileSync(dir+'tiny-emitted.lean',`import Kernel\nopen Cert Kern\ndef emittedTinyGoal : Goal := ⟨${en.tab},${en.hyps}⟩\ndef emittedTinyTree : Tree := ${en.tree}\nexample : checkGoal emittedTinyGoal emittedTinyTree = false := by decide\n`)
const extra=`
-- No changes to retained definitions. These are separately named diagnostic controls.
def h24 : C := (law20hs[24]?).getD (.eq (.const 0) (.const 0))
def nodeAt : Tree → List Bool → Tree
 | t, [] => t
 | .split _ y n, b::bs => nodeAt (if b then y else n) bs
 | t, _ => t
def pathAt : Tree → List Bool → Path → Path
 | _, [], p => p
 | .split r y n, b::bs, p => pathAt (if b then y else n) bs ((r,b)::p)
 | _, _, p => p
def firstRoute := [true,true,true,true,false]
def rootNoRoute := [false]
def firstPath := pathAt law20tree firstRoute []
def noPath := pathAt law20tree rootNoRoute []
def latestRow (p : Path) : Row := match p with | (r,_)::_ => r | [] => lconst 0
def correctedLeaf (h : Nat) (p : Path) : Tree := .leafAt [(latestRow p,.fact h),(flip (latestRow p),.atom 0)] [.input 0,.input 1,.combine 0 1 1 1] [] []
theorem first_original_rejected : checkT law20tab law20hs firstPath (nodeAt law20tree firstRoute) = false := by decide
theorem root_no_original_rejected : checkT law20tab law20hs noPath (nodeAt law20tree rootNoRoute) = false := by decide
-- Even ONE source hypothesis plus the exact inherited path gives a kernel-checked contradiction.
theorem first_source_refutation : checkT law20tab [h24] firstPath (correctedLeaf 0 firstPath) = true := by decide
theorem root_no_source_refutation : checkT law20tab [h24] noPath (correctedLeaf 0 noPath) = true := by decide
theorem first_source_inconsistent {env : Nat → Nat} {maps : Nat → Nat → Nat} {x : List Int}
    (hm : Model law20tab env maps x) (hp : PathHolds firstPath x) (hh : evalC env maps h24 = true) : False := by
  have hh' : ∀ c ∈ [h24], evalC env maps c = true := by
    intro c hc
    simp only [List.mem_singleton] at hc
    subst c
    exact hh
  exact checkT_sound hm hh' (correctedLeaf 0 firstPath) firstPath hp first_source_refutation
-- Replace only the two rejected leaves, explicitly a new diagnostic tree, not the original proof.
def replaceAt : Tree → List Bool → Tree → Tree
 | _, [], replacement => replacement
 | .split r y n, true::bs, t => .split r (replaceAt y bs t) n
 | .split r y n, false::bs, t => .split r y (replaceAt n bs t)
 | t, _, _ => t
def diagnosticAdaptedTree := replaceAt (replaceAt law20tree firstRoute (correctedLeaf 24 firstPath)) rootNoRoute (correctedLeaf 24 noPath)
#reduce ("ADAPTED_TREE_CONTROL", checkT law20tab law20hs [] diagnosticAdaptedTree)
def exactNodes : Tree → Path → List Bool → List (List Bool × Bool)
 | .split r y n, p, route => (route, checkT law20tab law20hs p (.split r y n)) :: (exactNodes y ((r,true)::p) (route++[true]) ++ exactNodes n ((r,false)::p) (route++[false]))
 | t, p, route => [(route,checkT law20tab law20hs p t)]
#reduce ("ALL_EXACT_LEAN_NODES", exactNodes law20tree [] [])
#print axioms first_original_rejected
#print axioms root_no_original_rejected
#print axioms first_source_refutation
#print axioms root_no_source_refutation
#print axioms first_source_inconsistent
`
const text=original+extra;writeFileSync(dir+'validate.lean',text);console.log('VALIDATE_LEAN_SHA',createHash('sha256').update(text).digest('hex'))

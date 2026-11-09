// Diagnostic only. Retained trees are never modified; node checks retain full context.
import {readFileSync,writeFileSync,mkdirSync,readdirSync} from 'node:fs'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {check,checkMC,countedObligations,mcGoal,canon,leafConstraints,withProducts} from '../../kernel/kernel.ts'
import {encode} from '../../lean-kernel/emit.ts'
const dir='runs/verify-all/paxos-law20-work/';mkdirSync(dir,{recursive:true})
const sha=(s:string)=>createHash('sha256').update(s).digest('hex')
const log=readFileSync('evidence/capture-paxos_epr.log','utf8')
writeFileSync(dir+'archive.tar.xz',Buffer.from(log.match(/ARCHIVE_BEGIN\n([A-Za-z0-9+/=\r\n]+)\nARCHIVE_END/)![1]!,'base64'))
const extracted=dir+'original/';mkdirSync(extracted,{recursive:true})
if(spawnSync('tar',['-xJf',dir+'archive.tar.xz','-C',extracted]).status!==0)throw Error('extract')
const fs=readdirSync(extracted),raw=readFileSync(extracted+fs.find(x=>x.endsWith('.json')&&!x.endsWith('.result.json'))!,'utf8'),original=readFileSync(extracted+fs.find(x=>x.endsWith('.lean'))!,'utf8')
if(sha(raw)!=='dc0e230fab5d0081a2c9d4f56b525ef314a2e78780647d3cb2fafaf3a512f386'||sha(original)!=='e31b4c24e46e021c0b0187d1c2b71736530c16e47db15c18eb4d8cd77cfc15b1')throw Error('hash mismatch')
console.log('INPUT_HASHES',sha(raw),sha(original))
const c=JSON.parse(raw,(_k,v)=>v?.__map?new Map(v.__map):v?.__set?new Set(v.__set):v).counted
const ob=countedObligations(c.machine,c.laws,c.proof.instances).find(o=>o.goal.name===c.laws[20].name+' @step')!,cert=c.proof.certs[ob.goal.name],goal=mcGoal(ob.goal.hyps,ob.decls,cert)!
console.log('TS_CHECK_MC',checkMC(ob.goal.hyps,ob.decls,cert),'LEMMA_COUNT',cert.lemmas?.length??0)
const ns=original.split('\n').find(l=>l.startsWith('--   (variables'))!.match(/variables (.*); maps (.*)\)$/)!,names=(x:string)=>x.split(', ').map(s=>s.replace(/^\d+ /,''))
const en=encode({name:'retained-step20',goal,tree:cert.tree},false,true,names(ns[1]!),names(ns[2]!))
writeFileSync(dir+'columns.json',JSON.stringify(en.cols,null,2))
const nodes:any[]=[];const leaves:any[]=[]
function walk(t:any,path:Map<string,any>,route:string){nodes.push({route,ts:check(goal,t,path)});if('split' in t){const id=canon(t.split);walk(t.yes,new Map(path).set(id,{lin:t.split,holds:true}),route+'Y');walk(t.no,new Map(path).set(id,{lin:t.split,holds:false}),route+'N')}else{leaves.push({route,path:[...path],tree:t,base:leafConstraints(goal,path),rows:withProducts(leafConstraints(goal,path),t.products??[],t.squares)})}}
walk(cert.tree,new Map(),'')
writeFileSync(dir+'nodes.json',JSON.stringify(nodes,null,2));writeFileSync(dir+'leaves.json',JSON.stringify(leaves,null,2))
console.log('TS_NODE_COUNT',nodes.length,'TS_LEAF_COUNT',leaves.length,'TS_FAILED_NODES',nodes.filter(n=>!n.ts))
const extra=`
-- Separate diagnostic, original failed safety theorem excluded.
def law20k := (verified_proof[20]).step
def law20hs := law20k.hyps ++ law20k.reads.map (readHyp (cStepDecls verified_machine verified_decls)) ++ pickHyps (cStepDecls verified_machine verified_decls) law20k.reads law20k.picks ++ (countHyps ((toCounts (cStepDecls verified_machine verified_decls) law20k.reads).getD []) law20k.insts).getD []
def law20tab := law20k.tab
def law20tree := law20k.tree
def expectedHyps : List C := ${en.hyps}
#reduce ("SAME_FULL_HYPOTHESES", law20hs == expectedHyps)
def badLeaves : Tree → Path → List Bool → List (List Bool)
 | .split l y n, p, r => badLeaves y ((l,true)::p) (r++[true]) ++ badLeaves n ((l,false)::p) (r++[false])
 | t, p, r => if checkT law20tab law20hs p t then [] else [r]
def firstBad : Tree → Path → List Bool → Option (List Bool × Path × Tree)
 | .split l y n, p, r => match firstBad y ((l,true)::p) (r++[true]) with
   | some x => some x
   | none => firstBad n ((l,false)::p) (r++[false])
 | t, p, r => if checkT law20tab law20hs p t then none else some (r,p,t)
#reduce ("LEAN_BAD_LEAVES",badLeaves law20tree [] [])
def law20bad := firstBad law20tree [] []
def inspectBad : Option (List Bool × Path × Tree) → List Bool × List (Row × Bool) × Bool × Bool × List (Nat × Row) × List Step
 | none => ([],[],true,true,[],[])
 | some (r,p,t) => match t with
   | .leafAt rows steps eqs prods =>
     let admissible := fun q => (srcRows law20tab p law20hs eqs q.2).any (same q.1) || (leafRows law20tab p law20hs eqs).any (same q.1)
     (r,p,rows.all admissible, (match extend law20tab (rows.map (·.1)) prods with | some rs => Cert.check rs steps | none => false), (rows.zipIdx.filter (fun (q,_) => !admissible q)).map (fun (q,i) => (i,q.1)), steps)
   | _ => (r,p,false,false,[],[])
#reduce ("FIRST_BAD_DETAIL",inspectBad law20bad)
`
const lean=original.split('theorem verified_check :')[0]!+extra
writeFileSync(dir+'localize.lean',lean);console.log('DIAGNOSTIC_LEAN_SHA',sha(lean))

import './paxos-law20-localize.ts'
import {readFileSync,writeFileSync,readdirSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {countedObligations,mcGoal,truth,facts,linear} from '../../kernel/kernel.ts'
import {encode} from '../../lean-kernel/emit.ts'
const dir='runs/verify-all/paxos-law20-work/',od=dir+'original/'
const files=readdirSync(od),original=readFileSync(od+files.find(x=>x.endsWith('.lean'))!,'utf8')
const c=JSON.parse(readFileSync(od+files.find(x=>x.endsWith('.json')&&!x.endsWith('.result.json'))!,'utf8'),(_k,v)=>v?.__map?new Map(v.__map):v?.__set?new Set(v.__set):v).counted
const ob=countedObligations(c.machine,c.laws,c.proof.instances).find(o=>o.goal.name===c.laws[20].name+' @step')!,cert=c.proof.certs[ob.goal.name],goal=mcGoal(ob.goal.hyps,ob.decls,cert)!
const ns=original.split('\n').find(l=>l.startsWith('--   (variables'))!.match(/variables (.*); maps (.*)\)$/)!,names=(x:string)=>x.split(', ').map(s=>s.replace(/^\d+ /,''))
const en=encode({name:'retained-step20',goal,tree:cert.tree},false,true,names(ns[1]!),names(ns[2]!))
const leaves=JSON.parse(readFileSync(dir+'leaves.json','utf8'))
let extra='\ndef deepPath : Path := match law20bad with | some (_,p,_) => p | none => []\n'
for(const route of ['YYYYN','N']){
 const leaf=leaves.find((l:any)=>l.route===route),path=new Map<string,any>(leaf.path)
 console.log('BAD_TS_LEAF',JSON.stringify(leaf))
 for(const step of leaf.tree.leaf){if(step.kind!=='input')continue;const row=leaf.base[step.index];console.log('USED_ROW',route,step.index,JSON.stringify(row));if(row.src?.fact===undefined)continue;const hi=row.src.fact,h=goal.hyps[hi]!;console.log('SOURCE_HYP',hi,JSON.stringify(h))
 if(route!=='YYYYN')continue
 extra+=`#reduce ("SOURCE_HYP_${hi}", facts law20tab deepPath true (law20hs[${hi}]!), truth law20tab deepPath (law20hs[${hi}]!))\n`
 let no=0;function descend(h:any){const id=no++,result={id,op:h.op,truth:truth(h,path),facts:facts(h,path),h};console.log('HYP_COMPONENT',JSON.stringify(result));extra+=`#reduce ("COMP_${id}", truth law20tab deepPath (${en.c(h)}), facts law20tab deepPath true (${en.c(h)}), facts law20tab deepPath false (${en.c(h)}))\n`;if(h.xs)h.xs.forEach(descend);if(h.x)descend(h.x);if(h.a&&h.b){console.log('LINEAR',id,JSON.stringify(linear(h.a,path)),JSON.stringify(linear(h.b,path)));extra+=`#reduce ("LINEAR_${id}", linear law20tab deepPath (${en.e(h.a)}), linear law20tab deepPath (${en.e(h.b)}))\n`}}
 descend(h)
 }
}
const text=readFileSync(dir+'localize.lean','utf8')+extra;writeFileSync(dir+'deep.lean',text)
console.log('DEEP_LEAN_SHA',createHash('sha256').update(text).digest('hex'))

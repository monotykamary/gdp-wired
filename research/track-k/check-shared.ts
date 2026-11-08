import assert from 'node:assert/strict'
import {readFileSync,writeFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {type E} from '../../core/machine.ts'
import {type Lin} from '../../core/solver.ts'
import {type Goal,type Tree,type LemmaCut,termColumn,checkGoalLemmas} from '../../kernel/kernel.ts'
import {countedToLean} from '../../lean-kernel/emit.ts'
const [file,out]=process.argv.slice(2) as [string,string]
const pack=JSON.parse(gunzipSync(readFileSync(file)).toString()) as {goal:Goal,tree:Tree,lemmas:LemmaCut[],columns:Record<string,E>}
const names=new Map(Object.entries(pack.columns).map(([id,e])=>[id,termColumn(e)]))
const row=(lin:Lin):Lin=>Object.fromEntries(Object.entries(lin).map(([k,z])=>[names.get(k)??k,z]))
const tree=(t:Tree):Tree=>'leaf'in t?t:{split:row(t.split),yes:tree(t.yes),no:tree(t.no)}
const cert={tree:tree(pack.tree),lemmas:pack.lemmas.map(l=>({...l,when:l.when.map(row),cut:row(l.cut),tree:tree(l.tree)}))}
assert(checkGoalLemmas(pack.goal,cert.tree,cert.lemmas),'portable emitted certificate refused')
assert(!checkGoalLemmas(pack.goal,cert.tree,[]),'shared tree unexpectedly checks without its cuts')
assert(!checkGoalLemmas(pack.goal,cert.tree,cert.lemmas.map((l,i)=>i?l:{...l,tree:{leaf:[]}})),'a non-refuting lemma was accepted')
const text='import Count\nopen Kern Cert\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n'+countedToLean('shared_send',{...pack.goal,counts:[]},{...cert,insts:[]})+'\n#print axioms shared_send\n'
writeFileSync(out,text)
console.log(JSON.stringify({checked:true,lemmas:cert.lemmas.length,leanBytes:Buffer.byteLength(text),sha256:createHash('sha256').update(text).digest('hex')}))

// Lean twin: GhostWriteTransport.checkedTransport, using the complete original
// post-row functional. Closed flags and a fresh observer are just views.
import {type C,type E,type Law,type Machine,get,n,same,walkOnce,x} from '../core/machine.ts'
import {checkLaws,ghostedMachine,ghostedOk,mapArities,obligations,own,sideGoals,substC,type Instances,type Tree} from './kernel.ts'

export type GhostWriteRecipe = {
  ghostMap:string, point:E, gates:[column:string,value:number][], group:string, weight:string, observer:string
}
export type GhostWriteCertificate = {
  kind:'ghost-write', recipe:GhostWriteRecipe, projection:{omitMap:string},
  target:Machine, laws:Law[], pointLaw:string,
  proof:{instances:Record<string,Instances>,trees:Record<string,Tree>}
}
const text=(x:unknown)=>JSON.stringify(x)
const eq=(a:unknown,b:unknown)=>text(a)===text(b)
const safeNat=(v:unknown)=>typeof v==='number'&&Number.isSafeInteger(v)&&v>=0
const noSub={vars:{},maps:{},flags:{}}

export function ghostWriteTheory(source:Machine,law:Law,p:GhostWriteCertificate) {
  const r=p.recipe, ghost=r.ghostMap
  if (p.kind!=='ghost-write'||Object.keys(p.projection).length!==1||p.projection.omitMap!==ghost||
      !law.forall||law.keys?.length||law.some?.length||law.ex||law.finite!==undefined||
      source.history||source.primitiveFailure||Object.keys(source.counts??{}).length||Object.keys(source.sums??{}).length||
      Object.keys(source.fns??{}).length||source.facts?.length||source.inputMaps?.length||Object.keys(source.leasts??{}).length) return
  const sums=Object.entries(p.target.sums??{})
  if (sums.length!==1) return
  const [sum,sd]=sums[0]!, used=text([source,law])
  const fresh=[r.observer,ghost,sum,sd.key]
  if (new Set(fresh).size!==fresh.length||fresh.some(key=>!key||used.includes(text(key)))||
      !eq(sd,{term:get(ghost,x(sd.key)),key:sd.key})) return
  let unsupported=false
  walkOnce([source,law.holds,r.point],o=>{
    const t=o as {op?:string,map?:string,value?:unknown,k?:unknown}
    if (t.op==='all'||t.op==='get'&&t.map?.startsWith('worddiv$')||t.op==='const'&&!safeNat(t.value)||t.op==='mul'&&!safeNat(t.k)) unsupported=true
  })
  if (unsupported) return
  obligations(source,[law])
  if (!Object.values(source.maps??{}).every(safeNat)||Object.values(mapArities(source,[law])).some(n=>n!==1)) return

  const written=(name:string)=>{ const w=own(source.step.maps??{},name); return w&&!('each' in w)?w:undefined }
  if (!r.gates.length||!r.gates.every(([map,val])=>safeNat(val)&&!!written(map))||!written(r.group)||!written(r.weight)||
      !r.gates.some(([map])=>eq(written(map)!.key,r.point))) return
  const post=(map:string,key:E):E=>{ const w=written(map)!; return eq(key,w.key)?w.value:
    {op:'if',c:same(key,w.key),then:w.value,else:get(map,key)} }
  const contribution=(read:(map:string)=>E):E=>({op:'if',
    c:r.gates.reduceRight<C>((tail,[map,val])=>({op:'and',xs:[same(read(map),n(val)),tail]}),same(read(r.group),x(r.observer))),
    then:read(r.weight),else:n(0)})

  // Match the existing Lean closed-flag view of the same machine. Its dummy
  // binders occur nowhere in the actual body or in the source machine.
  let stem='internal$'; while (text([source,law,fresh]).includes(stem)) stem+='a'
  const closed:Record<string,C>=Object.create(null), inlined:Record<string,C>=Object.create(null)
  for (const [i,[name,condition]] of Object.entries(source.step.flags??{}).entries()) {
    const c=substC(condition,{...noSub,flags:inlined})
    inlined[name]=c
    closed[name]={op:'all',key:`${stem}${i}`,c}
  }
  const orig={...source,params:[...source.params,r.observer],step:{...source.step,flags:closed}}
  const lift={orig,vars:{},maps:{[ghost]:{start:0,write:{key:r.point,value:contribution(map=>post(map,r.point))}}}}
  if (!ghostedOk(lift)) return
  const full=ghostedMachine(lift)
  const target={...full,state:{...full.state,[sum]:n(0)},sums:{[sum]:{term:get(ghost,x(sd.key)),key:sd.key}}}
  if (!eq(target,p.target)) return

  const publicEntry=p.laws.findIndex(l=>l.name===law.name), pointEntry=p.laws.findIndex(l=>l.name===p.pointLaw)
  if (publicEntry<0||pointEntry<0||publicEntry===pointEntry) return
  const publicLaw={name:law.name,holds:substC(law.holds,{...noSub,vars:{[law.forall]:x(r.observer)}})}
  const binder=p.laws[pointEntry]!.forall
  if (!binder) return
  const rowLaw={name:p.pointLaw,forall:binder,holds:same(get(ghost,x(binder)),contribution(map=>get(map,x(binder))))}
  if (!eq(publicLaw,p.laws[publicEntry])||!eq(rowLaw,p.laws[pointEntry])) return
  const laws:Law[]=p.laws.map((entry,i)=>i===publicEntry?publicLaw:i===pointEntry?rowLaw:entry)
  if (laws.some(l=>l.keys?.length||l.some?.length||l.ex||l.finite!==undefined)) return
  return {orig,lift,target,laws,publicEntry}
}

export function checkGhostWrite(source:Machine,law:Law,p:GhostWriteCertificate):boolean {
  try {
    const t=ghostWriteTheory(source,law,p)
    return !!t && sideGoals(t.target,t.laws).length===0 && checkLaws(t.target,t.laws,p.proof)
  } catch { return false }
}

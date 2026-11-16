// Retained witnesses and ghost updates are untrusted proposals, never a source proof.
import type {C,E,Law,Machine,SomeWitness} from '../../core/machine.ts'
import type {Ghosted} from '../../kernel/kernel.ts'
import type {SeedBindings,SeedLayout} from './candidate-seed-restatement.ts'
import {abstractWitnessValues} from './witness-value-proxies.ts'

export type RetainedWitnessContext={original:Machine,laws:Law[],G:Ghosted,plains:Record<string,{plain:Law,sub:Record<string,E>}>,family:Law[]}
export type WitnessSeedAudit={status:'proposed',name:string,sourceVariables:number,targetVariables:number,ghostMaps:Record<string,string>,helperMode:'guarded-equality',trusted:false}
export type WitnessSeedProposal={witnesses:Record<string,SomeWitness>,ghosts:Pick<Ghosted,'vars'|'maps'>,bindings:SeedBindings,laws:Law[],audit:WitnessSeedAudit[]}
const same=(a:unknown,b:unknown)=>JSON.stringify(a)===JSON.stringify(b)
const tuple=(xs:E[]):E=>xs.length===1?xs[0]!:{op:'tup',a:xs[0]!,b:tuple(xs.slice(1))}
const nativeParts=(e:E):E[]=>e.op==='tup'?[e.a,...nativeParts(e.b)]:[e]
const variable=(e:E,expected?:string):string=>{if(e.op!=='var'||expected!==undefined&&e.name!==expected)throw Error('witness coordinate is not the expected binder');return e.name}
function reads(x:unknown,map:string):Extract<E,{op:'get'}>[] {
 const out:Extract<E,{op:'get'}>[]=[]
 const visit=(v:unknown):void=>{if(Array.isArray(v)){v.forEach(visit);return}if(!v||typeof v!=='object')return;const o=v as any;if(o.op==='get'&&o.map===map)out.push(o);Object.values(o).forEach(visit)}
 visit(x);return out
}
function packed(e:E,layout:SeedLayout):E[]{
 const terms:{term:E,coefficient:number}[]=[]
 const visit=(x:E,k:number):void=>{if(x.op==='add'){visit(x.a,k);visit(x.b,k)}else if(x.op==='mul')visit(x.a,k*x.k);else if(x.op==='const'&&x.value===0){}else terms.push({term:x,coefficient:k})}
 visit(e,1)
 const powers=layout.sorts.map((_,i)=>layout.radix**(layout.sorts.length-i-1))
 if(!Number.isSafeInteger(layout.radix)||layout.radix<2||powers.some(p=>!Number.isSafeInteger(p))||terms.length!==powers.length)throw Error('unsupported packed witness shape')
 return powers.map(p=>{const xs=terms.filter(t=>t.coefficient===p);if(xs.length!==1)throw Error('packed witness coefficient mismatch');return xs[0]!.term})
}
function onlyRead(law:Law,map:string):Extract<E,{op:'get'}>{const xs=reads(law.holds,map);if(xs.length!==1)throw Error(`ambiguous witness role for ${map}`);return xs[0]!}

/** Restricted recognizer for the retained no-lost-keys witness: one owner or a
 * transfer tuple. Binding is by actual map-coordinate roles, not generated names.
 * A full native check of the resulting family is still mandatory. */
export function adaptCandidateSeedWitness(source:RetainedWitnessContext,target:Machine,publicLaws:Law[],config:SeedBindings):WitnessSeedProposal {
 if(!source?.G||!same(source.original,source.G.orig)||Object.keys(source.G.vars).length)throw Error('unsupported retained witness producer')
 const owner=config.maps.Owner,transfer=config.maps.TransferMsg
 if(!owner||!transfer||!same(owner.sorts,['Key','Node'])||!same(transfer.sorts,['Node','Key','Value']))throw Error('unsupported witness role layouts')
 if(!same(target.relations?.[owner.target],owner.sorts)||!same(target.relations?.[transfer.target],transfer.sorts))throw Error('native witness role layout mismatch')
 const selected=publicLaws.filter(l=>l.some?.length)
 if(selected.length!==1)throw Error('expected one native existential law')
 const to=selected[0]!,froms=source.laws.filter(l=>l.name===to.name)
 if(froms.length!==1)throw Error('retained public witness law is absent or ambiguous')
 const from=froms[0]!,sub=source.plains[to.name]?.sub
 if(!from.forall||!to.forall||from.keys?.length||to.keys?.length||from.some?.length!==2||to.some?.length!==4||!sub||Object.keys(sub).length!==2)throw Error('unsupported existential witness scope')
 const oldOwner=packed(onlyRead(from,'Owner').key,owner),oldTransfer=onlyRead(from,'TransferMsg').key
 variable(oldOwner[0]!,from.forall)
 const oldX=variable(oldOwner[1]!),oldZ=variable(oldTransfer)
 if(!same([...from.some].sort(),[oldX,oldZ].sort()))throw Error('source existential roles do not cover its binders')
 const newOwner=nativeParts(onlyRead(to,owner.target).key),newTransfer=nativeParts(onlyRead(to,transfer.target).key)
 if(newOwner.length!==2||newTransfer.length!==3)throw Error('native witness tuple arity mismatch')
 variable(newOwner[0]!,to.forall)
 const targets=[variable(newOwner[1]!),...newTransfer.map(e=>variable(e))]
 if(new Set(targets).size!==4||!same([...targets].sort(),[...to.some].sort()))throw Error('native existential roles do not cover its binders')
 const parts=[sub[oldX]!,...packed(sub[oldZ]!,transfer)]
 if(parts.some(p=>!p))throw Error('incomplete retained witness')
 const sorts=['Node','Node','Key','Value'],valueSorts:Record<string,string>=Object.create(null)
 const oldMaps=source.G.maps
 const checkWitness=(e:E,sort:string):void=>{
  if(e.op==='var'){if(e.name!==from.forall||sort!=='Key')throw Error('witness uses an unbound or mistyped variable');return}
  if(e.op!=='get'||!Object.hasOwn(oldMaps,e.map)||e.key.op!=='var'||e.key.name!==from.forall)throw Error('unsupported retained witness coordinate term')
  if(valueSorts[e.map]&&valueSorts[e.map]!==sort)throw Error('conflicting ghost value sort')
  valueSorts[e.map]=sort
 }
 parts.forEach((p,i)=>checkWitness(p,sorts[i]!))
 if(Object.keys(oldMaps).some(n=>!valueSorts[n]))throw Error('retained ghost has no witnessed value role')
 const reserved=new Set([...target.params,...target.inputs,...Object.keys(target.state),...Object.keys(target.maps??{}),...Object.keys(target.fns??{}),...Object.keys(target.counts??{}),...Object.keys(target.step.flags??{})])
 for(const l of publicLaws)for(const name of [l.forall,...(l.keys??[]),...(l.some??[])])if(name)reserved.add(name)
 const aliases:Record<string,string>=Object.create(null)
 for(const name of Object.keys(oldMaps)){let n=`seed$witness$${name}`;while(reserved.has(n))n+='$';reserved.add(n);aliases[name]=n}
 const allLayouts={...config.maps,...Object.fromEntries(Object.keys(oldMaps).map(n=>[n,{target:aliases[n]!,sorts:['Key'],radix:owner.radix}]))}
 const flags=target.step.flags??{}, allowed=new Set([...target.params,...target.inputs,...Object.keys(target.state)])
 const inputSorts:Record<string,string>={}
 const remember=(e:E,sort:string):void=>{if(e.op!=='var'||!target.inputs.includes(e.name))return;if(inputSorts[e.name]&&inputSorts[e.name]!==sort)throw Error('conflicting native input sort');inputSorts[e.name]=sort}
 const scan=(x:unknown):void=>{if(Array.isArray(x)){x.forEach(scan);return}if(!x||typeof x!=='object')return;const o=x as any;if(o.op==='get'){const l=Object.values(config.maps).find(l=>l.target===o.map);if(l){const ps=nativeParts(o.key);if(ps.length===l.sorts.length)ps.forEach((p,i)=>remember(p,l.sorts[i]!))}}Object.values(o).forEach(scan)}
 scan(target.step)
 for(const [name,w]of Object.entries(target.step.maps??{})){const l=Object.values(config.maps).find(l=>l.target===name);if(l&&'key'in w){const ps=nativeParts(w.key);if(ps.length===l.sorts.length)ps.forEach((p,i)=>remember(p,l.sorts[i]!))}}
 const term=(e:E,rename:Record<string,string>={}):E=>{
  switch(e.op){
   case 'var':{const name=rename[e.name]??e.name;if(!allowed.has(name)&&name!==to.forall)throw Error(`unmapped witness variable ${name}`);return{op:'var',name}}
   case 'const':if(!Number.isSafeInteger(e.value)||e.value<0)throw Error('invalid witness constant');return e
   case 'get':{const l=allLayouts[e.map];if(!l||!Object.hasOwn(target.maps??{},l.target)&&!Object.values(aliases).includes(l.target))throw Error(`unmapped witness map ${e.map}`);const ps=l.sorts.length===1?[e.key]:packed(e.key,l);return{op:'get',map:l.target,key:tuple(ps.map(p=>term(p,rename)))}}
   case 'if':return{...e,c:cond(e.c,rename),then:term(e.then,rename),else:term(e.else,rename)}
   case 'mul':if(!Number.isSafeInteger(e.k)||e.k<0)throw Error('invalid witness coefficient');return{...e,a:term(e.a,rename)}
   case 'proj':throw Error('unsupported witness projection')
   case 'add':case 'sub':case 'min':case 'max':case 'prod':case 'tup':return{...e,a:term(e.a,rename),b:term(e.b,rename)}
  }
 }
 const cond=(c:C,rename:Record<string,string>={}):C=>{
  switch(c.op){
   case 'flag':if(!Object.hasOwn(flags,c.name))throw Error(`unmapped witness flag ${c.name}`);return c
   case 'all':throw Error('unsupported quantified ghost update')
   case 'not':return{...c,x:cond(c.x,rename)}
   case 'and':case 'or':return{...c,xs:c.xs.map(x=>cond(x,rename))}
   case '=':if(same(c.a,c.b))return{op:'<=',a:{op:'const',value:0},b:{op:'const',value:0}};else{let a:E[]|undefined,b:E[]|undefined;try{a=packed(c.a,transfer);b=packed(c.b,transfer)}catch{}if(a&&b)return{op:'=',a:tuple(a.map(e=>term(e,rename))),b:tuple(b.map(e=>term(e,rename)))};return{...c,a:term(c.a,rename),b:term(c.b,rename)}}
   case '<':case '<=':{if(c.op==='<'&&c.a.op==='var'&&c.b.op==='const'&&c.b.value===owner.radix&&inputSorts[c.a.name]){const bound=config.domains[inputSorts[c.a.name]!];if(!bound||!target.params.includes(bound))throw Error('missing witness input domain');return{...c,a:term(c.a,rename),b:{op:'var',name:bound}}}return{...c,a:term(c.a,rename),b:term(c.b,rename)}}
  }
 }
 const maps:Ghosted['maps']=Object.create(null)
 for(const [name,g]of Object.entries(oldMaps)){
  if(g.start!==0||!('key'in g.write)||g.write.key.op!=='var'||inputSorts[g.write.key.name]!=='Key')throw Error('unsupported ghost point update')
  maps[aliases[name]!]={start:0,write:{key:term(g.write.key),value:term(g.write.value)}}
 }
 const rename={[from.forall]:to.forall},terms=Object.fromEntries(targets.map((n,i)=>[n,term(parts[i]!,rename)]))
 const augmented:SeedBindings={...config,maps:allLayouts,fields:Object.fromEntries(Object.entries(config.fields??{}).filter(([n])=>!Object.hasOwn(oldMaps,n)))}
 const abstracted=abstractWitnessValues(source.family,augmented,valueSorts)
 return{witnesses:{[to.name]:{terms}},ghosts:{vars:{},maps},bindings:abstracted.bindings,laws:abstracted.laws,
  audit:[{status:'proposed',name:to.name,sourceVariables:2,targetVariables:4,ghostMaps:aliases,helperMode:'guarded-equality',trusted:false}]}
}

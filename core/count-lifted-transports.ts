// Untrusted transport matching. Images describe the discovered write and a
// region's existing row-agreement premise; no image or relation is an axiom.
// Emitters must prove every selected relation on the unchanged machine.
import {type C,type E,type Law,type Machine,all,get,n,not,plus,same,times,walkOnce,x} from './machine.ts'
import {countsForReads} from './count-facts.ts'
import {type LiftedCountGuardShape,discoverLiftedCountGuard,discoverLiftedCountOperation} from './count-lifted-shape.ts'
import {type Count,type MapRead,substE} from '../kernel/kernel.ts'
import {discoverCountRowLoad} from './count-load-shape.ts'
import {inlineFrozenGuard} from './count-frozen-guard.ts'
type Image={kind:'row',row:E}|{kind:'source',map:string}|{kind:'empty'}
type Formula=boolean|{atom:string}|{not:Formula}|{op:'and'|'or',xs:Formula[]}
export type LiftedTransport={post:MapRead,target?:MapRead,kind:'equality'|'upper'|'zero',postBody:E,targetBody:E,derived:boolean,derivedFrom?:number[]}
export type LiftedTransportRegion={name:string,when:C[],premises:Law[],tuples:E[][],activeTuple:E[],relations:LiftedTransport[],partitions:{terms:[number,string][]}[],unmatched:{read:MapRead,body:E}[]}
const json=(value:unknown)=>JSON.stringify(value)
const neg=(f:Formula):Formula=>typeof f==='boolean'?!f:'not'in f?f.not:{not:f}
const join=(op:'and'|'or',items:Formula[]):Formula=>{
 const xs=items.flatMap(f=>typeof f!=='boolean'&&'op'in f&&f.op===op?f.xs:[f])
 if(xs.includes(op==='or'))return op==='or'
 const terms=new Set(xs.map(json));if(xs.some(f=>terms.has(json(neg(f)))))return op==='or'
 const unique=[...new Map(xs.filter(f=>f!==(op==='and')).map(f=>[json(f),f])).entries()].sort(([a],[b])=>a.localeCompare(b)).map(([,f])=>f)
 return !unique.length?op==='and':unique.length===1?unique[0]!:{op,xs:unique}
}
const normalize=(value:E):string=>{
 if(value.op==='const')return String(value.value)
 if(value.op==='var')return '$'+value.name
 if(value.op==='get')return value.map+'['+normalize(value.key)+']'
 if(value.op==='add')return [normalize(value.a),normalize(value.b)].sort().join('+')
 if(value.op==='mul')return value.k+'*'+normalize(value.a)
 return json(value)
}
function formula(c:C):Formula{
 if(c.op==='and'||c.op==='or')return join(c.op,c.xs.map(formula))
 if(c.op==='not')return neg(formula(c.x))
 if(c.op==='='||c.op==='<='||c.op==='<'){
  const a=c.a,b=c.b
  if(a.op==='const'&&b.op==='const')return c.op==='='?a.value===b.value:c.op==='<='?a.value<=b.value:a.value<b.value
  if(c.op==='='&&b.op==='const'&&(b.value===0||b.value===1))return b.value===1?body(a):neg(body(a))
  if(c.op==='='&&a.op==='const'&&(a.value===0||a.value===1))return a.value===1?body(b):neg(body(b))
  if(c.op==='<='&&a.op==='const'&&a.value===1)return body(b)
  const pair=[normalize(a),normalize(b)];if(c.op==='=')pair.sort()
  return {atom:c.op+json(pair)}
 }
 return {atom:json(c)}
}
function body(e:E):Formula{
 if(e.op==='const'&&(e.value===0||e.value===1))return !!e.value
 if(e.op==='if')return join('or',[join('and',[formula(e.c),body(e.then)]),join('and',[neg(formula(e.c)),body(e.else)])])
 return {atom:'present:'+normalize(e)}
}
function images(value:E,shape:LiftedCountGuardShape,rows:ReadonlyMap<string,Image>,fields:ReadonlySet<string>):E{
 const visit=(node:unknown):unknown=>{
  if(!node||typeof node!=='object')return node
  if(Array.isArray(node))return node.map(visit)
  const e=node as E
  if(e.op==='get'&&fields.has(e.map)){const image=rows.get(json(e.key));if(image?.kind==='row')return get(e.map,image.row)}
  if(e.op==='get'&&e.map===shape.origin.membershipMap&&e.key.op==='add'){
   const [base,column]=e.key.a.op==='mul'?[e.key.a,e.key.b]:[e.key.b,e.key.a]
   if(base.op==='mul'&&base.k===shape.origin.width){
    const image=rows.get(json(base.a))
    if(image?.kind==='empty')return n(0)
    if(image?.kind==='source')return get(image.map,column)
    if(image?.kind==='row')return get(e.map,plus(times(shape.origin.width,image.row),column))
   }
  }
  return Object.fromEntries(Object.entries(node).map(([key,child])=>[key,visit(child)]))
 }
 return visit(value) as E
}
// A syntactic Boolean-body match is only a transport proposal. Its witness
// obligation still passes through the unchanged native checker.
export function matchLiftedCountBodies(left:Count,right:Count):boolean{
 if(json(left.below)!==json(right.below))return false
 let member='match$member';const scope=json([left,right]);while(scope.includes(member))member='$'+member
 const canonical=(count:Count)=>body(substE(count.body,{vars:{[count.key]:x(member)},maps:{},flags:{}}))
 return json(canonical(left))===json(canonical(right))
}
// These are identities in the matcher's Boolean abstraction, not CountInsts.
// Raw comparisons may have different but equivalent spellings in the two
// generator paths. Only a later native proof can validate their use on counts.
export function proposeTransportPartitions(counts:Count[]):{terms:[number,string][]}[]{
 const result:{terms:[number,string][]}[]=[],groups=new Map<string,Count[]>()
 for(const count of counts){const key=json(count.below),group=groups.get(key)??[];group.push(count);groups.set(key,group)}
 for(const group of groups.values()){
  if(group.length>32)continue
  const fs=group.map(count=>body(count.body)),atoms=new Set<string>()
  const gather=(f:Formula):void=>{if(typeof f==='boolean')return;if('atom'in f)atoms.add(f.atom);else if('not'in f)gather(f.not);else f.xs.forEach(gather)}
  fs.forEach(gather);if(atoms.size>8)continue
  const keys=[...atoms].sort(),positions=new Map(keys.map((key,index)=>[key,index]))
  const evaluate=(f:Formula,bits:number):boolean=>typeof f==='boolean'?f:'atom'in f?!!(bits&(1<<positions.get(f.atom)!)):'not'in f?!evaluate(f.not,bits):f.op==='and'?f.xs.every(child=>evaluate(child,bits)):f.xs.some(child=>evaluate(child,bits))
  const masks=fs.map(f=>{let mask=0n;for(let bits=0;bits<2**keys.length;bits++)if(evaluate(f,bits))mask|=1n<<BigInt(bits);return mask})
  for(let b=0;b<group.length;b++)for(let c=b+1;c<group.length;c++){
   if(!masks[b]||!masks[c]||(masks[b]!&masks[c]!)!==0n)continue
   for(let a=0;a<group.length;a++)if(masks[a]===(masks[b]!|masks[c]!))result.push({terms:[[1,group[a]!.v],[-1,group[b]!.v],[-1,group[c]!.v]]})
  }
 }
 return result
}
export function liftedCopyTuples(law:Law,source:E):E[][]{
 if(!law.forall||law.keys?.length!==3)return []
 const a=x(law.forall+'#'),b=x(law.keys[0]!),rest=law.keys.slice(1).map(x)
 return [[a,b,...rest],[a,source,...rest],[source,b,...rest],[source,source,...rest]]
}
// Integer row reduction is only scheduling metadata. A derived mark still
// requires the emitter's checked base relations and final arithmetic proof.
function spanned(target:Map<string,bigint>,rows:Map<string,bigint>[]):boolean{
 const names=[...new Set([...target.keys(),...rows.flatMap(row=>[...row.keys()])])].sort(),basis=new Map<number,bigint[]>()
 const reduce=(input:Map<string,bigint>)=>{
  let a=names.map(name=>input.get(name)??0n)
  for(let i=0;i<a.length;i++)if(a[i]){
   const b=basis.get(i);if(!b)return {a,pivot:i}
   const q=a[i]!,p=b[i]!;a=a.map((value,j)=>p*value-q*b[j]!)
   const abs=(value:bigint)=>value<0n?-value:value,gcd=(left:bigint,right:bigint):bigint=>right?gcd(right,left%right):abs(left),divisor=a.reduce(gcd,0n)
   if(divisor>1n)a=a.map(value=>value/divisor)
  }
  return {a,pivot:-1}
 }
 for(const row of rows){const {a,pivot}=reduce(row);if(pivot>=0)basis.set(pivot,a)}
 return reduce(target).pivot<0
}
export function proposeLiftedTransports(m:Machine,family:Law[],law:Law,value:number):LiftedTransportRegion[]|undefined{
 const shape=discoverLiftedCountGuard(m,law,family),operation=shape&&discoverLiftedCountOperation(m,shape,value)
 if(!shape||!operation||!law.forall||law.keys?.length!==3)return
 const a=x(law.forall+'#'),b=x(law.keys[0]!),copy='copy'in operation?operation.copy:undefined,write='write'in operation?operation.write:undefined
 const load=operation.kind==='load'?discoverCountRowLoad(m,shape,family,operation):undefined
 const writer=copy?x(copy.to):write?x(write.source):operation.kind==='threshold-replace'?x(shape.origin.rowInput):load?x(load.written):undefined
 if(!writer)return []
 const guard=copy?.guard??write?.guard??load?.guard??shape.origin.guard,active=inlineFrozenGuard(m.step.flags??{},guard)
 let keyName='transport$member';const scope=json([m,law]);while(scope.includes(keyName))keyName='$'+keyName
 const declarations=Object.entries(m.counts??{}).map(([map,definition])=>({...definition,map})),post:MapRead[]=[]
 walkOnce(law.holds,(node:any)=>{if(node.op==='get'&&shape.countMaps.includes(node.map)){const key=substE(node.key,{vars:{[law.forall!]:a},maps:{},flags:{}}),read:MapRead=['post$'+post.length,node.map+'#',key];if(!post.some(r=>r[1]===read[1]&&json(r[2])===json(key)))post.push(read)}})
 const regions:{name:string,when:C[],premises:Law[],tuples:E[][],activeTuple:E[],postImages:Map<string,Image>,preImages:Map<string,Image>,upper:boolean}[]=[]
 const add=(name:string,when:C[],premises:Law[],tuples:E[][],postImages:Map<string,Image>,preImages=new Map<string,Image>(),upper=false,activeTuple=tuples[0]!)=>regions.push({name,when:[...(m.pre?[m.pre]:[]),active,...when],premises,tuples,activeTuple,postImages,preImages,upper})
 if(copy){
  const from=x(copy.from),tuples=liftedCopyTuples(law,from)
  for(let bits=0;bits<4;bits++){
   const left=!!(bits&2),right=!!(bits&1),map=new Map<string,Image>([[json(a),{kind:'row',row:left?from:a}],[json(b),{kind:'row',row:right?from:b}]])
   add('copy-'+bits,[left?same(a,writer):not(same(a,writer)),right?same(b,writer):not(same(b,writer))],[],tuples,map,new Map(),true,tuples[bits]!)
  }
 }else if(operation.kind==='threshold-replace'){
  const agreement=shape.rowAgreements[0]
  if(!agreement)return
  for(const left of [true,false]){
   const actor=left?a:b,other=left?b:a,preImages=new Map<string,Image>([[json(other),{kind:'row',row:writer}]]),postImages=new Map(preImages)
   postImages.set(json(actor),{kind:'source',map:shape.origin.requestSet})
   const rowGuard=substE({op:'if',c:agreement.shape.guard,then:n(1),else:n(0)},{vars:{[agreement.shape.left]:writer,[agreement.shape.right]:other},maps:{},flags:{}})
   add(left?'replacement-left-equal':'replacement-right-equal',[same(actor,writer),not(same(other,writer)),rowGuard.op==='if'?rowGuard.c:all()], [agreement.law],[[a,b,...law.keys.slice(1).map(x)]],postImages,preImages)
  }
 }else if(load){
  for(const both of [true,false]){
   const postImages=new Map<string,Image>([[json(a),both?{kind:'source',map:load.source}:{kind:'row',row:a}],[json(b),both?{kind:'source',map:load.source}:{kind:'row',row:b}]])
   add(both?'load-both':'load-neither',[both?same(a,writer):not(same(a,writer)),both?same(b,writer):not(same(b,writer))],[load.law,...load.phaseLaws],[[a,b,...law.keys.slice(1).map(x)]],postImages)
  }
  for(const left of [true,false])for(const marked of [true,false]){
   const actor=left?a:b,other=left?b:a,map=new Map<string,Image>([[json(actor),{kind:'source',map:load.source}],[json(other),marked?{kind:'source',map:load.source}:{kind:'empty'}]])
   add('load-'+(left?'left':'right')+'-'+(marked?'marked':'empty'),[same(actor,writer),not(same(other,writer)),marked?same(get(load.marker.map,other),n(load.marker.value)):same(get(load.marker.map,other),n(0))],[load.law,...load.phaseLaws],[[a,b,...law.keys.slice(1).map(x)]],map,new Map([[json(other),marked?{kind:'source',map:load.source}:{kind:'empty'}]]))
  }
 }else return []
 return regions.map(region=>{
  const candidates:MapRead[]=[]
  const put=(map:string,key:E)=>{if(!candidates.some(read=>read[1]===map&&json(read[2])===json(key)))candidates.push(['pre$'+candidates.length,map,key])}
  for(const tuple of region.tuples)for(const read of post)put(read[1].slice(0,-1),substE(read[2],{vars:{[a.op==='var'?a.name:'']:tuple[0]!,[b.op==='var'?b.name:'']:tuple[1]!},maps:{},flags:{}}))
  for(const endpoint of [a,b,writer])put(shape.origin.rowCount,endpoint)
  for(const [map,definition]of Object.entries(m.counts??{})){
   if(definition.base)continue
   const fields=new Set<string>(),variables=new Set<string>();walkOnce(definition.body,(node:any)=>{if(node.op==='get')fields.add(node.map);if(node.op==='var')variables.add(node.name)})
   if(!variables.has(definition.j)&&fields.size&&[...fields].every(field=>field===shape.origin.requestSet||field===shape.origin.membershipMap))put(map,n(0))
  }
  const records:{read:MapRead,count:Count,isPost:boolean}[]=[]
  for(const [isPost,reads,selectedImages]of [[true,post,region.postImages],[false,candidates,region.preImages]] as const)for(const read of reads){
   const raw:[string,string,E]=[read[0],read[1].replace(/#$/,''),read[2]],count=countsForReads(declarations,[raw])?.[0];if(!count)continue
   records.push({read,count:{...count,key:keyName,body:images(substE(count.body,{vars:{[count.key]:x(keyName)},maps:{},flags:{}}),shape,selectedImages,copy?new Set([shape.countShape.memberField,shape.countShape.thresholdField,...shape.rowAgreement?.fields??[]]):new Set())},isPost})
  }
  const relations:LiftedTransport[]=[],unmatched:LiftedTransportRegion['unmatched']=[]
  for(const record of records.filter(record=>record.isPost)){
   const key=json(body(record.count.body)),matches=records.filter(other=>other.read[0]!==record.read[0]&&json(body(other.count.body))===key)
   if(key==='false')relations.push({post:record.read,kind:'zero',postBody:record.count.body,targetBody:n(0),derived:false})
   for(const match of matches)relations.push({post:record.read,target:match.read,kind:region.upper&&!shape.origin.twins.some(twin=>twin.row===record.read[1].slice(0,-1))&&record.read[1]!==shape.origin.rowCount+'#'?'upper':'equality',postBody:record.count.body,targetBody:match.count.body,derived:false})
   for(const target of records.filter(other=>other.isPost&&other.read[1]===shape.origin.rowCount+'#'&&other.read[0]!==record.read[0]&&(key==='false'||json(body(other.count.body))!==key)))if(join('and',[body(record.count.body),neg(body(target.count.body))])===false)relations.push({post:record.read,target:target.read,kind:'upper',postBody:record.count.body,targetBody:target.count.body,derived:false})
   if(!relations.some(relation=>relation.post[0]===record.read[0]))unmatched.push({read:record.read,body:record.count.body})
  }
  const membershipMaps=new Set([shape.origin.membershipMap,shape.origin.requestSet,...load?[load.source]:[]])
  const partitionCounts=records.map(record=>record.count).filter(count=>{const fields:string[]=[];walkOnce(count.body,(node:any)=>{if(node.op==='get')fields.push(node.map)});return fields.every(field=>membershipMaps.has(field))})
  const partitions=proposeTransportPartitions(partitionCounts)
  const vector=(terms:[number,string][])=>new Map(terms.map(([coefficient,id])=>[id,BigInt(coefficient)]))
  const relationVector=(relation:LiftedTransport)=>vector([[1,relation.post[0]],...(relation.target?[[-1,relation.target[0]] as [number,string]]:[])])
  const accepted:number[]=[],basis=partitions.map(partition=>vector(partition.terms))
  const cost=(relation:LiftedTransport)=>{const f=json(body(relation.postBody)),atoms=[...f.matchAll(/"atom":/g)].length;return atoms*2+(f.includes('"not":')?0:1)}
  for(const index of relations.map((_,index)=>index).sort((a,b)=>cost(relations[a]!)-cost(relations[b]!))){
   const relation=relations[index]!;if(relation.kind!=='equality')continue
   const row=relationVector(relation)
   if(spanned(row,basis)){relation.derived=true;relation.derivedFrom=[...accepted]}
   else{basis.push(row);accepted.push(index)}
  }
  return {name:region.name,when:region.when,premises:region.premises,tuples:region.tuples,activeTuple:region.activeTuple,relations,partitions,unmatched}
 })
}

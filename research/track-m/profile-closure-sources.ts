// Static receipt analysis only: no prover queries or new assumptions.
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
const out=process.argv[2]!,referenceFile=process.argv[3]!
if(!out||!referenceFile)throw new Error('usage: profile-closure-sources.ts output-directory v3-summary.json')
const lines=readFileSync(join(out,'closure-source-profile.log'),'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l))
const artifact=lines.find(x=>x.artifact==='source-profile'),receipt=lines.find(x=>x.falsification)
if(!artifact||!receipt)throw new Error('missing profile or result receipt')
const profile=JSON.parse(gunzipSync(Buffer.from(artifact.data,'base64')).toString())
const reference=JSON.parse(readFileSync(referenceFile,'utf8')).results.find((r:any)=>r.version===3&&r.law===profile.law)
if(!reference)throw new Error('missing exact v3 law')
const targets=reference.attempts.filter((a:any)=>!a.checked),ids=new Set(profile.reads.map((r:any)=>r[0])),members=new Set(profile.insts.map((i:any)=>i.wit))
function stats(value:any){
 const counts=new Set<string>(),direct=new Set<string>(),vars=new Set<string>(),maps=new Set<string>(),ops:Record<string,number>={};let nodes=0
 const visit=(v:any):void=>{
  if(!v||typeof v!=='object')return
  if(Array.isArray(v)){v.forEach(visit);return}
  if(typeof v.op==='string'){nodes++;ops[v.op]=(ops[v.op]??0)+1}
  if(v.op==='var'){vars.add(v.name);if(ids.has(v.name))counts.add(v.name)}
  if(v.op==='get'){maps.add(v.map);for(const r of profile.reads)if(r[1]===v.map&&JSON.stringify(r[2])===JSON.stringify(v.key))direct.add(r[0])}
  Object.values(v).forEach(visit)
 }
 visit(value)
 return {nodes,ifs:ops.if??0,ops,counts:[...new Set([...counts,...direct])].sort((a,b)=>Number(a.slice(2))-Number(b.slice(2))),proxyCounts:[...counts],directCounts:[...direct],vars:[...vars].sort(),maps:[...maps].sort()}
}
function instanceClauses(goal:any){return goal.hyps.filter((h:any)=>h.op==='or'&&h.xs[0]?.op==='<='&&stats(h.xs[0]).proxyCounts.length>0).length}
const actual=profile.sources.filter((s:any)=>!s.checked).map((s:any)=>s.index)
if(JSON.stringify(actual)!==JSON.stringify(targets.map((t:any)=>t.index)))throw new Error('unknown source set changed under profiling')
const rows=targets.map((old:any)=>{
 const s=profile.sources.find((p:any)=>p.index===old.index),shape=stats(s.source.hyps),reconstruction=s.reconstructionGoal&&stats(s.reconstructionGoal.hyps)
 if(s.source.hyps.length!==old.sourceHyps||JSON.stringify(s.terms)!==JSON.stringify(old.terms))throw new Error(`source ${s.index} changed`)
 if(s.pointOutcome!=='unknown'||s.pointWhy!=='time'||s.pointCoreSize!==undefined)throw new Error(`unexpected point result at ${s.index}`)
 return {index:s.index,wit:s.wit,terms:s.terms,hyps:s.source.hyps.length,reconstructionHyps:s.reconstructionGoal?.hyps.length,countInstances:instanceClauses(s.source),reconstructionCountInstances:s.reconstructionGoal&&instanceClauses(s.reconstructionGoal),countReads:shape.counts,proxyCountReads:shape.proxyCounts,directCountReads:shape.directCounts,auxiliaryWitnesses:shape.vars.filter(w=>w.startsWith('w?')),foreignMembers:shape.vars.filter(w=>members.has(w)&&w!==s.wit),nodes:shape.nodes,ifs:shape.ifs,maps:shape.maps,reconstructionNodes:reconstruction?.nodes,reconstructionIfs:reconstruction?.ifs,pointOutcome:s.pointOutcome,pointWhy:s.pointWhy,pointCoreSize:s.pointCoreSize??null,pointCountedMs:s.pointCountedMs,booleanCountedMs:s.booleanCountedMs,pointWallMs:s.pointWallMs,booleanWallMs:s.booleanWallMs,totalCountedMs:s.ms,originalCountedMs:old.ms,transportWallMs:s.transportWallMs,admissionWallMs:s.admissionWallMs}
})
const union=profile.sources.find((s:any)=>s.index===39),last=receipt.attempts.find((a:any)=>a.index===39)?.last
const unionHypotheses=union.source.hyps.map((hyp:any,index:number)=>({index,...stats(hyp)}))
const form=(lin:Record<string,number>)=>JSON.stringify(Object.entries(lin).sort(([a],[b])=>a.localeCompare(b)))
const has=(path:any[],lin:Record<string,number>,holds:boolean)=>path.some(([,a])=>a.holds===holds&&form(a.lin)===form(lin))
const residualAliasConflict={
 rowAtMostWriter:has(union.path,{'a$#':1,i:-1},true),
 writerAtMostRow:has(union.path,{i:1,'a$#':-1},true),
 memberAbsent:has(last.path,{'1':1,[`S[${union.wit}:1]`]:-1},false),
 aliasedMemberPresent:has(last.path,{'1':1,[`S[a$#:64,i:-64,${union.wit}:1]`]:-1},true),
 explanation:'a$#=i makes 64*a$#-64*i+w equal w; the last path has S[w]<=0 and S[64*a$#-64*i+w]>=1. This branch is inconsistent, not a SAT model. It does not prove the whole union.'
}
if(!residualAliasConflict.rowAtMostWriter||!residualAliasConflict.writerAtMostRow||!residualAliasConflict.memberAbsent||!residualAliasConflict.aliasedMemberPresent)throw new Error('recorded residual alias conflict changed')
const aggregate={unknownSources:rows.length,allOriginalSourcesMatched:true,allPointQueriesTimedOut:true,allUnreduced:rows.every((r:any)=>r.hyps===r.reconstructionHyps),allSingleInstance:rows.every((r:any)=>r.countInstances===1&&r.reconstructionCountInstances===1),auxiliaryWitnesses:[...new Set(rows.flatMap((r:any)=>r.auxiliaryWitnesses))],foreignMembers:[...new Set(rows.flatMap((r:any)=>r.foreignMembers))],nodes:{min:Math.min(...rows.map((r:any)=>r.nodes)),max:Math.max(...rows.map((r:any)=>r.nodes))},ifs:{min:Math.min(...rows.map((r:any)=>r.ifs)),max:Math.max(...rows.map((r:any)=>r.ifs))},countedMs:rows.reduce((n:number,r:any)=>n+r.totalCountedMs,0),pointCountedMs:rows.reduce((n:number,r:any)=>n+r.pointCountedMs,0),booleanCountedMs:rows.reduce((n:number,r:any)=>n+r.booleanCountedMs,0),pointWallMs:rows.reduce((n:number,r:any)=>n+r.pointWallMs,0),booleanWallMs:rows.reduce((n:number,r:any)=>n+r.booleanWallMs,0)}
writeFileSync(join(out,'profile.json'),JSON.stringify({law:profile.law,receipt:{hyps:receipt.hyps,instances:receipt.instances,countedMs:receipt.countedMs,wallMs:receipt.wallMs,checked:receipt.checked},aggregate,reads:profile.reads,rows,unionHypotheses,residualAliasConflict},null,2)+'\n')
writeFileSync(join(out,'union-39.json'),JSON.stringify({law:profile.law,index:39,reads:profile.reads,instance:profile.insts[39],...union,lastBooleanEvent:last,residualAliasConflict},null,2)+'\n')
const short=(n:string)=>n.replace('r$','r')
const terms=(ts:any[])=>ts.map(([k,id])=>`${k===1?'+':'−'}${Math.abs(k)!==1?Math.abs(k)+'·':''}${short(id)}`).join(' ').replace(/^\+/,'')+' ≤ 0'
const table=['| Index / witness | Hyps | Count instances | AST nodes / ifs | Candidate; direct count reads | Point / Boolean units |','|---|---:|---:|---:|---|---:|',...rows.map((r:any)=>`| ${r.index} / \`${r.wit}\` | ${r.hyps} | ${r.countInstances} | ${r.nodes} / ${r.ifs} | \`${terms(r.terms)}\`; raw: ${r.directCountReads.length?r.directCountReads.map(short).join(', '):'none'} | ${r.pointCountedMs.toFixed(2)} / ${r.booleanCountedMs.toFixed(2)} |`)].join('\n')
writeFileSync(join(out,'table.md'),table+'\n')
console.log(JSON.stringify(aggregate))
console.log(table)
console.log(JSON.stringify({residualAliasConflict,unionHypotheses,columns:union.columns,maps:rows.find((r:any)=>r.index===39)?.maps}))

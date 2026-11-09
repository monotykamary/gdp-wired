// Section 15.6 root-first/model-guided row proposal. Disposable source only.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux required')
const mode=process.argv[2];if(!['before','after'].includes(mode!))throw Error('before|after required')
const change=(path:string,transform:(s:string)=>string)=>{const before=readFileSync(path,'utf8'),after=transform(before);writeFileSync(path,after);console.log(JSON.stringify({path,before:createHash('sha256').update(before).digest('hex'),after:createHash('sha256').update(after).digest('hex'),researchOnly:true}))}
const replace=(s:string,a:string,b:string)=>{if(s.split(a).length!==2)throw Error('row probe anchor '+a);return s.replace(a,b)}
const observe=(s:string)=>replace(replace(replace(s,'  const t=prove(path,Math.min(','  rowProbeStats.queries++\n  const t=prove(path,Math.min('),"if(accepted&&t){trace?.({stage:'row-mirror'","if(accepted&&t){rowProbeStats.mirrorHits++;trace?.({stage:'row-mirror'"),"if(accepted&&t){trace?.({stage:'row-case',key,cached:true","if(accepted&&t){rowProbeStats.cacheHits++;trace?.({stage:'row-case',key,cached:true")
if(mode==='before')change('core/count-recovery/row-cases.ts',s=>"import {rowProbeStats} from '../../research/track-m/section15-row-probe.ts'\n"+observe(s))
if(mode==='after'){
 change('core/count-recovery/derivability-closure.ts',s=>"import {rowProbe} from '../../research/track-m/section15-row-probe.ts'\n"+replace(s,"    trace.push({stage:'closure-model-round',",`    if(rowProbe.active){
     const sources=new Set<string>()
     for(const index of violated)for(const [,id]of cert.insts[index]!.terms){const read=cert.reads.find(r=>r[0]===id);if(read)walkLive(read[2],scope,(o:any)=>{if(o.op==='var')sources.add(o.name)})}
     rowProbe.remember(model,[...sources]);return stop('row-probe')
    }
    trace.push({stage:'closure-model-round',`))
 change('core/count-recovery/row-cases.ts',s=>{
  s=observe(s)
  s="import {chooseRowPair,rowProbe,rowProbeStats} from '../../research/track-m/section15-row-probe.ts'\n"+s
  s=replace(s," const out=split(pairs[0]!,root,", " const eager=()=>split(pairs[0]!,root,")
  const end=' // A composing caller may check this entire proposal after adding its cuts.'
  return replace(s,end,` const visit=(path:Path,remaining:RowPair[],states:Map<RowPair,string>,depth:number):Tree|undefined=>{
  if(clock()>=until)return undefined
  rowProbeStats.maxDepth=Math.max(rowProbeStats.maxDepth,depth)
  const key=pairs.map(p=>states.get(p)??'any').join('/')
  if(!remaining.length){rowProbeStats.terminalCalls++;return leaf(path,key)}
  rowProbeStats.probes++
  const proposal=rowProbe.run(()=>leaf(path,key))
  trace?.({stage:'row-root-probe',depth,proposed:!!proposal.value,model:!!proposal.point})
  if(proposal.value){if(depth===0)rowProbeStats.rootClosures++;return proposal.value}
  if(depth>=2||!options.splitEqual)return undefined
  const pick=chooseRowPair(remaining,path,proposal.point,proposal.sources)
  if(pick===undefined)return undefined
  const pair=remaining[pick]!,rest=remaining.filter((_,i)=>i!==pick)
  rowProbeStats.splits++;trace?.({stage:'row-model-pick',depth,pair: pairs.indexOf(pair)})
  return split(pair,path,p=>visit(p,rest,new Map(states).set(pair,'equal'),depth+1),p=>visit(p,rest,new Map(states).set(pair,'different'),depth+1))
 }
 let out=pairs.length<=2?visit(root,pairs,new Map(),0):undefined
 if(!out&&clock()<until){rowProbeStats.fallbacks++;trace?.({stage:'row-eager-fallback'});out=eager()}
${end}`)
 })
 change('core/count-recovery/row-cases.test.ts',s=>{
  s=replace(s,'expect(calls).toBe(3);expect(events.length)','expect(calls).toBe(1);expect(events.length)')
  s=replace(s,"expect(calls).toBe(3)\n})\ntest('mirrored row cases", "expect(calls).toBe(1)\n})\ntest('mirrored row cases")
  s=replace(s,"[[a,x('destination')],[b,x('destination')]],clock()+1500,(path,until)=>{calls++;", "[[a,x('destination')],[b,x('destination')]],clock()+1500,(path,until)=>{if(!path.size)return undefined;calls++;")
  return replace(s,"events.some(e=>e.cached&&e.proposed&&!e.checked&&e.deferred)","events.some(e=>e.stage==='row-root-probe'&&e.proposed)")
 })
}

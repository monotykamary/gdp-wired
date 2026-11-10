// Research-only, exact-anchor edits to a disposable frozen Linux tree.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
if(process.platform!=='linux'||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1')throw new Error('disposable Linux required')
const mode=process.argv[2],manifest:any[]=[],hash=(s:string)=>createHash('sha256').update(s).digest('hex')
const replace=(s:string,a:string,b:string)=>{if(s.split(a).length!==2)throw new Error('nonunique anchor: '+a);return s.replace(a,b)}
const save=(file:string,fn:(s:string)=>string)=>{const before=readFileSync(file,'utf8'),after=fn(before);writeFileSync(file,after);manifest.push({file,before:hash(before),after:hash(after)})}
if(mode==='observe'){
 save('research/protocols/ic3syn/run.ts',s=>"import {poolControl as __p} from '../../track-m/section17-control.ts'\n"+replace(s,'v = f(); return [v','v = __p.protocol(ms,f); return [v'))
 save('core/counts.ts',s=>{
  s="import {poolControl as __p} from '../research/track-m/section17-control.ts'\n"+s
  s=replace(s,"countsDump.on?.({phase: 'candidates', machine: m, laws: set})","countsDump.on?.({phase: 'candidates', machine: m, laws: set});__p.generated(m,set)")
  s=replace(s,"countsDump.on?.({phase: 'closed-family', machine: m, laws: ls, proof, checked: true})","countsDump.on?.({phase: 'closed-family', machine: m, laws: ls, proof, checked: true});__p.accepted(ls)")
  s=replace(s,'  const traced = (law: Law, ls: Law[], pass: 0 | 1, ms: number): Tried<Proof> => {','  const tracedImpl = (law: Law, ls: Law[], pass: 0 | 1, ms: number): Tried<Proof> => {')
  return replace(s,'  return {traced, get counted()',"  const traced:typeof tracedImpl=(...args)=>{const token=__p.attemptStart(...args);let result:ReturnType<typeof tracedImpl>|undefined;try{result=tracedImpl(...args);return result}finally{__p.attemptEnd(token,args[0],args[2],result)}}\n  return {traced, get counted()")
 })
}else if(mode==='pool')save('core/counts.ts',s=>{
 s=replace(s,'  const until = clock() + ms\n  if (!caller.every','  const until = __p.countedEnd(clock() + ms)\n  if (!caller.every')
 s=replace(s,'      for (const law of supportOrder(set, caller, support)) {','      const __ordered=supportOrder(set,caller,support)\n      for (const [__index,law] of __ordered.entries()) {')
 s=replace(s,'        const allotted = supportBudget(until - clock(), share, boundedSupport && caller.includes(law), structural)',"        const __lease=__p.enabled&&!was?__p.lease(m,set,law,__ordered.slice(__index).filter(l=>!kept.has(l.name)&&!carried.has(l.name)),until):undefined\n        const allotted = __lease?.allotted??supportBudget(until - clock(), share, boundedSupport && caller.includes(law), structural)")
 s=replace(s,'const supportUntil = Math.min(until, clock() + (boundedSupport ? Math.min(allotted, 5_000) : allotted)), supportWall = performance.now() + 4_800','const supportUntil = __lease?.stop??Math.min(until, clock() + (boundedSupport ? Math.min(allotted, 5_000) : allotted)), supportWall = __lease?.wall??(performance.now() + 4_800)')
 s=replace(s,'(boundedSupport ? supportUntil : until) - clock()','((boundedSupport||__lease) ? supportUntil : until) - clock()')
 s=replace(s,'return boundedSupport ? withWall(supportWall','return (boundedSupport||__lease) ? withWall(supportWall')
 s=replace(s,'      const remaining=until-clock(),share=remaining/Math.max(1,set.length-known.size),allotted=supportBudget(remaining,share,caller.includes(law),support.has(law)&&!caller.includes(law)),stop=Math.min(until,clock()+Math.min(allotted,5000)),wall=performance.now()+4800',"      const __lease=__p.enabled?__p.lease(m,set,law,set.filter(l=>!known.has(l.name)),until):undefined\n      const remaining=until-clock(),share=remaining/Math.max(1,set.length-known.size),allotted=__lease?.allotted??supportBudget(remaining,share,caller.includes(law),support.has(law)&&!caller.includes(law)),stop=__lease?.stop??Math.min(until,clock()+Math.min(allotted,5000)),wall=__lease?.wall??(performance.now()+4800)")
 return s
})
else if(mode==='combo'){
 save('research/track-m/section15-control.ts',s=>"import {poolControl as __p} from './section17-control.ts'\n"+replace(s,'t12.cap?Math.min(end,now+600):end','t12.cap?__p.fallbackEnd(end,now):end'))
 save('core/count-cases.ts',s=>{
  s="import {fallbackEnd as __cap} from '../research/track-m/section15-control.ts'\n"+s
  s=replace(s,'for(let round=0;!tree&&round<6&&clock()<caseEnd&&!pastWall();round++){','const __fallbackEnd=__cap(caseEnd)\n      for(let round=0;!tree&&round<6&&clock()<__fallbackEnd&&!pastWall();round++){')
  s=replace(s,'Math.min(caseEnd,clock()+(options.queryMs??200))','Math.min(__fallbackEnd,clock()+(options.queryMs??200))')
  s=replace(s,"if(!('tree'in q)&&q.why===REFUTED&&q.core?.length&&q.core.length<=(options.coreLimit??Infinity)){","if(!('tree'in q)&&q.why===REFUTED&&q.core?.length&&q.core.length<=(options.coreLimit??Infinity)&&clock()<__fallbackEnd){")
  s=replace(s,'out=coreGrow(core,caseEnd)','out=coreGrow(core,__fallbackEnd)')
  s=replace(s,'if(!tree&&clock()<caseEnd&&!pastWall()){','if(!tree&&clock()<__fallbackEnd&&!pastWall()){')
  s=replace(s,'until:caseEnd,units:options.units','until:__fallbackEnd,units:options.units')
  s=replace(s,'try{return grow(g,new Map(),{nodes:0,until:end,units:options.units})','try{return grow(g,new Map(),{nodes:0,until:__cap(end),units:options.units})')
  return replace(s,'const out=grow(part,new Map(),{nodes:0,until:end,units:options.units})','const out=grow(part,new Map(),{nodes:0,until:__cap(end),units:options.units})')
 })
 save('core/count-recovery/guard-cases.ts',s=>"import {fallbackEnd as __cap} from '../../research/track-m/section15-control.ts'\n"+replace(s,'until:end,units:false','until:__cap(end),units:false'))
 save('core/count-recovery/derivability-closure.ts',s=>{
  s="import {numericPhase as __numeric,classSelector as __classes} from '../../research/track-m/section15-control.ts'\n"+s
  s=replace(s,' const pool=cert.insts.flatMap',' const __selectClass=__classes(m,ds,cert,memberHints)\n const pool=cert.insts.flatMap')
  s=replace(s,'const indices=[...pending],baseGoal=numericFor()','const indices=__selectClass([...pending],scope),baseGoal=numericFor()')
  const old='natural=proveNaturalCases(numeric,scope,end,trace,{deferCheck:true}),q=natural?{tree:natural}:modelSequence(scope)(numeric,end)'
  return replace(s,old,'__phase=__numeric(()=>modelSequence(scope)(numeric,end),()=>proveNaturalCases(numeric,scope,end,trace,{deferCheck:true}),q=>!!validPoint(numeric,scope,q.witness)),{natural,q}=__phase')
 })
}else throw new Error('observe|pool|combo required')
console.log(JSON.stringify({researchOnly:true,mode,manifest}))

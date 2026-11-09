// Research-only policy changes and call-site profiles in a disposable frozen tree.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import ts from 'typescript'
if(process.platform!=='linux'||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1')throw new Error('disposable Linux required')
const manifest:any[]=[],hash=(s:string)=>createHash('sha256').update(s).digest('hex')
const replace=(s:string,a:string,b:string)=>{if(s.split(a).length!==2)throw new Error('nonunique T12 anchor: '+a);return s.replace(a,b)}
const save=(file:string,change:(s:string)=>string)=>{const before=readFileSync(file,'utf8'),after=change(before);writeFileSync(file,after);manifest.push({file,before:hash(before),after:hash(after)})}
save('core/count-cases.ts',s=>{
 s="import {fallbackEnd as __cap} from '../research/track-m/section15-control.ts'\n"+s
 s=replace(s,'for(let round=0;!tree&&round<6&&clock()<caseEnd&&!pastWall();round++){','const __fallbackEnd=__cap(caseEnd)\n      for(let round=0;!tree&&round<6&&clock()<__fallbackEnd&&!pastWall();round++){\n       const __round=__d.begin(\'action-query-round\',{round});try{')
 s=replace(s,'Math.min(caseEnd,clock()+(options.queryMs??200))','Math.min(__fallbackEnd,clock()+(options.queryMs??200))')
 s=replace(s,"if(!('tree'in q)&&q.why===REFUTED&&q.core?.length&&q.core.length<=(options.coreLimit??Infinity)){","if(!('tree'in q)&&q.why===REFUTED&&q.core?.length&&q.core.length<=(options.coreLimit??Infinity)&&clock()<__fallbackEnd){")
 s=replace(s,'out=coreGrow(core,caseEnd)','out=coreGrow(core,__fallbackEnd)')
 s=replace(s,'at=next;if(!rebuild())return undefined\n      }','at=next;if(!rebuild())return undefined\n       }finally{__d.end(__round)}\n      }')
 s=replace(s,'if(!tree&&clock()<caseEnd&&!pastWall()){','if(!tree&&clock()<__fallbackEnd&&!pastWall()){')
 s=replace(s,'until:caseEnd,units:options.units','until:__fallbackEnd,units:options.units')
 s=replace(s,'try{return grow(g,new Map(),{nodes:0,until:end,units:options.units})','try{return grow(g,new Map(),{nodes:0,until:__cap(end),units:options.units})')
 // The captured op must receive its ordinary second-pass fallback too.
 s=replace(s,'__s.finish(records.at(-1),{goal,packet,at,cert,path:new Map(path)})','if(records.at(-1))__s.finish(records.at(-1),{goal,packet,at,cert,path:new Map(path)})')
 s=replace(s,'for(const [j,i] of missing.entries()){','for(const [j,i] of missing.entries()){\n      if(__s.mode===\'run\'&&cuts[i]!==__s.op)continue')
 s=replace(s,'const out=grow(part,new Map(),{nodes:0,until:end,units:options.units})','const out=grow(part,new Map(),{nodes:0,until:__cap(end),units:options.units})')
 s=replace(s,'    if(records.some(r=>!r))return undefined',"    if(__s.mode==='run')__s.finish(records[cuts.indexOf(__s.op)],{goal,packet,at,cert,path:new Map(path)})\n    if(records.some(r=>!r))return undefined")
 return s
})
save('core/count-recovery/guard-cases.ts',s=>"import {fallbackEnd as __cap} from '../../research/track-m/section15-control.ts'\nimport {diagnostic as __d} from '../../research/track-m/section10-diagnostic.ts'\n"+replace(s,'until:end,units:false','until:__cap(end),units:false'))
save('core/count-recovery/derivability-closure.ts',s=>{
 s="import {numericPhase as __numeric,classSelector as __classes} from '../../research/track-m/section15-control.ts'\n"+s
 s=replace(s,' const pool=cert.insts.flatMap',' const __selectClass=__classes(m,ds,cert,memberHints)\n const pool=cert.insts.flatMap')
 s=replace(s,'const indices=[...pending],baseGoal=numericFor()','const indices=__selectClass([...pending],scope),baseGoal=numericFor()')
 const line=s.split('\n').find(l=>l.includes('rounds++;const available=')&&l.includes('natural='));if(!line)throw new Error('numeric phase line missing')
 const split=line.indexOf(',natural='),expr=line.slice(split+9),marker=',q=natural?{tree:natural}:';const at=expr.indexOf(marker);if(at<0)throw new Error('numeric marker missing')
 const natural=expr.slice(0,at),model=expr.slice(at+marker.length)
 s=replace(s,line,line.slice(0,split)+`,__phase=__numeric(()=>${model},()=>${natural},q=>!!validPoint(numeric,scope,q.witness)),{natural,q}=__phase`)
 return s
})
// Attribute every expensive action/guard call and every fallback grow separately.
for(const file of ['core/count-cases.ts','core/count-recovery/guard-cases.ts'])save(file,s=>{
 const ast=ts.createSourceFile(file,s,ts.ScriptTarget.Latest,true),edits:{at:number,text:string}[]=[],names=new Set(['grow','coreGrow','seq','fieldCase','guardCases','selectedCase','rebuild','build','modelInstances','independentCountInstances','seedCountWitnessFlags','widen','transportConditionalProof','collectConditionalCertificate','checkMC','rowsAt','refuteFast','frameLemmas','fieldBoundLemmas','solve'])
 const walk=(n:ts.Node)=>{if(ts.isCallExpression(n)&&ts.isIdentifier(n.expression)&&names.has(n.expression.text)){const line=ast.getLineAndCharacterOfPosition(n.getStart(ast)).line+1,site=`${file}:${line}:${n.expression.text}`;edits.push({at:n.getStart(ast),text:`__d.run('action-site',{site:${JSON.stringify(site)},fn:${JSON.stringify(n.expression.text)}},()=>`},{at:n.end,text:')'})}ts.forEachChild(n,walk)};walk(ast)
 for(const e of edits.sort((a,b)=>b.at-a.at))s=s.slice(0,e.at)+e.text+s.slice(e.at);return s
})
console.log(JSON.stringify({researchOnly:true,manifest}))

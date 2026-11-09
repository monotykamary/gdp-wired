// Observation-only op selection and helper cost frames in a disposable replay.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux copy required')
const changes:any[]=[]
const change=(p:string,f:(s:string)=>string)=>{const before=readFileSync(p,'utf8'),after=f(before);writeFileSync(p,after);changes.push({path:p,before:createHash('sha256').update(before).digest('hex'),after:createHash('sha256').update(after).digest('hex')})}
const replace=(s:string,a:string,b:string)=>{if(s.split(a).length!==2)throw Error('nonunique op hook: '+a);return s.replace(a,b)}
change('core/count-cases.ts',s=>{
 s="import {shardControl as __s} from '../research/track-m/section13-control.ts'\nimport {lemmaRecorder as __l} from '../research/track-m/section18-recorder.ts'\n"+s
 s=replace(s,'  let goal:Goal={...root,name:packet.goal.name}','  let goal:Goal={...root,name:packet.goal.name}\n  __l.root(goal)')
 s=replace(s,'      branches.push({prefix,path:new Map(path),root,tails})',`      branches.push({prefix,path:new Map(path),root,tails})
      if(__s.mode==='run'&&value!==__s.op){records.push(undefined);for(const v of tails)path.delete(canon(splitAt(v)));if(split){path.set(canon(split),{lin:split,holds:false});conditions.push({op:'not',x:cut!})}continue}`)
 s=replace(s,'      records.push(tree&&source?{goal:source,tree,path:new Map(path),indices,...(from?{from}:{})}:undefined)',"      records.push(tree&&source?{goal:source,tree,path:new Map(path),indices,...(from?{from}:{})}:undefined)\n      if(records.at(-1))__s.finish(records.at(-1),{})")
 s=replace(s,'    for(const [j,i] of missing.entries()){',"    for(const [j,i] of missing.entries()){\n      if(__s.mode==='run'&&cuts[i]!==__s.op)continue\n      __l.phase='retry'")
 return replace(s,'    if(records.some(r=>!r))return undefined',"    __s.finish(records[cuts.indexOf(__s.op)],{})\n    if(records.some(r=>!r))return undefined")
})
const pre="import {lemmaRecorder as __l} from '../../research/track-m/section18-recorder.ts'\n"
change('core/count-recovery/field-bound-lemmas.ts',s=>pre+replace(replace(s,"(...args)=>wallTree('proposal-control',()=>{","(...args)=>__l.helper('field',args,()=>wallTree('proposal-control',()=>{"), '})\nfunction fieldBoundLemmasImpl','}))\nfunction fieldBoundLemmasImpl'))
change('core/count-recovery/frame-lemmas.ts',s=>pre+replace(s,"(...args)=>wallTree('proposal-control',()=>frameLemmasImpl(...args))","(...args)=>__l.helper('frame',args,()=>wallTree('proposal-control',()=>frameLemmasImpl(...args)))"))
change('core/count-recovery/conditional-proof.ts',s=>pre+replace(s,'  marked.set(tree, {goal, lemmas})','  marked.set(tree, {goal, lemmas});__l.noteMark(tree,{goal,lemmas})'))
console.log(JSON.stringify({observationOnly:true,changes}))

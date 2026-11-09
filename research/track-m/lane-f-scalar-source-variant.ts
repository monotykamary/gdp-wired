// Disposable weakening-only scalar-context projection before the source query.
import {readFileSync,writeFileSync,renameSync} from 'node:fs'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux required')
const path='core/count-recovery/derivability-closure.ts',source=readFileSync(path,'utf8')
const before='q=modelSequence(path)(part,queryLimit)'
const after=`q=(():ReturnType<ReturnType<typeof modelSequence>>=>{
   const names=new Set<string>();walkLive(h,path,(o:any)=>{if(o.op==='var')names.add(o.name)})
   const last=part.hyps.at(-1)!,seed={name:part.name,hyps:part.hyps.slice(-2)},projected=sourceScalarContext(part,seed,names,path)
   const hint={...projected,hyps:[...projected.hyps.filter(c=>c!==last),last]}
   const positions=hint.hyps.map(c=>part.hyps.findIndex(h=>h===c||JSON.stringify(h)===JSON.stringify(c)))
   if(positions.some(i=>i<0))return modelSequence(path)(part,queryLimit)
   const out=modelSequence(path)(hint,queryLimit)
   trace.push({stage:'closure-scalar-projection',index,hyps:hint.hyps.length,outcome:'tree'in out?'tree':out.stuck,core:out.core?.length})
   if('tree'in out){const tree=widen(hint,part,out.tree,{},path,path);return tree?{...out,tree}:{stuck:'unknown',path,why:'scalar projection transport'}}
   if(out.why===REFUTED)return {...out,core:out.core?.map(i=>positions[i]!)}
   return clock()<queryLimit?modelSequence(path)(part,queryLimit):out
  })()`
if(source.split(before).length!==2||!source.includes('{piecesAt,walkLive}'))throw Error('source projection anchors changed')
writeFileSync(path+'.tmp',source.replace('{piecesAt,walkLive}','{piecesAt,sourceScalarContext,walkLive}').replace(before,after));renameSync(path+'.tmp',path)

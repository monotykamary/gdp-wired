// Research-only model-demanded source projection; every positive tree is widened.
import {readFileSync,writeFileSync,renameSync} from 'node:fs'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux required')
const file='core/count-recovery/derivability-closure.ts',source=readFileSync(file,'utf8')
const old='q=modelSequence(path)(part,queryLimit)',next=`q=(()=>{
   const positions=[part.hyps.length-2,part.hyps.length-1],included=new Set(positions),sequence=modelSequence(path)
   for(let round=0;round<8&&clock()<queryLimit;round++){
    const small={...part,hyps:positions.map(i=>part.hyps[i]!)},out=sequence(small,queryLimit)
    trace.push({stage:'closure-source-projection',index,round,hyps:small.hyps.length,outcome:'tree'in out?'tree':out.stuck})
    if('tree'in out){const tree=widen(small,part,out.tree,{},path,path);return tree?{...out,tree}:{stuck:'unknown' as const,path,why:'projection transport'}}
    if(out.why===REFUTED)return {...out,core:out.core?.map(i=>positions[i]!)}
    if(out.stuck!=='sat'||!out.witness)return out
    if(validPoint(part,path,out.witness))return out
    const model={...out.witness};walkLive(part.hyps,path,(o:any)=>{if(o.op==='var'&&!Object.hasOwn(model,o.name))model[o.name]=0})
    const next=brokenOf(part)(model).find(i=>!included.has(i))
    if(next===undefined)break
    positions.push(next);included.add(next)
   }
   return modelSequence(path)(part,queryLimit)
  })()`
if(source.split(old).length!==2)throw Error('source demand anchor changed')
writeFileSync(file+'.tmp',source.replace(old,next));renameSync(file+'.tmp',file)

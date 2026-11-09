// Disposable scheduling experiment only; no law, budget, or checker is replaced.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
export type EarlyMode='early'|'row-first'
export function installEarly(source:string,mode:EarlyMode):string{
 if(mode!=='early'&&mode!=='row-first')throw Error('unknown early-completion mode')
 const start='    let countCompleted = false\n'
 const stop='    let decideStep = decisions.get(id)'
 const anchor='    let built = build()'
 if(source.split(start).length!==2||source.split(stop).length!==2||source.split(anchor).length!==2)throw Error('completion anchors changed')
 const a=source.indexOf(start),b=source.indexOf(stop,a),block=source.slice(a,b)
 if(!block.includes('completeCountLawInstances(modelLaws, at, ts,')||!block.endsWith('    }\n'))throw Error('unexpected completion block')
 let moved=block
 if(mode==='row-first')moved=moved.replace('      const completion = completeCountLawInstances(modelLaws, at, ts,',`      const formal = [...law.forall ? [law.forall] : [], ...law.keys ?? []]
      const rowNames = new Set([...reads(law.holds, mp => !isCount(mp)).values()].flatMap(([, key]) => key.op === 'var' ? [key.name] : []))
      const rows = formal.flatMap((name, i) => rowNames.has(name) ? [ts[i]!] : [])
      const completionTerms = reads(law.holds, isCount).size ? ts : [...rows, ...keyed, ...ts]
      const completion = completeCountLawInstances(modelLaws, at, completionTerms,`)
 return source.slice(0,a).concat(source.slice(b)).replace(anchor,moved+'    if (pass) completeCounts()\n'+anchor)
}
if(import.meta.main){
 if(process.env.LAB_DISPOSABLE!=='1')throw Error('LAB_DISPOSABLE=1 required')
 const mode=process.argv[2] as EarlyMode,file='core/counts.ts',source=readFileSync(file,'utf8'),next=installEarly(source,mode)
 writeFileSync(file,next)
 const sha=(s:string)=>createHash('sha256').update(s).digest('hex')
 console.log(JSON.stringify({experimental:true,mode,before:sha(source),after:sha(next),maxTerms:4,maxTuples:48,addedLaws:0,kernelChanged:false}))
}

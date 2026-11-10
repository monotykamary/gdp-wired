// Research only: match the census's conditional STEP and no-share boundary.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux copy required')
const path='core/counts.ts',before=readFileSync(path,'utf8')
let source=before
const old="const obligations = (i: Instances) => ptime('encode', () => countedObligations(m, ls, {[law.name]: i}, ls.indexOf(law)))"
if(source.split(old).length!==2)throw Error('non-unique obligation anchor')
source=source.replace(old,old.slice(0,-1)+".filter(({goal}) => goal.name.endsWith('@step')))")
const contexts=source.split('\n').filter(line=>line.trim().startsWith('const contexts = '))
if(contexts.length!==1)throw Error('non-unique context anchor')
source=source.replace(contexts[0]!,"      const contexts: {local: Law[], fraction: number, kind: string}[] = [] // research: no source-subset probes")
writeFileSync(path,source)
const hash=(s:string)=>createHash('sha256').update(s).digest('hex')
console.log(JSON.stringify({variant:'operation-step-no-share',path,before:hash(before),after:hash(source),edits:2,kernelChanged:false}))

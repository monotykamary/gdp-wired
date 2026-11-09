// Disposable-only diagnostic: production closure source is never edited here.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
if(process.env.LAB_DISPOSABLE!=='1')throw Error('LAB_DISPOSABLE=1 required')
const path='core/count-recovery/derivability-closure.ts'
let text=readFileSync(path,'utf8')
if(createHash('sha256').update(text).digest('hex')!=='dd311dd7188db859bdd74c7aaa3af2da4f572226030a68401649a4512f6d4ed2')throw Error('unexpected closure parent')
function replace(old:string,next:string){if(text.split(old).length!==2)throw Error('nonunique patch anchor');text=text.replace(old,next)}
replace("import {countsForReads} from '../count-facts.ts'","import {countsForReads} from '../count-facts.ts'\nimport {fieldCountDemand} from './field-count-demand.ts'")
replace(" if(wanted.size<2||!cert.insts.some(q=>q.unit===0&&q.terms.length>=3)"," if(wanted.size<2){const demand=fieldCountDemand(ds,cert,options.claim);for(const id of demand)wanted.add(id);if(demand.size)trace.push({stage:'field-count-demand',reads:[...demand]})}\n if(wanted.size<2||!cert.insts.some(q=>q.unit===0&&q.terms.length>=3)")
writeFileSync(path,text)
for(const name of ['field-count-demand.ts','field-count-demand.test.ts'])writeFileSync('core/count-recovery/'+name,readFileSync('row-field-demand/'+name+'.txt'))
writeFileSync('core/count-recovery/field-demand.integration.test.ts',readFileSync('row-field-demand/field-demand.integration.test.txt'))
console.log(JSON.stringify({experiment:'field-count-demand',closureSha256:createHash('sha256').update(text).digest('hex')}))

// Isolate Section 15.2 in a disposable replay; no switch ships in production.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.env.LAB_DISPOSABLE!=='1')throw Error('disposable copy required')
const mode=process.argv[2];if(!['before','after'].includes(mode!))throw Error('before|after required')
if(mode==='before'){
 const p='core/counts.ts',s=readFileSync(p,'utf8'),needle='if (completeCounts())';if(s.split(needle).length!==3)throw Error('completion anchors changed')
 writeFileSync(p,s.replaceAll(needle,'if (false && completeCounts())'))
}

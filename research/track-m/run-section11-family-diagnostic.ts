import {join} from 'node:path'
import {diagnostic as d} from './section10-diagnostic.ts'
import {analyzeSection10} from './section10-replay-diagnostic.ts'
const output=process.env.DIAG_OUTPUT,revision=process.env.TRACK_M_CANDIDATE
if(!output||!revision)throw new Error('DIAG_OUTPUT and TRACK_M_CANDIDATE required')
const records:any[]=[],log=console.log.bind(console)
console.log=(...args:unknown[])=>{log(...args);if(typeof args[0]!=='string')return;let r:any;try{r=JSON.parse(args[0])}catch{return}if(r.mode==='family'&&!r.checked)records.push({...d.dump(),captures:[...d.captures]})}
try{await import('./profile-family.ts')}finally{console.log=log}
for(const r of records){const name=r.label.startsWith('Inv2973')?'overlap':r.label.startsWith('Inv*')?'star':r.label.replace(/[^A-Za-z0-9]+/g,'-');analyzeSection10(join(output,name+'-full.json'),r,revision)}

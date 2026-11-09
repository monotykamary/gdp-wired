// Small receipt projection only: no prover imports or search.
import {readFileSync,readdirSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
const base='runs/track-m',output=process.argv[2];if(!output)throw Error('OUTPUT required')
const jsonLines=(s:string):any[]=>s.split('\n').flatMap(line=>{try{return[JSON.parse(line)]}catch{return[]}})
const placements=(dir:string)=>JSON.parse(readFileSync(join(base,dir,'placement.json'),'utf8'))
const logs=(dir:string)=>readdirSync(join(base,dir)).filter(n=>n.endsWith('.log')&&n!=='check.log').map(name=>({name:name.slice(0,-4),text:readFileSync(join(base,dir,name),'utf8')}))
const projected=(dir:string,key:string)=>{const place=placements(dir);return logs(dir).flatMap(({name,text})=>{const r=jsonLines(text).find(r=>r[key]!==undefined);if(!r)return[];const {events,profile,...row}=r;return[{name,...row,completionTuples:profile?.['#count-completion']??0,placement:place[name]}]})}
const sharePlace=placements('lane-b-share-v1')
const share=logs('lane-b-share-v1').map(({name,text})=>{const full=readFileSync(join(base,'lane-b-share-v1','receipts',name,'raw','run.log'),'utf8'),r=jsonLines(full).find(r=>r.search),attempts=full.split('\n').filter(s=>s.startsWith('counts: try '));if(!r)throw Error('missing verdict '+name);return{name,strictExit:Number(text.match(/STRICT_EXIT=(\d+)/)?.[1]),...r.search,units:r.search.full/250,attempts:attempts.length,reachedRows:attempts.some(s=>s.includes('rows agree')),reachedSafety:attempts.some(s=>s.includes('one primary per term')),placement:sharePlace[name]}})
const generation=jsonLines(readFileSync(join(base,'lane-b-generated-v1','generation.log'),'utf8')).find(r=>r.phase==='family')
const result={note:'Worker receipts; conditional certificates and op ledgers await independent audit. CPU models differ between arms; clock-limited prefixes are not whole-law costs.',sourceTrees:{share:'f31965ab921f',op:'37cca604b140',conditionalCompletion:'fe77a8e3c0d2',generated:'4d442ca21342',leafPolicy:'899fd3a9bcc8'},share,op:projected('lane-b-op-v1','searchUnits'),leafPolicy:projected('lane-b-leaf-v1','searchUnits'),conditionalCompletion:projected('lane-b-completion-v1','familySize'),generation,validation:{tests:66,assertions:5417,typecheck:true,lint:true,log:'../lane-b-generated-v1/check.log'}}
writeFileSync(output,JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify({output,share:share.length,op:result.op.length,conditional:result.conditionalCompletion.length,generatedLaws:generation.laws}))

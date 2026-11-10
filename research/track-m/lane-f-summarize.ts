// Iteration-only receipt reader. This cannot emit GATE GREEN.
import {readFileSync,writeFileSync,existsSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
const [dir]=process.argv.slice(2);if(!dir)throw Error('BATCH required')
const placement=JSON.parse(readFileSync(join(dir,'placement.json'),'utf8'))
const rows=readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\n').map(line=>line.split('\t'))
const result=rows.map(([name,exit,seconds,backend])=>{
 const file=join(dir,name+'.log'),text=existsSync(file)?readFileSync(file,'utf8'):'',sides:any[]=[];let active:any
 for(const line of text.split('\n')){
  if(line.startsWith('LANE_F_BEGIN ')){const [,kind,tag,op,side]=line.split(' ');active={kind,tag,op:Number(op),side,source:[]};sides.push(active)}
  if(active&&/^[a-f0-9]{64}  core\//.test(line))active.source.push(line)
  if(active&&line.startsWith('{')){try{const r=JSON.parse(line);if(typeof r.checked==='boolean'&&(r.searchUnits!==undefined||r.units!==undefined))active.result=r}catch{}}
  if(line.startsWith('LANE_F_END '))active=undefined
 }
 const before=sides.filter(s=>s.side==='before'),after=sides.filter(s=>s.side==='after'),a=before[0]?.result,b=after[0]?.result
 const complete=Number(exit)===0&&before.length===1&&after.length===1&&!!a&&!!b
 const frozenSame=!!a?.packetSha256&&a.packetSha256===b?.packetSha256
 return {name,exit:Number(exit),seconds:Number(seconds),backend,placement:placement[name!],logSha256:createHash('sha256').update(text).digest('hex'),complete,frozenSame,sides,checkedLost:complete&&a.checked&&!b.checked,searchDelta:complete?b.searchUnits-a.searchUnits:null,wallDelta:complete?(b.wallMs??b.searchWallMs)-(a.wallMs??a.searchWallMs):null}
})
const report={iterationOnly:true,gateGreen:false,rows:result,complete:result.every(r=>r.complete),lost:result.filter(r=>r.checkedLost).map(r=>r.name)}
writeFileSync(join(dir,'lane-f-summary.json'),JSON.stringify(report,null,2)+'\n')
console.log(JSON.stringify({iterationOnly:true,complete:report.complete,lost:report.lost,rows:result.map(({name,complete,checkedLost,searchDelta,wallDelta})=>({name,complete,checkedLost,searchDelta,wallDelta}))},null,2))

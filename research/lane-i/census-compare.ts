import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
type RecordRow = {id:string,count:number,canonical:string[],names:string[],wallMs:number,phases:Record<string,number>}
const [id,repeat,...paths]=process.argv.slice(2)
const rows=paths.map(path=>{
 const text=readFileSync(path!,'utf8'), marks=[...text.matchAll(/T13_DATA_GZIP_BASE64 (\S+)/g)]
 if(marks.length!==1)throw Error(`${path}: receipt cardinality`)
 const data=JSON.parse(gunzipSync(Buffer.from(marks[0]![1]!,'base64')).toString()) as {queries:number,records:RecordRow[]}
 if(data.queries!==0||data.records.length!==1||data.records[0]!.id!==id)throw Error(`${path}: wrong roster or proof queries`)
 return data.records[0]!
})
if(rows.length!==2)throw Error('expected pair')
const digest=(row:RecordRow)=>createHash('sha256').update(JSON.stringify(row.canonical)).digest('hex')
const [base,candidate]=rows as [RecordRow,RecordRow]
const identical=JSON.stringify(base.canonical)===JSON.stringify(candidate.canonical)
console.log('LANE_I_CENSUS '+JSON.stringify({id,repeat:Number(repeat),identical,base:{count:base.count,hash:digest(base),wallMs:base.wallMs,phases:base.phases},candidate:{count:candidate.count,hash:digest(candidate),wallMs:candidate.wallMs,phases:candidate.phases},...(id==='mldr'?{names:candidate.names}: {})}))

import {readFileSync} from 'node:fs'
const file=process.argv[2]
if(!file)throw Error('log required')
for(const line of readFileSync(file,'utf8').split('\n'))if(line.startsWith('STRATEGY_MERGE_CONFLICT ')){
 const row=JSON.parse(line.slice('STRATEGY_MERGE_CONFLICT '.length))
 if(process.argv[3]&&row.path!==process.argv[3])continue
 if(process.argv[4]==='head'){console.log(row.text.split('\n').slice(0,65).join('\n'));continue}
 const hunks=[...row.text.matchAll(/<<<<<<<[^\n]*\n[\s\S]*?=======[^\n]*\n[\s\S]*?>>>>>>>[^\n]*/g)].map(m=>m[0])
 console.log(JSON.stringify({path:row.path,hunks}))
}

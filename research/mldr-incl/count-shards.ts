import {readFileSync,readdirSync} from 'node:fs'
const dir=process.argv[2]!,rows=readdirSync(dir).filter(n=>/^shard-\d+\.log$/.test(n)).sort().map(file=>{const text=readFileSync(`${dir}/${file}`,'utf8'),sum=(word:string)=>[...text.matchAll(new RegExp(`^\\s*(\\d+) ${word}\\s*$`,'gm'))].reduce((n,m)=>n+Number(m[1]),0);return {file,pass:sum('pass'),fail:sum('fail'),skip:sum('skip')}})
console.log(JSON.stringify({rows,total:rows.reduce((a,r)=>({pass:a.pass+r.pass,fail:a.fail+r.fail,skip:a.skip+r.skip}),{pass:0,fail:0,skip:0})}))

// Parse timing receipts only; never runs a prover or changes source admission.
import {readFileSync,readdirSync,statSync} from 'node:fs'
import {join} from 'node:path'
type Sample={pair:string,phase:string,name:string,sample:number,wallMs:number,kernelProven:boolean}
const samples:Sample[]=[]
function visit(path:string):void{
 for(const file of readdirSync(path)){
  const p=join(path,file)
  if(statSync(p).isDirectory()){if(!file.endsWith('.files'))visit(p);continue}
  if(file!=='out'&&!file.endsWith('.log'))continue
  for(const line of readFileSync(p,'utf8').split('\n')){
   if(!line.startsWith('{'))continue
   let v:Sample;try{v=JSON.parse(line)}catch{continue}
   if(typeof v.wallMs==='number'&&v.sample>=0&&typeof v.pair==='string')samples.push(v)
  }
 }
}
for(const path of process.argv.slice(2))visit(path)
const median=(xs:number[]):number=>{const a=xs.toSorted((a,b)=>a-b),i=Math.floor(a.length/2);return a.length%2?a[i]!:((a[i-1]!+a[i]!)/2)}
for(const pair of [...new Set(samples.map(s=>s.pair))])for(const name of [...new Set(samples.filter(s=>s.pair===pair).map(s=>s.name))]){
 const s=samples.filter(s=>s.pair===pair&&s.name===name),b=s.filter(s=>s.phase==='before'),a=s.filter(s=>s.phase==='after')
 if(b.length!==20||a.length!==20||s.some(x=>!x.kernelProven))throw Error('invalid sample set '+pair+name)
 const bm=median(b.map(s=>s.wallMs)),am=median(a.map(s=>s.wallMs))
 console.log(JSON.stringify({pair,name,beforeN:b.length,afterN:a.length,beforeMedian:bm,afterMedian:am,percent:(am/bm-1)*100}))
}

// Cold same-VM comparisons. Both arms call the ordinary score/protocol CLI.
import assert from 'node:assert/strict'
import {spawnSync} from 'node:child_process'
import {appendFileSync,readdirSync,readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {corpus} from '../realworld/corpus.ts'
import {protocols as duo} from '../protocols/models.ts'
import {protocols as ic3} from '../protocols/ic3syn/models.ts'

const [mode,a,b]=process.argv.slice(2)
assert.equal(process.version,'v24.22.1')
const real=corpus.flatMap(item=>item.laws.map((law,k)=>({suite:'realworld',id:item.id,k,name:law.name,cli:['research/realworld/score.ts','--one',item.id,String(k),'--ms','60000']})))
const proto=(suite,ps,script,skip)=>ps.map(p=>({suite,id:p.id,cli:[script,'--only',p.id,'--skip',skip,'--ms','60000']}))
const rows=[...real,...proto('duoai',duo,'research/protocols/run.ts','given,broken'),...proto('ic3syn',ic3,'research/protocols/ic3syn/run.ts','broken')]
assert.deepEqual([corpus.length,real.length,duo.length,ic3.length,rows.length],[86,467,10,29,506])
assert.equal(new Set(rows.map(row=>[row.suite,row.id,row.k].join('\t'))).size,506)
const flags=['--experimental-transform-types','--disable-warning=ExperimentalWarning']
const order=(i,reversed=false)=>(i%2!==0)!==reversed?['candidate','stock']:['stock','candidate']
if(mode==='jobs'){
  const n=Number(b); assert(Number.isInteger(n)&&n>0)
  writeFileSync(a,JSON.stringify(Array.from({length:n},(_,i)=>({name:`aggregate-pair-${String(i).padStart(2,'0')}`,cmd:`bash research/kernel-sums/paired.sh run ${i} ${n}`,timeout:2500,cpu:1,memory:6144,required_agent_capabilities:{output_files_protocol:1}})),null,2))
  writeFileSync(`${a}.manifest.json`,JSON.stringify(rows.map(({cli:_cli,...row},i)=>({i,...row})),null,2))
}else if(mode==='run'||mode==='reverse'||mode==='row'){
  const stock=process.env.KERNEL_SUMS_STOCK,out=process.env.SUPERCOMPUTER_OUTPUT_DIR
  assert(stock&&out)
  const indices=mode==='reverse'||mode==='row'?[Number(a)]:rows.flatMap((_,i)=>i%Number(b)===Number(a)?[i]:[])
  for(const i of indices){
    const row=rows[i];assert(row)
    const ordered=order(i,mode==='reverse'), pair=[]
    for(const arm of ordered){
      const t=performance.now()
      const child=spawnSync('timeout',['--signal=TERM','-k','5','70',process.execPath,...flags,...row.cli],{
        cwd:arm==='stock'?stock:process.cwd(),encoding:'utf8',maxBuffer:16*1024*1024,env:process.env})
      let data
      try{data=JSON.parse(child.stdout.trim().split('\n').at(-1))}catch{/* classified below */}
      const outcome=child.status===124||child.status===137?'timeout':child.status!==0||data?.error?'error':data?.outcome??data?.search?.verdict??'error'
      if(outcome==='error'||outcome==='timeout')appendFileSync(join(out,'failures.ndjson'),JSON.stringify({i,arm,outcome,exit:child.status,stdout:child.stdout?.slice(-3000),stderr:child.stderr?.slice(-3000)})+'\n')
      pair.push({arm,outcome,exit:child.status,wallMs:Math.round(performance.now()-t),ms:data?.ms??data?.search?.ms,work:data?.work,full:data?.full,goal:data?.goal})
    }
    const {cli:_cli,...id}=row
    appendFileSync(join(out,'pairs.ndjson'),JSON.stringify({i,...id,order:ordered,pair,node:process.version})+'\n')
  }
}else if(mode==='compare'){
  const received=readdirSync(a).filter(x=>x.endsWith('.files')).flatMap(f=>readFileSync(join(a,f,'pairs.ndjson'),'utf8').trim().split('\n').filter(Boolean).map(JSON.parse))
  const seen=new Set(), changes=[], losses=[], errors=[], summary={}
  for(const z of received){
    const row=rows[z.i];assert(row&&!seen.has(z.i));seen.add(z.i)
    assert.equal(z.id,row.id);assert.equal(z.k,row.k);assert.equal(z.node,'v24.22.1');assert.deepEqual(z.order,order(z.i))
    const s=z.pair.find(p=>p.arm==='stock'),c=z.pair.find(p=>p.arm==='candidate');assert(s&&c&&z.pair.length===2)
    const x=summary[z.suite]??={rows:0,stock:{},candidate:{}};x.rows++
    x.stock[s.outcome]=(x.stock[s.outcome]??0)+1;x.candidate[c.outcome]=(x.candidate[c.outcome]??0)+1
    if(s.outcome!==c.outcome){changes.push(z);if(['proven','refuted'].includes(s.outcome))losses.push(z)}
    if([s,c].some(p=>p.outcome==='error'))errors.push(z)
  }
  assert.equal(seen.size,rows.length)
  writeFileSync(b,JSON.stringify({summary,changes,losses,errors},null,2)+'\n')
}else throw Error(`unsupported paired mode ${mode}`)

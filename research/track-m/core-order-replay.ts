import {readFileSync} from 'node:fs'
import {type Goal,check} from '../../kernel/kernel.ts'
import {atPoint,clock,counted,fullRate,fullWork,grow,widen,withWall} from '../../kernel/prove.ts'
const rows=readFileSync(process.argv[2]!,'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l))
for(const row of rows)for(const item of row.cores??[]){
 if(process.env.LAB_CORE_CASE&&String(item.value)!==process.env.LAB_CORE_CASE)continue
 const goal:Goal=item.goal,n=goal.hyps.length
 for(const point of [false,true])for(const mode of ['same','reverse','last-first','inner-reverse','last-first-inner'].filter(m=>!process.env.LAB_ORDER_MODE||m===process.env.LAB_ORDER_MODE)){
  const h=goal.hyps,hyps=mode==='reverse'?[...h].reverse():mode==='last-first'?[h[n-1]!,...h.slice(0,-1)]:mode==='inner-reverse'?[...h.slice(0,-1).reverse(),h[n-1]!]:mode==='last-first-inner'?[h[n-1]!,...h.slice(0,-1).reverse()]:h
  const part={...goal,hyps},start=performance.now(),w=fullWork();atPoint.on=point
  const out=withWall(start+4000,()=>counted(fullRate,()=>grow(part,new Map(),{nodes:0,until:clock()+1000,units:process.env.LAB_NO_UNITS==='1'?false:undefined}),true))
  const tree=out&&'tree'in out?widen(part,goal,out.tree):undefined
  console.log(JSON.stringify({value:item.value,point,mode,outcome:out&&'tree'in out?'tree':out?.stuck,...(out&&'stuck'in out?{why:out.why,path:[...out.path.values()]}:{}),checked:!!tree&&check(goal,tree),counted:Math.round((fullWork()-w)/fullRate),wall:Math.round(performance.now()-start)}))
 }
}

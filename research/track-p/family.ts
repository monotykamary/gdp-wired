import {readFileSync} from 'node:fs'
import {type Law,type Machine,x} from '../../core/machine.ts'
import {candidateWork,prepareSupport,grammarPool,polaritySelection,sparseReadInstances,countedInstanceSources} from '../../core/count-support.ts'
import {type CountCert,type Instances,countedObligations,mcGoal,checkMC} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,grow,modelInstances,widen,withWall,withDeadline} from '../../kernel/prove.ts'
import {relevantGoals} from '../../core/relevance.ts'
const data: {machine:Machine,laws:Law[]}=JSON.parse(readFileSync(process.argv[2]!,'utf8'))
const indices=[2,3,4,7,9,10,11,13,14,17,33,45,61,64,66,70,71,73,74]
const laws=indices.map(i=>data.laws[i]!),m=data.machine,shard=Number(process.argv[3]??0),shards=Number(process.argv[4]??1),ms=Number(process.env.REPLAY_MS??1500)
for(let i=0;i<laws.length;i++){if(i%shards!==shard)continue;const law=laws[i]!
 for(const phase of ['init','step'])for(const mode of ['full','relevant']){
  const start=performance.now(),work=fullWork();let outcome='unknown',why='',size=0,round=0,checked=false
  withWall(performance.now()+ms*2,()=>counted(fullRate,()=>withDeadline(clock()+ms,()=>{
   const until=clock()+ms,budget=candidateWork(),terms=[...(law.forall?[x(law.forall+'#')]:[]),...(law.keys??[]).map(x),...m.inputs.map(x)]
   const initial:Instances=Object.fromEntries(Object.entries(m.step.flags??{}).filter(([,q])=>q.op==='all'&&!q.keys?.length).map(([f])=>['?'+f,terms]))
   const prep=prepareSupport(m,laws,law,initial,1,budget);let at=prep.at,seedCount=prep.seedCount
   const sources=countedInstanceSources(m,laws)
   let cachedPool:ReturnType<typeof grammarPool>|undefined,cachedKey=''
   for(;round<6&&clock()<until;round++){
    const {goal,decls}=countedObligations(m,laws,{[law.name]:at},i)[phase==='init'?0:1]!
    let c:Pick<CountCert,'reads'|'insts'|'picks'>={reads:[],insts:[]}
    if(phase==='step'){
     const key=JSON.stringify(Object.entries(at).filter(([name])=>sources.has(name)))
     const pool=cachedPool&&cachedKey===key?cachedPool:grammarPool(goal,decls,1000,budget)
     cachedPool=pool;cachedKey=key
     c=polaritySelection(goal,decls,pool,budget,prep.sourceMaps).pick
    }
    const gg=mcGoal(goal.hyps,decls,c);if(!gg){why='invalid count proposal';break};size=gg.hyps.length
    if(phase==='step'&&seedCount<64){const seed=sparseReadInstances(m,laws,law,at,gg,c,64-seedCount,goal.hyps.at(-1),decls,prep.sourceMaps,goal.hyps.slice(0,-1),budget);if(seed.added.length){at=seed.at;seedCount+=seed.added.length;continue}}
    let proof
    if(mode==='relevant')for(const part of relevantGoals(gg)){const q=grow(part,new Map(),{nodes:0,until:Math.min(until,clock()+ms/4)});if('tree'in q){proof=widen(part,gg,q.tree);if(proof)break}}
    const q=proof?{tree:proof}:grow(gg,new Map(),{nodes:0,until})
    if('tree'in q){outcome='tree';checked=checkMC(goal.hyps,decls,{...c,tree:q.tree});break}
    outcome=q.stuck;why=q.why??''
    const next=phase==='step'&&q.stuck==='sat'&&q.witness?modelInstances(m,laws,at,gg,q.witness):undefined
    if(!next)break;at=next
   }
  }),true))
  console.log(JSON.stringify({family:indices[i],name:law.name,phase,mode,outcome,checked,why,hyps:size,round,ms:Math.round(performance.now()-start),work:Math.round(fullWork()-work)}))
 }
}

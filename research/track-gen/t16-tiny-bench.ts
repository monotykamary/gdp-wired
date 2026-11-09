// Benchmark vocabulary stays here, never in the production generator.
// Historical sampler drops are independently replayed before constructing the
// survivor benchmark. A name in a captured log is not a drop certificate.
import {readFileSync} from 'node:fs'
import {mldr} from '../protocols/ic3syn/mldr.ts'
import {type Machine, type Law, type State, type Request, interpret} from '../../core/machine.ts'
import {tinyFiniteCandidates, type TinyFiniteStatistics} from '../../core/finite-tiny.ts'
import {finiteEvaluator} from '../../core/finite-houdini.ts'
import {withWall} from '../../kernel/prove.ts'
import {checkWall, WallExpired} from '../../core/wall.ts'
const capture = JSON.parse(readFileSync('tiny-data/0.json', 'utf8'))
const data = capture.beforeFinite, source = mldr().machine, m = data.machine as Machine
let family = [...data.caller, ...data.candidates] as Law[]
const run = interpret(source), evaluate = finiteEvaluator(m), protectedLaws = new Set<Law>(data.caller as Law[])
const extras: Law[] = [...m.facts??[], ...(m.pre?[{name:'machine precondition',holds:m.pre}]:[])]
const prior: string[] = []
withWall(performance.now()+5000,()=>{
  const rounds = [...new Set<number>(capture.finiteDrops.map((d: {round:number})=>d.round))].sort((a,b)=>a-b)
  for(const round of rounds){
    checkWall('historical finite round')
    const removed = new Set<string>()
    for(const drop of capture.finiteDrops.filter((d:{round:number})=>d.round===round)){
      checkWall('historical finite replay')
      const pre: State = {...drop.pre, maps:Object.fromEntries(Object.entries(drop.pre.maps as Record<string,[number,number][]>).map(([k,v])=>[k,new Map(v)]))}
      const request: Request = Object.fromEntries(Object.entries(drop.request).map(([k,v])=>[k,Array.isArray(v)?new Map(v as [number,number][]):v])) as Request
      const law=family.find(l=>l.name===drop.law.name)
      if(!law || protectedLaws.has(law) || ![...family,...extras].every(l=>evaluate(l,drop.params,pre)===true)) throw Error('historical full-family/pre/facts check failed: '+drop.law.name)
      const post=run.step(drop.params,pre,request)
      if(evaluate(law,drop.params,post)!==false) throw Error('historical interpreter/post check failed: '+law.name)
      removed.add(law.name); prior.push(law.name)
    }
    family=family.filter(l=>!removed.has(l.name))
  }
})
console.log('family',family.length,JSON.stringify({replayedDrops:prior,names:family.map(l=>l.name)}))
const params={size:3}, accepted:string[]=[], rejected:string[]=[], stats:TinyFiniteStatistics[]=[]
const started=performance.now(), end=started+Number(process.argv[2]??2000), maxRounds=family.length
let timedOut=false
try{withWall(end,()=>{
  for(let round=0;round<maxRounds;round++){
    checkWall('tiny certified survivor round')
    const current=family.slice(), required=[...current,...extras], removed=new Set<Law>()
    const row=tinyFiniteCandidates(source,m,current,params,(pre,request,violated)=>{
      const helpers=violated.filter(l=>!protectedLaws.has(l))
      if(!helpers.length) return true // stop proposals, never remove a caller
      if(!required.every(l=>evaluate(l,params,pre)===true)){rejected.push(helpers[0]!.name+': pre');return false}
      try{
        const post=run.step(params,pre,request), genuine=helpers.filter(l=>evaluate(l,params,post)===false)
        if(genuine.length!==helpers.length){rejected.push(helpers[0]!.name+': post');return false}
        for(const law of genuine){removed.add(law);if(!accepted.includes(law.name))accepted.push(law.name)}
        console.log('CTI',JSON.stringify({round,ms:performance.now()-started,laws:genuine.map(l=>l.name),pre:{scalars:pre.scalars,maps:Object.fromEntries(Object.entries(pre.maps).map(([k,v])=>[k,[...v]]))},request:Object.fromEntries(Object.entries(request).map(([k,v])=>[k,v instanceof Map?[...v]:v]))}))
        return true
      }catch(e){if(e instanceof WallExpired)throw e;rejected.push(helpers[0]!.name+': step '+String(e));return false}
    })
    stats.push(row);family=family.filter(l=>!removed.has(l))
    console.log('TINY_ROUND',JSON.stringify({round,removed:[...removed].map(l=>l.name),family:family.length,stats:row}))
    if(row.timedOut){timedOut=true;break}
    if(!removed.size)break
  }
})}catch(e){if(e instanceof WallExpired)timedOut=true;else throw e}
console.log('TINY_RESULT',JSON.stringify({stats,accepted,rejected,timedOut,family:family.length,wall:performance.now()-started}))
if(accepted.length<5)process.exitCode=1

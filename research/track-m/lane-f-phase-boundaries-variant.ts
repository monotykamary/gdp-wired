// Diagnostic-only entry/exit markers around work hidden between countsDump events.
import {readFileSync,writeFileSync,renameSync} from 'node:fs'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux required')
const file='core/counts.ts',source=readFileSync(file,'utf8')
const ptime="const ptime = <T>(k: string, f: () => T): T => { const t = performance.now(); try { checkWall(k); const out = f(); checkWall(k); return out } finally { cprof[k] = (cprof[k] ?? 0) + performance.now() - t } }"
const helper=`let phaseSerial=0
const phaseWatched=new Set(['mbqi','lazy','decide','focused','encode','build','rawBuild','finiteCompletion'])
const phaseBoundary=<T>(span:string,work:()=>T):T=>{
 if(!phaseWatched.has(span))return work()
 const id=++phaseSerial
 if(id>1024){if(id===1025)countsDump.on?.({phase:'boundary-limit',limit:1024});return work()}
 const emit=(edge:string)=>countsDump.on?.({phase:'boundary',span,id,edge,wall:performance.now(),units:clock(),rss:process.memoryUsage().rss})
 emit('enter');let returned=false
 try{const value=work();returned=true;return value}finally{emit(returned?'return':'throw')}
}
`
const changes:[string,string][]=[
 [ptime,helper+ptime.replace('=> { const t','=> phaseBoundary(k,()=>{ const t').replace(/ }$/,' })')],
 ['    const rawBuild = () => obligations(at).map','    const rawBuild = () => phaseBoundary(\'rawBuild\',()=>obligations(at).map'],
 ['    })\n    let lastSignature', '    }))\n    let lastSignature'],
 ['    const build = () => {','    const build = () => phaseBoundary(\'build\',()=>{'],
 ['      return built\n    }\n    // (the pool', '      return built\n    })\n    // (the pool'],
 ['const completion = (finite ??= finiteModelChecker(m))(ls, law, w, () => clock() >= attemptEnd)',"const completion = phaseBoundary('finiteCompletion',()=>(finite ??= finiteModelChecker(m))(ls, law, w, () => clock() >= attemptEnd))"],
]
let next=source
for(const [from,to]of changes){if(next.split(from).length!==2)throw Error('phase boundary anchor changed: '+from);next=next.replace(from,to)}
writeFileSync(file+'.tmp',next);renameSync(file+'.tmp',file)

// Append after phase-preload.ts; only observe existing cache counters.
import {resolve as resolveCachePath} from 'node:path'
const rowsObserver=await import(resolveCachePath('kernel/prover-rows.ts')).catch(()=>undefined)
const cacheLog=console.log.bind(console)
console.log=(...args:unknown[])=>{
 if(typeof args[0]==='string'&&args[0].startsWith('{')){
  try{const row=JSON.parse(args[0]);if(row.id&&row.search)console.error('LANE_I_CACHE '+JSON.stringify({stats:rowsObserver?.rowReuseStats,storage:rowsObserver?.rowReuseStorage(),memory:process.memoryUsage()}))}catch{/* ordinary output */}
 }
 cacheLog(...args)
}

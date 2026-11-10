// Observation-only preload for the original harness. No engine or budget edits.
const error=console.error.bind(console),log=console.log.bind(console)
let first=true
console.error=(...args:unknown[])=>{
 const text=typeof args[0]==='string'?args[0]:''
 if(text.startsWith('counts: candidates at '))error('LANE_I_TIMING '+JSON.stringify({event:'candidates',at:performance.now()}))
 if(first&&text.startsWith('counts: try ')){
  first=false
  const wall=/ wall (\d+) /.exec(text)
  error('LANE_I_TIMING '+JSON.stringify({event:'first-attempt-return',at:performance.now(),attemptWallMs:wall?Number(wall[1]):null}))
 }
 error(...args)
}
console.log=(...args:unknown[])=>{
 if(typeof args[0]==='string'&&args[0].startsWith('{')){
  let row: {id?:string,search?:{ms?:number}}|undefined
  try{row=JSON.parse(args[0]) as typeof row}catch{/* ordinary non-JSON output */}
  if(row?.id&&row.search?.ms!==undefined)error('LANE_I_TIMING '+JSON.stringify({event:'result',at:performance.now(),id:row.id,searchMs:row.search.ms}))
 }
 log(...args)
}

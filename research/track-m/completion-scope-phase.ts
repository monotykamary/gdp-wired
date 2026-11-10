// Observation only: preserve strict budgets and capture full candidate names/profile.
import {resolve} from 'node:path'
const {cprof, countsDump} = await import(resolve('core/counts.ts'))
const error = console.error.bind(console), log = console.log.bind(console)
const prior = countsDump.on
countsDump.on = (event: object) => {
  prior?.(event)
  if ('phase' in event && event.phase === 'candidates' && 'laws' in event && Array.isArray(event.laws)) error('LANE_I_PROFILE ' + JSON.stringify({event:'candidate-names', names:event.laws.map((law:{name:string})=>law.name)}))
}
let first = true
console.error = (...args: unknown[]) => {
  const text = typeof args[0] === 'string' ? args[0] : ''
  if (text.startsWith('counts: candidates at ')) error('LANE_I_PROFILE ' + JSON.stringify({event:'candidates',at:performance.now(),profile:{...cprof}}))
  if (first && text.startsWith('counts: try ')) {
    first = false
    const wall = / wall (\d+) /.exec(text)
    error('LANE_I_PROFILE ' + JSON.stringify({event:'first-attempt-return',at:performance.now(),attemptWallMs:wall?Number(wall[1]):null}))
  }
  error(...args)
}
console.log = (...args: unknown[]) => {
  if (typeof args[0] === 'string' && args[0].startsWith('{')) {
    try { const row = JSON.parse(args[0]); if(row.id && row.search) error('LANE_I_PROFILE '+JSON.stringify({event:'result',at:performance.now(),searchMs:row.search.ms,profile:{...cprof}})) } catch { /* ordinary output */ }
  }
  log(...args)
}

// Progress receipts outside every measured interval; no proof/search changes.
import {readFileSync,writeFileSync} from 'node:fs'
const file='research/track-m/run-phase-census.ts';let s=readFileSync(file,'utf8')
s=s.replace('  const start=performance.now(),before=fullWork()',"  console.error(JSON.stringify({progress:'law-start',side,law:law.name,at:performance.now()}))\n  const start=performance.now(),before=fullWork()")
s=s.replace('  // Do not check or traverse proof dependencies',"  console.error(JSON.stringify({progress:'law-end',side,law:law.name,wallMs,countedUnits,verdict}))\n  // Do not check or traverse proof dependencies")
s=s.replace('let auditWallMs=0',"console.error(JSON.stringify({progress:'audit-start',at:performance.now()}))\nlet auditWallMs=0")
writeFileSync(file,s)

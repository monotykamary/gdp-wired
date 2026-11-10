// Diagnostic: the first exact CLI call from the unchanged effect-pool test.
import {resolve} from 'node:path'
const {check}=await import(resolve('core/cli.ts'))
const started=performance.now(),result=await check([resolve('examples/effect-pool.ts')],{ms:30_000,propose:false})
console.log('EFFECT_CLI_RESULT '+JSON.stringify({ms:performance.now()-started,exit:result.exit,rules:result.rules.map((r:any)=>({entry:r.entry,ok:r.ok,notes:r.notes,laws:r.laws}))}))

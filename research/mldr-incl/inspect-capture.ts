import {readFileSync} from 'node:fs'
for(const file of process.argv.slice(2)){const d=JSON.parse(readFileSync(file,'utf8'));console.log(JSON.stringify({file,law:d.law,phase:d.phase,pass:d.pass,hyps:d.hyps?.length,generation:d.generation,reads:d.certificateRequest?.reads,instances:Object.fromEntries(Object.entries(d.instances??{}).map(([k,v])=>[k,(v as unknown[]).length]))}))}

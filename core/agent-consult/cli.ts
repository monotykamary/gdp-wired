#!/usr/bin/env node
import {serveStdio} from './session.ts'
// No tool/CLI flags accept roots or interpreters. Only trusted server startup environment configures roots.
process.exitCode=2
let settled=false,reported=false
const onUnsettled=(ev:string)=>{if(settled||reported)return;reported=true;process.exitCode=2;process.stderr.write(`gdp-wired: the check did not complete (${ev})\n`)}
process.on('beforeExit',()=>onUnsettled('beforeExit'))
process.on('exit',()=>onUnsettled('exit'))
if(process.argv.length>2){
  settled=true
  process.stderr.write('Usage: gdp-wired-agent-consult (stdio MCP; accepts no arguments)\n')
  process.exitCode=2
}else{
  try {
    const configured:unknown=JSON.parse(process.env.GDP_AGENT_CONSULT_ROOTS??'[]')
    if(!Array.isArray(configured)||!configured.every(p=>typeof p==='string'))throw Error('GDP_AGENT_CONSULT_ROOTS must be a JSON array of trusted absolute directories')
    await serveStdio({workspaceRoots:configured as string[]})
    settled=true
    if(process.exitCode===2)process.exitCode=0
  }catch(e){settled=true;process.stderr.write(String(e)+'\n');process.exitCode=1}
}

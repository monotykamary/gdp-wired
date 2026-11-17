#!/usr/bin/env node
import {serveStdio} from './session.ts'
// No tool/CLI flags accept roots or interpreters. Only trusted server startup environment configures roots.
if(process.argv.length>2){
  process.stderr.write('Usage: gdp-wired-agent-consult (stdio MCP; accepts no arguments)\n')
  process.exitCode=2
}else{
  try {
    const configured:unknown=JSON.parse(process.env.GDP_AGENT_CONSULT_ROOTS??'[]')
    if(!Array.isArray(configured)||!configured.every(p=>typeof p==='string'))throw Error('GDP_AGENT_CONSULT_ROOTS must be a JSON array of trusted absolute directories')
    await serveStdio({workspaceRoots:configured as string[]})
  }catch(e){process.stderr.write(String(e)+'\n');process.exitCode=1}
}

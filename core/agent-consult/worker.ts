import {execute,failure} from './service.ts'
import {wireJSON} from './protocol.ts'
process.exitCode=2
let settled=false,reported=false
const onUnsettled=(ev:string)=>{if(settled||reported)return;reported=true;process.exitCode=2;process.stderr.write(`gdp-wired: the check did not complete (${ev})\n`)}
process.on('beforeExit',()=>onUnsettled('beforeExit'))
process.on('exit',()=>onUnsettled('exit'))
let data=''
try {
  for await(const chunk of process.stdin){data+=chunk.toString();if(Buffer.byteLength(data)>131072)throw Error('worker input exceeds128KiB')}
  const request=JSON.parse(data) as {tool:unknown,args:unknown,roots?:import('./workspace.ts').WorkspaceRoot[]}
  const value=request.tool==='check'?await (await import('./source-service.ts')).executeSource(request.args,request.roots??[]):execute(request.tool,request.args)
  process.stdout.write(wireJSON(value)+'\n')
  settled=true;process.exitCode=0
}catch(e){settled=true;process.stdout.write(wireJSON(failure('worker',e))+'\n');process.exitCode=1}

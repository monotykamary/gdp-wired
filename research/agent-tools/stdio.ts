// Legacy research entrypoint; delegates to the supported implementation.
import {createConsultation,serveStdio} from '../../core/agent-consult.ts'
const session=createConsultation()
export const handle=session.handle
if(import.meta.main)await serveStdio().catch(e=>{process.stderr.write(String(e)+'\n');process.exitCode=1})

/** Counted consultation; data-only by default. Explicit server roots opt into source execution.
 * Each session owns a bounded evidence registry and serial isolated workers.
 * close()/AbortSignal cancel work, never turn cancellation into a verdict.
 */
export {createConsultation,serveStdio} from './agent-consult/session.ts'
export {parseRequest,revision,inputSchema,toolNames,toolDescriptions,Refusal} from './agent-consult/protocol.ts'
export type {Tool,Unit,Budget,Request,Json} from './agent-consult/protocol.ts'
export type {ConsultationOptions} from './agent-consult/workspace.ts'

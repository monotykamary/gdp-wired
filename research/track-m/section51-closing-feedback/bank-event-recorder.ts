// Test-harness evidence only; no native meter, search or proof behavior lives here.
import {openSync,writeSync,closeSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {gzipSync} from 'node:zlib'
import {type WorkAdmissionEvent} from '../../../core/work-admission.ts'

export const MAX_BANK_BYTES=128*1024*1024
export type BankEventSummary=Readonly<{
 records:number,bytes:number,storedBytes:number,maxBytes:number,sha256:string,
 firstSequence:number,lastSequence:number
}>
type RecorderOptions={
 maxBytes?:number,flushBytes?:number,
 // Fault injection for this recorder's unit tests, never native proof hooks.
 compress?:(bytes:Buffer)=>Buffer,
 write?:(fd:number,bytes:Buffer,offset:number,length:number)=>number,
 close?:(fd:number)=>void
}
export function createBankEventRecorder(path:string,options:RecorderOptions={}){
 const {maxBytes=MAX_BANK_BYTES,flushBytes=256*1024,
  compress=(bytes:Buffer)=>gzipSync(bytes,{level:1}),write=writeSync,close=closeSync}=options
 if(!Number.isSafeInteger(maxBytes)||maxBytes<0||!Number.isSafeInteger(flushBytes)||flushBytes<=0)throw Error('invalid bank stream bounds')
 const fd=openSync(path,'wx'),hash=createHash('sha256')
 let records=0,bytes=0,storedBytes=0,buffer='',bufferBytes=0,firstSequence=0,lastSequence=0,depth=0
 let failed=false,failure:unknown,closed=false,summary:BankEventSummary|undefined
 const remember=(error:unknown)=>{if(!failed){failed=true;failure=error}}
 const checkFailure=()=>{if(failed)throw failure}
 const flush=()=>{
  if(!bufferBytes)return
  const data=compress(Buffer.from(buffer));let offset=0
  if(!Buffer.isBuffer(data)||!data.length)throw Error('bank stream compression produced no bytes')
  while(offset<data.length){
   const written=write(fd,data,offset,data.length-offset)
   if(!Number.isSafeInteger(written)||written<=0||written>data.length-offset)throw Error('bank stream short write')
   offset+=written
  }
  storedBytes+=data.length;buffer='';bufferBytes=0
 }
 const record=(event:WorkAdmissionEvent)=>{
  checkFailure()
  try{
   if(closed)throw Error('bank stream already finalized')
   if(!Number.isSafeInteger(event.sequence)||event.sequence<=0||
    (records?event.sequence!==lastSequence+1:event.kind!=='trace-start')||
    (records&&depth===0))throw Error('bank stream sequence discontinuity')
   const nextDepth=depth+(event.kind==='trace-start'?1:event.kind==='trace-end'?-1:0)
   if(nextDepth<0)throw Error('bank stream trace ended without a start')
   const serialized=JSON.stringify(event)
   if(typeof serialized!=='string')throw Error('bank stream serialization produced no row')
   const row=serialized+'\n',size=Buffer.byteLength(row)
   if(bytes+size>maxBytes)throw Error('parity bank stream exceeded its complete-evidence bound')
   hash.update(row);records++;bytes+=size;buffer+=row;bufferBytes+=size
   if(records===1)firstSequence=event.sequence
   lastSequence=event.sequence;depth=nextDepth
   if(bufferBytes>=flushBytes)flush()
  }catch(error){remember(error);throw failure}
 }
 const finish=():BankEventSummary=>{
  // A separate boolean retains even `throw undefined`. Never clear the first
  // failure, retry a failed flush, or summarize a successfully written prefix.
  try{checkFailure();if(!closed){
   if(!records||depth!==0)throw Error('bank stream lacks a complete trace')
   flush()
  }}catch(error){remember(error)}
  finally{if(!closed){closed=true;try{close(fd)}catch(error){remember(error)}}}
  checkFailure()
  if(!summary){try{summary=Object.freeze({records,bytes,storedBytes,maxBytes,
   sha256:hash.digest('hex'),firstSequence,lastSequence})}catch(error){remember(error);throw failure}}
  return summary
 }
 return Object.freeze({record,finish})
}

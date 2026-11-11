import {strict as assert} from 'node:assert'
import {Worker} from 'node:worker_threads'
import {createUnitPublisher,readUnitSnapshot,meterKeys,unitSnapshotBytes} from './unit-snapshot.mjs'
// Owned finite synthetic loop. Production clocks and inputs are not changed.
const mode=process.argv[2];assert(['silent','zero-price','priced'].includes(mode))
const buffer=new SharedArrayBuffer(unitSnapshotBytes),initial=Object.fromEntries(meterKeys.map(k=>[k,0])),publisher=createUnitPublisher(buffer,initial),weights=meterKeys.map(k=>k==='evals'?1:0)
const worker=new Worker(new URL('./unit-observer-worker.mjs',import.meta.url),{workerData:{buffer,weights}})
const exited=new Promise((resolve,reject)=>{worker.once('exit',code=>code?reject(Error('worker '+code)):resolve());worker.once('error',reject)})
function mainThreadUnitControl(){const until=performance.now()+1400;let count=0;while(performance.now()<until){count++;if(mode!=='silent')publisher.publish(mode==='priced'?'evals':'tableCells',count)}return count}
try{
 await new Promise((resolve,reject)=>{worker.once('message',value=>value.ready?resolve():reject(Error(value.error)));worker.once('error',reject)})
 Atomics.store(publisher.control,1,1);const iterations=mainThreadUnitControl();Atomics.store(publisher.control,1,2);worker.postMessage('stop');await exited
 console.log('F3_UNIT_CONTROL '+JSON.stringify({mode,iterations,snapshot:readUnitSnapshot(buffer,weights)}))
}finally{await worker.terminate()}

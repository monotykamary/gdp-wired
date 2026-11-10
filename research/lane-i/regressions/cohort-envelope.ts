// Keep the exact raw measurement traces; remove only their nested transport encoding.
import {brotliCompressSync,brotliDecompressSync,gunzipSync,constants} from 'node:zlib'
import {decodeReceipt} from './merge-bisect-audit.ts'
export function packCohort(group:{id:number,cpu:string|undefined,revisions:string[],results:any[]}):Buffer{
 const results=group.results.map(result=>{if(result.exit!==0)return result;const {stdout,...rest}=result;return{...rest,receipt:decodeReceipt(stdout)}})
 return brotliCompressSync(JSON.stringify({...group,format:'decoded-v1',results}),{params:{[constants.BROTLI_PARAM_QUALITY]:11,[constants.BROTLI_PARAM_LGWIN]:24}})
}
export function unpackCohort(bytes:Uint8Array,encoding:'br'|'gzip'='br'):any{return JSON.parse((encoding==='br'?brotliDecompressSync(bytes):gunzipSync(bytes)).toString('utf8'))}
export function cohortReceipt(group:any,result:any):ReturnType<typeof decodeReceipt>{
 if(group.format===undefined)return decodeReceipt(result.stdout)
 if(group.format!=='decoded-v1'||!result.receipt||result.stdout!==undefined)throw new Error('invalid cohort receipt format')
 return result.receipt
}

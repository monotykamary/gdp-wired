import {test,expect} from 'bun:test'
import {parseShardReceipt} from './shard-receipt.ts'
test('both singular and plural Bun file summaries are counted',()=>{
 const r=parseShardReceipt(' 2 pass\n 0 fail\nRan 2 tests across 1 file. [1ms]\n 3 pass\n 1 skip\n 0 fail\nRan 4 tests across 2 files. [2ms]\n')
 expect(r).toEqual({pass:5,fail:0,skip:1,runs:[{tests:2,files:1},{tests:4,files:2}],complete:true})
})
test('a missing or truncated summary is incomplete',()=>{
 expect(parseShardReceipt(' 2 pass\n 0 fail\n').complete).toBe(false)
 expect(parseShardReceipt(' 2 pass\nRan 3 tests across 1 file. [1ms]\n').complete).toBe(false)
})
test('completeness does not turn failed tests into passes',()=>{
 const r=parseShardReceipt(' 2 pass\n 1 fail\nRan 3 tests across 1 file. [1ms]\n')
 expect(r.complete).toBe(true);expect(r.fail).toBe(1)
})

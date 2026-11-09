import {expect,test} from 'bun:test'
import {parseResourceValues} from './resource-run.ts'
test('kernel resource counters accept tab and space separators',()=>{
 expect(parseResourceValues('VmRSS:\t 1234 kB\nMemAvailable:   4321 kB\noom_kill 7\nName:\tbun\n')).toEqual({VmRSS:1234,MemAvailable:4321,oom_kill:7})
 expect(parseResourceValues('high 0\noom 3\noom_kill 2\n')).toEqual({high:0,oom:3,oom_kill:2})
})

import {test,expect} from 'bun:test'
import {selectPaxosCpu} from './paxos-cpu.ts'
test('Paxos timing CPU is explicit and limited to separate qualified cohorts',()=>{expect(selectPaxosCpu()).toBe('AMD EPYC 9455 48-Core Processor');expect(selectPaxosCpu('AMD Ryzen 9 9950X 16-Core Processor')).toBe('AMD Ryzen 9 9950X 16-Core Processor');expect(()=>selectPaxosCpu('other')).toThrow('unsupported Paxos timing CPU')})

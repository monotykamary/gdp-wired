import {afterEach,beforeEach,expect,spyOn,test} from 'bun:test'
import {type Goal,check} from '../kernel/kernel.ts'
import {atMost,n,plus,same,x} from './machine.ts'
import {minimalViewFirst} from './count-minimal-view.ts'
import * as replay from './count-replay-skeleton.ts'
import {env} from './solver.ts'
const flags=['GDP_COUNT_REPLAY_FORWARD','GDP_COUNT_G1_OWNED_DEFER','GDP_COUNT_C2_LEMMAS','GDP_COUNT_C2_REPLAY','GDP_COUNT_DEFER_CHECKS'] as const
let saved:(string|undefined)[]=[]
beforeEach(()=>{saved=flags.map(key=>env[key]);for(const key of flags)env[key]='1'})
afterEach(()=>{flags.forEach((key,i)=>{if(saved[i]===undefined)delete env[key];else env[key]=saved[i]})})
for(const [deferCheck,deferReplayCheck,wanted]of [[false,false,false],[true,false,false],[false,true,false],[true,true,true]]as const)test('replay ownership forwarding '+deferCheck+'/'+deferReplayCheck,()=>{
 const original=replay.replayLinearSkeleton;let seen:boolean|undefined
 const spy=spyOn(replay,'replayLinearSkeleton').mockImplementation((...args)=>{seen=args[4]?.deferCheck;return original(...args)})
 try{const sum=plus(x('a'),x('b')),full:Goal={name:'full',hyps:[atMost(x('a'),n(0)),atMost(x('b'),n(0)),atMost(n(1),sum)]},small:Goal={name:'small',hyps:[atMost(sum,n(0)),atMost(n(1),sum)]},result=minimalViewFirst(full,small,new Map(),Infinity,undefined,new Map(),{deferCheck,deferReplayCheck});expect(seen).toBe(wanted);expect(result.kind).toBe('proof');expect(result.tree&&check(full,result.tree)).toBe(true)}finally{spy.mockRestore()}
})
test('deferred replay cannot certify a contradictory projection of a satisfiable goal',()=>{
 const full:Goal={name:'sat',hyps:[same(x('a'),n(0))]},small:Goal={name:'invalid projection',hyps:[atMost(n(1),n(0))]}
 const result=minimalViewFirst(full,small,new Map(),Infinity,undefined,new Map(),{deferCheck:true,deferReplayCheck:true});expect(result.kind).toBe('rejected');expect(result.tree).toBeUndefined()
})

import {expect,test} from 'bun:test'
import {optionalReachabilityScreen} from './count-reachability.ts'

for(const flag of [undefined,'0','false','1'])test('whole reachable screen is explicit opt-in: '+String(flag),()=>{
 const previous=process.env.GDP_COUNT_REACHABILITY_SCREEN
 let setup=0
 try{
  if(flag===undefined)delete process.env.GDP_COUNT_REACHABILITY_SCREEN
  else process.env.GDP_COUNT_REACHABILITY_SCREEN=flag
  const screen={screen:()=>{throw Error('this test must not run a screen')}}
  const result=optionalReachabilityScreen(()=>{setup++;return screen})
  expect(setup).toBe(flag==='1'?1:0)
  expect(result).toBe(flag==='1'?screen:undefined)
 }finally{
  if(previous===undefined)delete process.env.GDP_COUNT_REACHABILITY_SCREEN
  else process.env.GDP_COUNT_REACHABILITY_SCREEN=previous
 }
})

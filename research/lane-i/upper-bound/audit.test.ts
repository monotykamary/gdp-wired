import {test,expect} from 'bun:test'
import {elapsedSeconds,stopKind} from './audit.ts'
test('resource wall clocks parse seconds, minutes and hours',()=>{
 expect(elapsedSeconds('Elapsed (wall clock) time (h:mm:ss or m:ss): 6:15.96')).toBeCloseTo(375.96)
 expect(elapsedSeconds('Elapsed (wall clock) time (h:mm:ss or m:ss): 1:02:03.5')).toBe(3723.5)
 expect(elapsedSeconds('missing')).toBeUndefined()
})
test('a short SIGKILL is not a thirty-minute watchdog result',()=>{
 expect(stopKind('censored',false,137,375.96)).toBe('early-process-kill')
 expect(stopKind('censored',false,124,1810.4)).toBe('watchdog')
 expect(stopKind('censored',true,0,1800)).toBe('cooperative-wall')
 expect(stopKind('censored',false,0,5)).toBe('other-nonterminal')
})
test('stop classification never promotes a non-closed result',()=>{
 expect(stopKind('unknown',true,0,1)).toBe('unknown')
 expect(stopKind('closed',true,0,1)).toBe('closed')
})

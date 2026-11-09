import {expect,test} from 'bun:test'
import {parseUpperLog} from './summarize.ts'
const result={status:'closed',checked:true,familySize:34,suppliedLaws:[],originalFamily:true,noShare:true,countedUnits:12,wallMs:34,peakRssKiB:50,progress:{excludedCount:2,excluded:[3,7],leaf:{path:['p']},last:{stage:'closure-final'}}}
test('a missing shard stays pending',()=>{expect(parseUpperLog('').status).toBe('pending')})
test('a closed worker without independent verification is not closed',()=>{const r=parseUpperLog('UPPER_RESULT '+JSON.stringify(result));expect(r.status).toBe('unknown');expect(r.issues).toContain('missing/failed independent check')})
test('a fresh checked result retains resource and leaf metrics',()=>{const r=parseUpperLog('UPPER_RESULT '+JSON.stringify(result)+'\nUPPER_VERIFY {"checked":true}\nMaximum resident set size (kbytes): 70');expect(r.status).toBe('closed');expect(r.peakRssKiB).toBe(70);expect(r.excludedCount).toBe(2);expect(r.countedUnitsLowerBound).toBe(false)})
test('a forced stop retains only a lower bound',()=>{const r=parseUpperLog('UPPER_CENSORED {"countedUnits":10,"wallMs":1800000,"excludedCount":0}');expect(r.status).toBe('censored');expect(r.countedUnits).toBe(10);expect(r.countedUnitsLowerBound).toBe(true)})
test('a different family cannot be admitted',()=>{const r=parseUpperLog('UPPER_RESULT '+JSON.stringify({...result,familySize:35})+'\nUPPER_VERIFY {"checked":true}');expect(r.status).toBe('unknown');expect(r.issues).toContain('invalid original-family contract')})

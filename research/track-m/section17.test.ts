import {test,expect} from 'bun:test'
import {goalSize,proportionalDraw} from './section17-budget.ts'
test('pooled shares are derived, nonnegative and capped at a third',()=>{
 for(const r of [-1,0,1,30,900])for(const a of [1,2,8])for(const extra of [0,1,9]){const n=proportionalDraw(r,a,a+extra);expect(n).toBeGreaterThanOrEqual(0);expect(n).toBeLessThanOrEqual(Math.max(0,r)/3)}
 expect(proportionalDraw(900,1,9)).toBe(100);expect(proportionalDraw(900,8,9)).toBe(300);expect(proportionalDraw(900,1,1)).toBe(300)
 expect(proportionalDraw(900,0,0)).toBe(0)
})
test('unspent budget remains in the pool, with no last-law bonus',()=>{const first=proportionalDraw(900,1,3);expect(first).toBe(300);expect(proportionalDraw(850,1,2)).toBe(850/3);expect(proportionalDraw(850,1,1)).toBe(850/3)})
test('goal weights count expression nodes, not names or constants',()=>{expect(goalSize([{op:'<=',a:{op:'var',name:'a'},b:{op:'const',value:100}}])).toBe(3);expect(goalSize({op:'and',xs:[{op:'var',name:'b'},{op:'var',name:'c'}]})).toBe(3)})

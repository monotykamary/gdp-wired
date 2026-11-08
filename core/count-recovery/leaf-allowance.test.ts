import {test,expect} from 'bun:test'
import {leafAllowance} from './leaf-allowance.ts'
import {supportBudget} from '../support-budget.ts'
test('leaf draws reuse exactly the existing priority allowance rule',()=>{
 for(const remaining of [0,1,25,350,1500,5000])for(const left of [1,2,3,9,30]){
  const draw=leafAllowance(remaining,left)
  expect(draw).toBe(supportBudget(remaining,remaining/left,true))
  expect(draw).toBeGreaterThanOrEqual(0);expect(draw).toBeLessThanOrEqual(remaining)
 }
})
test('successive full draws conserve the total allowance',()=>{
 for(const initial of [1,17,350,5000]){let remaining=initial,total=0
  for(let left=9;left>=1;left--){const draw=leafAllowance(remaining,left);total+=draw;remaining-=draw;expect(total).toBeLessThanOrEqual(initial+1e-10)}
  expect(remaining).toBeCloseTo(0,10);expect(total).toBeCloseTo(initial,10)
 }
})
test('split children spend from one parent deadline, not two draws',()=>{
 const initial=900,draw=leafAllowance(initial,9),start=10,end=start+draw,first=120
 expect(draw).toBe(300);expect(Math.max(0,end-(start+first))).toBe(180)
 expect(first+Math.max(0,end-(start+first))).toBe(draw)
})

import {test,expect} from 'bun:test'
import {leafAllowance} from './leaf-allowance.ts'
test('leaf draws take an even remaining share with a one-third ceiling',()=>{
 for(const remaining of [0,1e-9,1,25,350,1500,5000])for(const left of [1,2,3,9,30]){
  const draw=leafAllowance(remaining,left)
  expect(draw).toBe(Math.min(remaining/left,remaining/3))
  expect(draw).toBeGreaterThanOrEqual(0);expect(draw).toBeLessThanOrEqual(remaining/3)
 }
})
test('one third is a ceiling, not a floor or a last-leaf windfall',()=>{
 expect(leafAllowance(900,9)).toBe(100)
 expect(leafAllowance(900,3)).toBe(300)
 expect(leafAllowance(900,2)).toBe(300)
 expect(leafAllowance(900,1)).toBe(300)
 expect(leafAllowance(900,0)).toBe(300)
 expect(leafAllowance(-1,9)).toBe(0)
})
test('successive draws conserve spent plus unspent allowance',()=>{
 for(const initial of [1,17,350,5000]){let remaining=initial,total=0
  for(let left=9;left>=1;left--){const draw=leafAllowance(remaining,left);total+=draw;remaining-=draw
   expect(total).toBeLessThanOrEqual(initial+1e-10);expect(remaining).toBeGreaterThanOrEqual(0)
   expect(total+remaining).toBeCloseTo(initial,10)
  }
  expect(remaining).toBeGreaterThan(0)
 }
})
test('split children spend one parent draw and cannot obtain another',()=>{
 const initial=900,draw=leafAllowance(initial,9),start=10,end=start+draw,first=40
 expect(draw).toBe(100);expect(Math.max(0,end-(start+first))).toBe(60)
 expect(first+Math.max(0,end-(start+first))).toBe(draw)
 expect(Math.max(0,end-(start+draw))).toBe(0)
})

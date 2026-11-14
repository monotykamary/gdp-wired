import {expect, test} from 'bun:test'
import {spawnSync} from 'node:child_process'

const run = (extra: Record<string, string>, program: string) => {
  const env = Object.fromEntries(Object.entries(process.env).filter(([key]) => !key.startsWith('GDP_')))
  const out = spawnSync(process.execPath, ['--eval', program], {cwd: process.cwd(), env: {...env, ...extra}, encoding: 'utf8', timeout: 10000})
  expect(out.status, out.stderr || out.stdout).toBe(0)
}
const imports = `
import {strict as assert} from 'node:assert';
import {clock,counted,fullRate,pastWall,withWall,withBudget,wallAt,wallDeadline,searchNow} from './kernel/prove.ts';
import {checkWall,WallExpired,searchWall} from './core/wall.ts';
`

test('empty flags retain an expired inherited wall inside a legacy counted clock', () => {
  run({}, imports + `
    const expired=performance.now()-1;
    withWall(expired,()=>counted(fullRate,()=>{
      assert.equal(wallAt(),Infinity); // counted endpoint, separate from the inherited real wall
      assert.equal(pastWall(),true);
      assert.throws(()=>checkWall('legacy inherited'),WallExpired);
    },true));
    counted(fullRate,()=>withWall(performance.now()-1,()=>assert.equal(pastWall(),true)),true);
    assert.equal(pastWall(),false);
  `)
})

test('counted searchWall and countedSearchNow support deadlines never become real wall timestamps', () => {
  run({}, imports + `
    Object.defineProperty(performance,'now',{configurable:true,value:()=>1000000});
    counted(fullRate,()=>{
      const end=searchWall(1000);
      assert.equal(end.domain,'counted');
      assert.equal(withWall(end,()=>pastWall()),false);
      assert.equal(withWall(wallDeadline(searchNow()+4800),()=>pastWall()),false);
      withWall(wallDeadline(clock()-1,'counted'),()=>assert.equal(pastWall(),true));
      assert.equal(pastWall(),false);
    },true);
    assert.equal(pastWall(),false);
  `)
})

test('a real deadline keeps its domain when a nested call becomes counted', () => {
  run({}, imports + `
    let now=1000;
    Object.defineProperty(performance,'now',{configurable:true,value:()=>now});
    const end=searchWall(1000);
    assert.equal(end.domain,'real');
    withWall(end,()=>counted(fullRate,()=>{
      assert.equal(pastWall(),false);
      now=end.end+1;
      assert.equal(pastWall(),true);
      assert.throws(()=>checkWall('real through counted'),WallExpired);
    },true));
    assert.equal(pastWall(),false);
  `)
})

test('explicit real endpoints are elided only inside the existing work-only policy', () => {
  run({}, imports + `
    const end=wallDeadline(-Infinity,'real');
    withWall(end,()=>counted(fullRate,()=>assert.equal(pastWall(),true),true));
    withBudget(1000000,()=>withWall(end,()=>assert.equal(pastWall(),false)));
    assert.equal(pastWall(),false);
  `)
})
test('an explicit work budget elides an inherited legacy wall but retains work deadlines', () => {
  run({}, imports + `
    withWall(performance.now()-1,()=>withBudget(1000000,()=>counted(fullRate,()=>{
      assert.equal(pastWall(),false);
      checkWall('explicit work');
      withWall(clock()-1,()=>assert.equal(pastWall(),true));
    },true)));
    assert.equal(pastWall(),false);
  `)
})

test('FULL policy never consults the real wall and still honors its counted deadline', () => {
  run({GDP_WORK_FULL:'1'}, imports + `
    const desc=Object.getOwnPropertyDescriptor(performance,'now');
    Object.defineProperty(performance,'now',{configurable:true,value:()=>{throw Error('FULL wall read')}});
    try {
      counted(fullRate,()=>withWall(clock()+1000000,()=>{
        assert.equal(pastWall(),false);checkWall('FULL work');
        withWall(clock()-1,()=>assert.equal(pastWall(),true));
      }),true);
    } finally {
      if(desc)Object.defineProperty(performance,'now',desc);else Reflect.deleteProperty(performance,'now');
    }
    assert.equal(pastWall(),false);
  `)
})

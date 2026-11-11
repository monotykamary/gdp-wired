import {expect, test} from 'bun:test'
import {spawnSync} from 'node:child_process'

test('row and guard composers use the shared trace boundary with both control clocks forbidden', () => {
  const env = Object.fromEntries(Object.entries(process.env).filter(([name]) => !name.startsWith('GDP_')))
  const result = spawnSync(process.execPath, ['--eval', `
    import {strict as assert} from 'node:assert';
    import * as budget from './kernel/prove.ts';
    import {rowCompositionFixture} from './core/count-row-composition.fixture.ts';
    import {proveCountRowComposition} from './core/count-row-composition.ts';
    import {proveCountGuardComposition} from './core/count-guard-composition.ts';
    import {prepareGuardCountContext} from './core/count-guard-context.ts';
    import {certFor} from './core/counts.ts';
    import {all,get,n,same,x} from './core/machine.ts';
    import {checkMC,countedObligations} from './kernel/kernel.ts';
    const key=(a,b)=>({op:'add',a:{op:'mul',k:4,a:x(a)},b:x(b)}), below=x('size');
    const member=same(get('edge',key('row','member')),n(1));
    const m={name:'renamed clock fixture',params:['size'],inputs:['move'],state:{phase:n(0)},maps:{edge:0,tick:0,limit:0},step:{},pre:all({op:'<=',a:n(1),b:below},{op:'<=',a:below,b:n(4)}),assume:{op:'or',xs:[5,6,7].map(i=>same(x('move'),n(i)))},counts:{
      voters:{j:'row',lo:'column',key:'member',base:4,below,body:{op:'if',c:all(member,{op:'<',a:get('tick',x('member')),b:get('limit',x('column'))}),then:n(1),else:n(0)}},
      rows:{j:'row',key:'member',below,body:{op:'if',c:member,then:n(1),else:n(0)}}}};
    const law={name:'renamed bound',forall:'a',keys:['b'],holds:{op:'or',xs:[{op:'not',x:all({op:'<',a:x('a'),b:below},{op:'<',a:x('b'),b:below})},{op:'<=',a:{op:'mul',k:2,a:get('voters',key('a','b'))},b:get('rows',x('a'))}]}};
    const phase={name:'zero phase',forall:'t',holds:{op:'or',xs:[{op:'not',x:same(x('phase'),n(0))},same(get('limit',x('t')),n(0))]}};
    let reads=0;const forbidden=()=>{reads++;throw Error('composer read a control clock')};
    Object.defineProperty(performance,'now',{configurable:true,value:forbidden});
    Object.defineProperty(Date,'now',{configurable:true,value:forbidden});
    const run=()=>{
      const until=budget.clock()+10000,request=(g,ds)=>certFor(g,ds,false,0,()=>true);
      const row=rowCompositionFixture(),rowProof=proveCountRowComposition(row.m,row.family,row.law,until,request);
      assert(rowProof,'row composition');
      for(const p of countedObligations(row.m,row.family,{[row.law.name]:rowProof.instances},row.family.indexOf(row.law)))assert(checkMC(p.goal.hyps,p.decls,rowProof.certs[p.goal.name]));
      const family=[law,phase],context=prepareGuardCountContext(m,law,family);
      const guardProof=proveCountGuardComposition(context,family,law,until,request);
      assert(guardProof,'guard composition');
      for(const p of countedObligations(context.machine,family,{[law.name]:guardProof.instances},0))assert(checkMC(p.goal.hyps,p.decls,guardProof.certs[p.goal.name]));
    };
    if('withBudget' in budget)budget.withBudget(3000000,run);
    else budget.counted(budget.fullRate,run,true);
    assert.equal(reads,0);
  `], {cwd: new URL('../', import.meta.url).pathname, env: {...env, GDP_WORK_FULL: '1', GDP_COUNT_STRATEGIES: '1'}, encoding: 'utf8', timeout: 30000})
  if (result.status !== 0) throw Error(result.stderr)
  expect(result.status).toBe(0)
})

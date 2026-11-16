import {expect,test} from 'bun:test'
import {mkdtempSync,writeFileSync,rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {extractC} from '../../core/extract-c.ts'
import {buildLaw} from '../../core/laws.ts'
import {proveSteps} from '../../core/dsl.ts'

test('C unsigned boundary has a checked certificate and a native-interpreted source law',()=>{
  const root=mkdtempSync(join(tmpdir(),'gdp-reader-c-boundary-'))
  try {
    const file=join(root,'meter.c')
    writeFileSync(file,`#include <stdio.h>
int quota_bonus(int n);
struct meter { unsigned used; unsigned cap; };
void meter_init(struct meter *m, unsigned cap) { m->used = 0; m->cap = cap; }
int meter_take(struct meter *m, unsigned n) {
  fflush(stdout); // gdp: skip
  unsigned extra = (unsigned)quota_bonus((int)(n % 100));
  if (n > m->cap || extra > m->cap - n || m->used > m->cap - n - extra) return -1;
  m->used += n + extra;
  return 0;
}
`)
    const x=extractC(file,{check:{runs:25,depth:6,states:50}})
    if(!x.ok) throw Error(JSON.stringify(x.refusals))
    const b=buildLaw(x,{name:'never past its cap',expr:'old(used) > old(cap) or used <= cap',method:'meter_take'})
    if(b.kind!=='step') throw Error('expected step law')
    const verdict=proveSteps(x.rule!,x.invariants??[],[b.law],{search:false})
    expect(verdict).toMatchObject({proven:true,checked:true,translation:'sampled'})
    expect(verdict.translationChecks).toBeGreaterThan(0)
  } finally {rmSync(root,{recursive:true,force:true})}
},120000)

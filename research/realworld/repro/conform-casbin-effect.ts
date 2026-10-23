// Conformance harness for access/node-casbin/effectorStream: runs node-casbin's own enforcer (casbin@5.51.1 from npm,
// whose gitHead is the pinned commit, installed into a temp dir; never vendored) and the rule's interpreter on the same
// random policy lists, and reports the first divergence in enforce()'s answer.
//
// Each policy is one step of the rule: a row [k, eft] of `p = sub, eft`, the matcher `m = res(p.sub)` with `res` a
// function returning the matcher result the step names (false, true, 2, 3 or 7), and eft '' (absent: the code's
// `if (eft && ...)`), 'allow', 'deny' or another string. The request has no field the matcher reads.
// subjectPriority is left out here (it sorts the policies by a role hierarchy first); it shares priority's branch.
//   bun research/realworld/repro/conform-casbin-effect.ts [dir with node_modules/casbin]
import {execSync} from 'node:child_process'
import {existsSync, mkdtempSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {effectorStream} from '../items/authz-casbin.ts'

let dir = process.argv[2]
if (!dir || !existsSync(join(dir, 'node_modules/casbin'))) {
  dir = mkdtempSync(join(tmpdir(), 'casbin-'))
  execSync('npm init -y && npm install casbin@5.51.1 --no-audit --no-fund', {cwd: dir, stdio: 'ignore'})
}
// @ts-expect-error casbin is installed into a temp dir at run time, not in the repo's node_modules
const casbin = await import(join(dir, 'node_modules/casbin/lib/cjs/index.js')) as typeof import('casbin')

const exprs = {allow: 'some(where (p.eft == allow))', deny: '!some(where (p.eft == deny))', allowAndDeny: 'some(where (p.eft == allow)) && !some(where (p.eft == deny))', priority: 'priority(p.eft) || deny'} as const
const results = ['falsy', 'truthy', 'num2', 'num3', 'numOther'] as const
const value = {falsy: false, truthy: true, num2: 2, num3: 3, numOther: 7} as const
const efts = ['none', 'allow', 'deny', 'other'] as const
const eftText = {none: '', allow: 'allow', deny: 'deny', other: 'maybe'} as const

const r = effectorStream(), run = r.interpreter()
let seed = 5
const rand = (n: number) => ((seed = (seed * 1103515245 + 12345) % 2 ** 31), seed % n)
let failure: string | undefined, runs = 0
for (; runs < 1500 && !failure; runs++) {
  const expr = (Object.keys(exprs) as (keyof typeof exprs)[])[rand(4)]!
  const policies = Array.from({length: rand(7)}, () => ({result: results[rand(5)]!, pEft: efts[rand(4)]!}))
  const m = casbin.newModelFromString(`[request_definition]\nr = sub\n[policy_definition]\np = sub, eft\n[policy_effect]\ne = ${exprs[expr]}\n[matchers]\nm = res(p.sub)\n`)
  const e = await casbin.newEnforcer(m)
  await e.addFunction('res', (k: string) => (k === '' ? false : value[policies[Number(k)]!.result]))
  for (let i = 0; i < policies.length; i++) await e.addPolicy(String(i), eftText[policies[i]!.pEft])
  const got = e.enforceSync('anyone')
  const params = r.encodeParams({expr})
  let st = run.init(params)
  // No policy: the code takes its else branch (coreEnforcer.ts:574-596), one push of the matcher's own result, which
  // here reads p.sub = '' (res('') is false: Indeterminate).
  for (const p of policies.length ? policies : [{result: 'falsy' as const, pEft: 'none' as const}]) st = run.step(params, st, r.encodeInput(p))
  const want = (r.decode(st) as {res: boolean}).res
  if (got !== want) failure = `${expr}, policies ${JSON.stringify(policies)}: casbin ${got}, rule ${want}`
}
console.log(failure ? `DIVERGES ${failure}` : `conforms: ${runs} random policy lists, enforce() equal to the rule's result`)

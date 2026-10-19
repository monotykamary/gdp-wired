#!/bin/sh
# The published package as a user gets it: the tarball (bun pm pack, as CI packs it) installed with npm into an empty
# project, the README's budget example run under plain Node, and a TypeScript consumer type-checked against the
# declarations. Usage: sh scripts/smoke.sh [tarball]  (packs one when none is given)
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
tarball=${1:-}
if [ -z "$tarball" ]; then
  (cd "$root" && bun scripts/build.ts >/dev/null && bun pm pack --destination "$work/pack" >/dev/null)
  tarball=$(ls "$work"/pack/*.tgz)
fi
cd "$work"
printf '{"name":"smoke","private":true,"type":"module"}\n' > package.json
npm install --no-audit --no-fund --silent "$tarball" "typescript@$(node -p "require('$root/package.json').devDependencies.typescript")" \
  "@gdp-ts/core@$(node -p "require('$root/package.json').devDependencies['@gdp-ts/core']")"
cat > smoke.mjs <<'JS'
import {everyKey, min, nat, proveRule, rule, when} from 'gdp-wired'
import {interpret} from 'gdp-wired/machine'
import {leanProject, toLean} from 'gdp-wired/lean'
const budget = rule('budget').params({b: nat, m: nat}).inputs({c: nat}).state({s: 0})
  .step(({c, s, b, m}) => ({s: when(s.lt(b), s.plus(min(c, m)), s)}))
const v = proveRule(budget, [budget.law('spend stays within b + m', ({s, b, m}) => s.atMost(b.plus(m)))])
if (!v.proven || !v.checked) throw new Error(`not proven: ${JSON.stringify(v)}`)
const run = budget.compiled(), params = budget.encodeParams({b: 100, m: 30})
let st = run.init(params)
for (const c of [50, 40, 70, 20]) st = run.step(params, st, budget.encodeInput({c}))
if (st.scalars.s !== 110) throw new Error(`compiled spend ${st.scalars.s}, not 110`)
if (typeof interpret !== 'function') throw new Error('gdp-wired/machine has no interpret')
const lean = toLean([{id: 'budget', machine: budget.machine, laws: [budget.law('spend stays within b + m', ({s, b, m}) => s.atMost(b.plus(m)))]}])
if (!lean.includes('theorem law0') || !lean.includes('ρ «s» ≤ (ρ «b» + ρ «m»)')) throw new Error('gdp-wired/lean: no readable statement')
const project = leanProject(lean)
if (!project['lakefile.lean'] || !project['Kernel.lean'] || !project['Sets.lean'] || !project['Proofs.lean']) throw new Error('gdp-wired/lean: an incomplete project')
// A set of names: a request carries a set, and only names in it are ever held.
const club = rule('club').inputs({op: nat}).maps({Member: 0}).carries('Invited')
  .flags(({Invited}) => ({bits: everyKey(k => Invited.at(k).atMost(1))})).assume(({bits}) => bits)
  .step(({op, Invited, Member}) => ({Member: Member.each(k => when(op.eq(1), Invited.at(k), Member.at(k)))}))
const sets = toLean([{id: 'club', machine: club.machine, laws: [club.law('members are a set', ({Member}) => ({forall: k => Member.at(k).atMost(1)}))]}])
if (!sets.includes('import Sets') || !sets.includes('smachine_sound')) throw new Error('gdp-wired/lean: a machine with sets not through smachine_sound')
// gdp-ts's proofs minted by a proven gate: a one-time token is redeemed once.
const {defineProof, name} = await import('@gdp-ts/core')
const {gate} = await import('gdp-wired/gdp')
const tokens = rule('tokens').inputs({op: nat, token: nat}).maps({Used: 0})
  .flags(({op, token, Used}) => ({redeem: op.eq(1).and(Used.at(token).eq(0))}))
  .step(({token, redeem, Used}) => ({Used: Used.bump(token, redeem)}))
const redeemed = gate(defineProof('Redeemed'), tokens, 'redeem', {laws: [tokens.law('used at most once', ({Used}) => ({forall: k => Used.at(k).atMost(1)}))]})
const minted = name(7, t => [redeemed.request({op: 1, token: 7}, t)?.kind, redeemed.request({op: 1, token: 7}, t)])
if (minted[0] !== 'Redeemed' || minted[1] !== null) throw new Error(`gdp-wired/gdp: minted ${JSON.stringify(minted)}`)
console.log(`node ${process.version}: proven, kernel accepts; compiled spend 110; Lean project of ${Object.keys(project).length} files; a gate minted once`)
JS
node smoke.mjs
cat > consumer.ts <<'TS'
import {bool, forall, fun, nat, proveRule, proveSteps, rule, type Verdict} from 'gdp-wired'
import type {Machine} from 'gdp-wired/machine'
import {check} from 'gdp-wired/kernel'
import {type LeanItem, toLean} from 'gdp-wired/lean'
import {product} from 'gdp-wired/compose'
import {type Mint, guard} from 'gdp-wired/gdp'
import {defineProof} from '@gdp-ts/core'
const caps = rule('caps').params({d: nat}).inputs({day: nat}).maps({Day: 0})
  .step(({day, Day}) => ({Day: Day.bump(day, Day.at(day).lt(1))}))
const v: Verdict = proveRule(caps, [caps.law('at most one a day', ({Day}) => forall(k => Day.at(k).atMost(1)))])
const s: Verdict = proveSteps(caps, [], [caps.stepLaw('never down', ({Day}, after) => forall(k => Day.at(k).atMost(after.Day.at(k))))])
const m: Machine = caps.machine
const items: LeanItem[] = [{id: 'caps', machine: product(m, m), laws: []}]
const text: string = toLean(items)
const access = fun('access').inputs({cleared: bool}).returns(({cleared}) => ({permit: cleared}))
const mint: Mint<'CanRead', {cleared: boolean}> = guard(defineProof('CanRead'), access, 'permit', {laws: [access.law('only cleared', (_, out) => out.permit, (_, {cleared}) => cleared)]})
export {v, s, m, check, text, mint}
TS
printf '{"compilerOptions":{"strict":true,"noEmit":true,"module":"nodenext","moduleResolution":"nodenext","target":"es2022","lib":["es2022"],"types":[],"skipLibCheck":false},"files":["consumer.ts"]}\n' > tsconfig.json
npx tsc -p tsconfig.json
echo "typescript consumer: declarations resolve and type-check"

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
npm install --no-audit --no-fund --silent "$tarball" "typescript@$(node -p "require('$root/package.json').devDependencies.typescript")"
cat > smoke.mjs <<'JS'
import {min, nat, proveRule, rule, when} from 'gdp-wired'
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
if (!project['lakefile.lean'] || !project['Kernel.lean'] || !project['Proofs.lean']) throw new Error('gdp-wired/lean: an incomplete project')
console.log(`node ${process.version}: proven, kernel accepts; compiled spend 110; Lean project of ${Object.keys(project).length} files`)
JS
node smoke.mjs
cat > consumer.ts <<'TS'
import {forall, nat, proveRule, proveSteps, rule, type Verdict} from 'gdp-wired'
import type {Machine} from 'gdp-wired/machine'
import {check} from 'gdp-wired/kernel'
import {type LeanItem, toLean} from 'gdp-wired/lean'
import {product} from 'gdp-wired/compose'
const caps = rule('caps').params({d: nat}).inputs({day: nat}).maps({Day: 0})
  .step(({day, Day}) => ({Day: Day.bump(day, Day.at(day).lt(1))}))
const v: Verdict = proveRule(caps, [caps.law('at most one a day', ({Day}) => forall(k => Day.at(k).atMost(1)))])
const s: Verdict = proveSteps(caps, [], [caps.stepLaw('never down', ({Day}, after) => forall(k => Day.at(k).atMost(after.Day.at(k))))])
const m: Machine = caps.machine
const items: LeanItem[] = [{id: 'caps', machine: product(m, m), laws: []}]
const text: string = toLean(items)
export {v, s, m, check, text}
TS
printf '{"compilerOptions":{"strict":true,"noEmit":true,"module":"nodenext","moduleResolution":"nodenext","target":"es2022","lib":["es2022"],"types":[],"skipLibCheck":false},"files":["consumer.ts"]}\n' > tsconfig.json
npx tsc -p tsconfig.json
echo "typescript consumer: declarations resolve and type-check"

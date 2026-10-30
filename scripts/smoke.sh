#!/bin/sh
# The published package as a user gets it: the tarball (bun pm pack, as CI packs it) installed with npm into an empty
# project, the README's budget example run under plain Node, and a TypeScript consumer type-checked against the
# declarations; then gdp-wired-cli (packages/cli) installed alone beside it, its `npx gdp-wired-cli check` on a Python
# file. Usage: sh scripts/smoke.sh [tarball cli-tarball]  (packs both when none is given)
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
tarball=${1:-} clitarball=${2:-}
if [ -z "$tarball" ]; then
  (cd "$root" && bun scripts/build.ts >/dev/null && bun pm pack --destination "$work/pack" >/dev/null)
  tarball=$(ls "$work"/pack/*.tgz)
fi
if [ -z "$clitarball" ]; then
  (cd "$root/packages/cli" && bun pm pack --destination "$work/pack-cli" >/dev/null)
  clitarball=$(ls "$work"/pack-cli/*.tgz)
fi
cd "$work"
printf '{"name":"smoke","private":true,"type":"module"}\n' > package.json
npm install --no-audit --no-fund --silent "$tarball" "typescript@$(node -p "require('$root/package.json').devDependencies.typescript")" \
  "@gdp-ts/core@$(node -p "require('$root/package.json').devDependencies['@gdp-ts/core']")"
cat > smoke.mjs <<'JS'
import {everyKey, min, nat, proveRule, recur, rule, variant, when} from 'gdp-wired'
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
if (!sets.includes('import Sets') || !sets.includes('cyc_qmachine_sound')) throw new Error('gdp-wired/lean: a machine with sets not through its cyclic certificate')
const usualSets = toLean([{id: 'club', machine: club.machine, laws: [club.law('members are a set', ({Member}) => ({forall: k => Member.at(k).atMost(1)}))]}], {cyclic: false})
if (!usualSets.includes('smachine_sound')) throw new Error('gdp-wired/lean: a machine with sets not through smachine_sound with cyclic: false')
// gdp-ts's proofs minted by a proven gate: a one-time token is redeemed once.
const {defineProof, name} = await import('@gdp-ts/core')
const {gate} = await import('gdp-wired/gdp')
const tokens = rule('tokens').inputs({op: nat, token: nat}).maps({Used: 0})
  .flags(({op, token, Used}) => ({redeem: op.eq(1).and(Used.at(token).eq(0))}))
  .step(({token, redeem, Used}) => ({Used: Used.bump(token, redeem)}))
const redeemed = gate(defineProof('Redeemed'), tokens, 'redeem', {laws: [tokens.law('used at most once', ({Used}) => ({forall: k => Used.at(k).atMost(1)}))]})
const minted = name(7, t => [redeemed.request({op: 1, token: 7}, t)?.kind, redeemed.request({op: 1, token: 7}, t)])
if (minted[0] !== 'Redeemed' || minted[1] !== null) throw new Error(`gdp-wired/gdp: minted ${JSON.stringify(minted)}`)
// A recurrence and its lemma, read at a variant's case: the wait is at most 64.
const delay = recur('delay', {zero: 1, next: (_, d) => min(d.times(2), 64)}, {'at most 64': (_, d) => d.atMost(64)})
const Pay = variant({card: {amount: nat}, cash: {}})
const waits = rule('waits').inputs({pay: Pay, n: nat}).state({w: 0}).fns({delay})
  .step(({pay, n, delay}) => ({w: pay.match({card: c => min(c.amount, delay(n)), cash: () => 0})}))
const wv = proveRule(waits, [waits.law('the wait is at most 64', ({w}) => w.atMost(64))])
if (!wv.proven || !wv.checked) throw new Error(`recur: not proven: ${JSON.stringify(wv)}`)
const wr = waits.compiled(), w = wr.step({}, wr.init({}), waits.encodeInput({pay: {tag: 'card', amount: 100}, n: 3}))
if (w.scalars.w !== 8) throw new Error(`recur: compiled wait ${w.scalars.w}, not 8`)
if (!toLean([{id: 'waits', machine: waits.machine, laws: []}]).includes('def Recur.delay')) throw new Error('gdp-wired/lean: no recurrence defined')
// The Effect front end loads with effect absent: nothing in the package imports it (the code read brings it).
let effectThere = true
try { await import('effect') } catch { effectThere = false }
if (effectThere) throw new Error('effect is installed here: the smoke runs without it')
const fx = await import('gdp-wired/effect')
if (typeof fx.extractEffect !== 'function' || typeof fx.conforms !== 'function' || typeof fx.fromSchema !== 'function') throw new Error('gdp-wired/effect: an export is missing')
// The Python front end loads and refuses, never throws, where no Python runs (python3 is needed only to extract).
const pyx = await import('gdp-wired/extract-py')
const noPy = pyx.extractPython('absent.py', {entry: 'X', python: 'gdp-no-such-python'})
if (noPy.ok || !/python3 is needed to extract Python/.test(noPy.refusals[0]?.what ?? '')) throw new Error(`gdp-wired/extract-py without Python: ${JSON.stringify(noPy)}`)
// The C front end refuses, never throws, where no clang runs (clang is needed only to extract).
const cx = await import('gdp-wired/extract-c')
const noC = cx.extractC('absent.c', {entry: 'X', clang: 'gdp-no-such-clang'})
if (noC.ok || !/clang is needed to extract C/.test(noC.refusals[0]?.what ?? '')) throw new Error(`gdp-wired/extract-c without clang: ${JSON.stringify(noC)}`)
const cppx = await import('gdp-wired/extract-cpp')
const noCpp = cppx.extractCpp('absent.cpp', {entry: 'X', clang: 'gdp-no-such-clang'})
if (noCpp.ok || !/clang is needed to extract C\+\+/.test(noCpp.refusals[0]?.what ?? '')) throw new Error(`gdp-wired/extract-cpp without clang: ${JSON.stringify(noCpp)}`)
// The JVM front ends refuse, never throw, where no JDK runs (a JDK is needed only to extract).
const jx = await import('gdp-wired/extract-java')
const noJdk = jx.extractJava('absent.java', {entry: 'X', javaHome: '/gdp-no-such-jdk'})
if (noJdk.ok || !/JDK 17 or later is needed/.test(noJdk.refusals[0]?.what ?? '')) throw new Error(`gdp-wired/extract-java without a JDK: ${JSON.stringify(noJdk)}`)
const kx = await import('gdp-wired/extract-kotlin')
const noKt = kx.extractKotlin('absent.kt', {entry: 'X', kotlinHome: '/gdp-no-such-kotlin'})
if (noKt.ok || !/kotlinc .* is needed to extract Kotlin/.test(noKt.refusals[0]?.what ?? '')) throw new Error(`gdp-wired/extract-kotlin without kotlinc: ${JSON.stringify(noKt)}`)
// The Go front end refuses, never throws, where no Go runs or the package isn't there (its reader is built beside it).
const gox = await import('gdp-wired/extract-go')
const noGo = gox.extractGo('absent-package', {})
if (noGo.ok || !/Go reader didn't run|go is needed/.test(noGo.refusals[0]?.what ?? '')) throw new Error(`gdp-wired/extract-go: ${JSON.stringify(noGo)}`)
const swx = await import('gdp-wired/extract-swift')
const noSw = swx.extractSwift('absent.swift', {entry: 'X', swift: 'gdp-no-such-swift'})
if (noSw.ok || !noSw.refusals.length) throw new Error(`gdp-wired/extract-swift without swift: ${JSON.stringify(noSw)}`)
const rsx = await import('gdp-wired/extract-rs')
const noRs = rsx.extractRust('absent-crate', {entry: 'X', cargo: 'gdp-no-such-cargo'})
if (noRs.ok || !noRs.refusals.length) throw new Error(`gdp-wired/extract-rs without cargo: ${JSON.stringify(noRs)}`)
console.log(`node ${process.version}: proven, kernel accepts; compiled spend 110; Lean project of ${Object.keys(project).length} files; a gate minted once; a recurrence's lemma used`)
JS
node smoke.mjs
# The CLI, as npx runs it: a TypeScript class with one law stated in a comment (proven) and one broken (exit 1).
cat > wallet.ts <<'TS'
export class Wallet {
  balance = 0
  // gdp: law a debit never overdraws: balance >= 0
  debit(x: number): boolean { if (x <= 0) throw new Error('positive'); if (x > this.balance) return false; this.balance -= x; return true }
  credit(x: number): void { if (x <= 0) throw new Error('positive'); this.balance += x }
}
TS
npx --no-install gdp-wired check wallet.ts --no-propose > cli.log || { cat cli.log; echo 'gdp-wired check: a proven law exits non-zero'; exit 1; }
grep -q 'proven   a debit never overdraws' cli.log || { cat cli.log; exit 1; }
sed 's|^  credit(x|  // gdp: law a credit adds one more: balance == old(balance) + x + 1\
  credit(x|' wallet.ts > wallet2.ts
if npx --no-install gdp-wired check wallet2.ts --no-propose > cli.log; then cat cli.log; echo 'gdp-wired check: a broken law exits 0'; exit 1; fi
grep -q 'broken   a credit adds one more' cli.log || { cat cli.log; exit 1; }
echo "gdp-wired check: a proven law exits 0, a broken one 1"
cat > consumer.ts <<'TS'
import {bool, forall, fun, nat, proveRule, proveSteps, record, recur, rule, variant, type Verdict} from 'gdp-wired'
import type {Machine} from 'gdp-wired/machine'
import {check} from 'gdp-wired/kernel'
import {type LeanItem, toLean} from 'gdp-wired/lean'
import {product} from 'gdp-wired/compose'
import {type Mint, guard} from 'gdp-wired/gdp'
import {defineProof} from '@gdp-ts/core'
import {type EffectOptions, type Service, extractEffect} from 'gdp-wired/effect'
import {type PyOptions, extractPython} from 'gdp-wired/extract-py'
import {type GoOptions, extractGo} from 'gdp-wired/extract-go'
const goRead: (dir: string, o: GoOptions) => boolean = (dir, o) => extractGo(dir, o).ok
const pyRead: (file: string, o: PyOptions) => boolean = (file, o) => extractPython(file, o).ok
const effectRead: (code: string, o: EffectOptions) => boolean = (code, o) => extractEffect(code, o).ok
const shortRead: boolean = extractEffect('./limiter.ts').ok && extractPython('limiter.py').ok && extractGo('p/limiter.go').ok
const service: Service<{take: (n: number) => unknown}> | undefined = undefined
const caps = rule('caps').params({d: nat}).inputs({day: nat}).maps({Day: 0})
  .step(({day, Day}) => ({Day: Day.bump(day, Day.at(day).lt(1))}))
const v: Verdict = proveRule(caps, [caps.law('at most one a day', ({Day}) => forall(k => Day.at(k).atMost(1)))])
const s: Verdict = proveSteps(caps, [], [caps.stepLaw('never down', ({Day}, after) => forall(k => Day.at(k).atMost(after.Day.at(k))))])
const m: Machine = caps.machine
const items: LeanItem[] = [{id: 'caps', machine: product(m, m), laws: []}]
const text: string = toLean(items)
const access = fun('access').inputs({cleared: bool}).returns(({cleared}) => ({permit: cleared}))
const mint: Mint<'CanRead', {cleared: boolean}> = guard(defineProof('CanRead'), access, 'permit', {laws: [access.law('only cleared', (_, out) => out.permit, (_, {cleared}) => cleared)]})
const pay = fun('pay').inputs({p: variant({card: {amount: nat}, cash: {}}), who: record({limit: nat})})
  .returns(({p, who}) => ({ok: p.match({card: c => c.amount.atMost(who.limit), cash: () => p.is('cash')})}))
const ok: boolean = pay.run({p: {tag: 'card', amount: 3}, who: {limit: 5}}).ok
const steps = recur('steps', {zero: 0, next: (_, y) => y.plus(1)}, {'at most x': (x, y) => y.atMost(x)})
export {v, s, m, check, text, mint, ok, steps, effectRead, service, pyRead, goRead}
TS
printf '{"compilerOptions":{"strict":true,"noEmit":true,"module":"nodenext","moduleResolution":"nodenext","target":"es2022","lib":["es2022"],"types":[],"skipLibCheck":false},"files":["consumer.ts"]}\n' > tsconfig.json
npx tsc -p tsconfig.json
echo "typescript consumer: declarations resolve and type-check"
# gdp-wired-cli, installed with nothing else (its typescript comes with it): a law in a Python file proven (exit 0), a
# broken one (exit 1).
mkdir "$work/cli" && cd "$work/cli"
printf '{"name":"smoke-cli","private":true,"type":"module"}\n' > package.json
npm install --no-audit --no-fund --silent "$tarball" "$clitarball"
cat > meter.py <<'PY'
class Meter:
    def __init__(self, cap: int):
        self.cap = cap
        self.used = 0

    # gdp: law never past the cap: used <= cap or used == 0
    def take(self, n: int) -> bool:
        if n <= 0 or self.used + n > self.cap:
            return False
        self.used += n
        return True
PY
npx --no-install gdp-wired-cli check meter.py --no-propose > cli.log || { cat cli.log; echo 'gdp-wired-cli check: a proven law exits non-zero'; exit 1; }
grep -q 'proven   never past the cap' cli.log || { cat cli.log; exit 1; }
sed 's|^    # gdp: law never past the cap.*|    # gdp: law a take always counts: used == old(used) + n|' meter.py > meter2.py
if npx --no-install gdp-wired-cli check meter2.py --no-propose > cli.log; then cat cli.log; echo 'gdp-wired-cli check: a broken law exits 0'; exit 1; fi
grep -q 'broken   a take always counts' cli.log || { cat cli.log; exit 1; }
echo "gdp-wired-cli check: a proven law exits 0, a broken one 1"

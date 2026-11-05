#!/bin/sh
# Isolated consumers of the actual tarball, with exactly one pinned Effect version per install.
# Boat-only validation: sh scripts/smoke-effect-schema.sh [absolute-tarball]
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
tarball=${1:-}
if [ -z "$tarball" ]; then
  (cd "$root" && bun scripts/build.ts && bun pm pack --destination "$work/pack")
  tarball=$(find "$work/pack" -name '*.tgz' -type f)
fi
for version in 3.22.4 4.0.7; do
  dir="$work/effect-$version"
  mkdir -p "$dir"
  cd "$dir"
  printf '{"name":"schema-consumer","private":true,"type":"module"}\n' > package.json
  npm install --no-audit --no-fund --silent "$tarball" "effect@$version" typescript@5.9.3
  cat > runtime.mjs <<'JS'
import {Schema as S} from 'effect'
import {fromSchema, SchemaError} from 'gdp-wired/effect'
import {Int, int, proveRule, rule} from 'gdp-wired'
const bounded = S.Int.check ? S.Int.check(S.isBetween({minimum: 2, maximum: 4})) : S.Int.pipe(S.between(2, 4))
const k = fromSchema(bounded)
if (!(k.value('n') instanceof Int) || k.report.runtime !== 'exact-on-decoded-closed-values') throw new Error('wrong public kind/report')
for (const n of [1,2,3,4,5,NaN,Infinity,2**53]) {
  let accepted = true
  try { k.encode('n', n) } catch { accepted = false }
  if (accepted !== S.is(bounded)(n)) throw new Error(`acceptance disagrees at ${n}`)
  if (accepted && k.decode('n', k.encode('n', n)) !== n) throw new Error('round trip')
}
const r = rule('packed schema').inputs({n:k}).state({s:k.from(2)}).step(({n}) => ({s:n}))
const result = proveRule(r, [r.law('within schema', ({s}) => s.atLeast(2).and(s.atMost(4)))], {search:false})
if (!result.proven || !result.checked) throw new Error(JSON.stringify(result))
if (proveRule(r.step(({s}) => ({s:s.plus(1)})), [], {search:false}).proven) throw new Error('broken state proven')
let refused = false
try { fromSchema(S.Struct({x:S.optional(S.Boolean)})) } catch (e) { refused = e instanceof SchemaError }
if (!refused) throw new Error('optional accepted as exact')
console.log(`packed schema runtime: ${process.env.EFFECT_VERSION}, proven && checked; broken state refused`)
JS
  EFFECT_VERSION="$version" node runtime.mjs
  cat > consumer.ts <<'TS'
import {Schema as S} from 'effect'
import {fromSchema} from 'gdp-wired/effect'
import {Choice, Int, Str, Term, int, rule} from 'gdp-wired'
const k = fromSchema(S.Struct({n:S.Int, b:S.Boolean, nullable:S.NullOr(S.Int)}))
const value = k.value('v')
const brandedString: Str = fromSchema(S.String.pipe(S.brand('Name'))).value('name')
const brandedLiteral: Choice<'ready'> = fromSchema(S.Literal('ready').pipe(S.brand('Ready'))).value('ready')
const approximate = fromSchema(S.Int, {mode:'approximate'}).value('n')
// @ts-expect-error approximate values are unknown, not promised Int
const approximateInt: Int = approximate
void [brandedString,brandedLiteral,approximateInt]
const n: Int = value.n
// @ts-expect-error symbolic Int is not raw number
const raw: number = value.n
// @ts-expect-error signed Int is not a natural Term
const term: Term = value.n
// @ts-expect-error no any leakage
value.doesNotExist()
const r = rule('packed types').inputs({v:k}).state({n:int.from(0)})
r.step(({n,v}) => ({n:n.plus(v.n)}))
// @ts-expect-error boolean is not a numeric update
r.step(({v}) => ({n:v.b}))
void [n,raw,term]
TS
  printf '{"compilerOptions":{"strict":true,"noEmit":true,"module":"nodenext","moduleResolution":"nodenext","target":"es2022","lib":["es2022","dom"],"types":[],"skipLibCheck":false},"files":["consumer.ts"]}\n' > tsconfig.json
  npx --no-install tsc -p tsconfig.json
  echo "packed schema types: Effect $version"
done

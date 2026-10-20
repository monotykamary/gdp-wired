// Whether two groups of effects conflict, decided over every pair at once: for the suite (`bun examples/groups.ts`),
// core/pairs.test.ts and lean-kernel/package-check.ts. Each effect touches a scope of named resources (or an unknown
// one); two effects conflict when both are effects, one is ordered, and their scopes overlap or one is unknown. A
// request carries each group's effects as a list, and each group's scopes as rows (the effect's place, a name), so the
// pairing of a name with its effect is the request's own data, not a loop's.
//   - the group rule: no ordered pair with an unknown scope and no ordered pair naming one resource, each a condition at
//     every two keys (a row reads its effect at the place it names); its laws say a group found independent has no such
//     pair, and a pair of either kind makes a conflict
//   - against the pair rule: the compiled group rule says what checking every pair with the pair rule says, on drawn
//     groups (examples/groups.ts's main)
//   - broken variants, each refused with a run that breaks a law: pairs on the diagonal only, the last left effect
//     skipped, the first right effect only, and one group against itself
import {type StepLaw, all, bool, everyKey, forall, nat, proveSteps, record, rule, when} from '../core/dsl.ts'

export const Effect = record({effect: bool, ordered: bool, exact: bool})
export const Row = record({item: nat, name: nat})
type Bug = 'diagonal only' | 'skips the last left effect' | 'first right effect only' | 'within one side'
export const groups = (bug?: Bug) => rule('resource groups')
  .carriesList('L', Effect).carriesList('R', Effect).carriesList('LN', Row).carriesList('RN', Row)
  .state({conflict: 0})
  .flags(({L, R, LN, RN}) => {
    const right = bug === 'within one side' ? L : R, rightN = bug === 'within one side' ? LN : RN
    const conflicting = (l: ReturnType<typeof L.at>, r: ReturnType<typeof L.at>) => all(l.effect, r.effect, l.ordered.or(r.ordered))
    return {
      // every row names an effect of its group
      rows: everyKey(p => p.lt(LN.len).implies(LN.at(p).item.lt(L.len))).and(everyKey(q => q.lt(RN.len).implies(RN.at(q).item.lt(R.len)))),
      // no ordered pair of effects with an unknown scope
      known: everyKey((i, j) => all(i.lt(bug === 'skips the last left effect' ? L.len.minus(1) : L.len), j.lt(bug === 'first right effect only' ? 1 : right.len), ...(bug === 'diagonal only' ? [i.eq(j)] : []))
        .implies(all(conflicting(L.at(i), right.at(j)), L.at(i).exact.and(right.at(j).exact).not()).not())),
      // no ordered pair of effects naming one resource
      unshared: everyKey((p, q) => all(p.lt(LN.len), q.lt(rightN.len), LN.at(p).name.eq(rightN.at(q).name), ...(bug === 'diagonal only' ? [LN.at(p).item.eq(rightN.at(q).item)] : []))
        .implies(conflicting(L.at(LN.at(p).item), right.at(rightN.at(q).item)).not())),
    }
  })
  .assume(({rows}) => rows)
  .step(({known, unshared}) => ({conflict: when(known.and(unshared), 0, 1)}))

type Groups = ReturnType<typeof groups>
export const groupLaws = (g: Groups = groups()): StepLaw[] => [
  g.stepLaw('a group found independent has no ordered pair with an unknown scope', ({L, R}, after) => forall((i, j) =>
    all(after.conflict.eq(0), i.lt(L.len), j.lt(R.len), L.at(i).effect, R.at(j).effect, L.at(i).ordered.or(R.at(j).ordered)).implies(L.at(i).exact.and(R.at(j).exact)))),
  g.stepLaw('a group found independent has no ordered pair naming one resource', ({L, R, LN, RN}, after) => forall((p, q) =>
    all(after.conflict.eq(0), p.lt(LN.len), q.lt(RN.len), LN.at(p).name.eq(RN.at(q).name), L.at(LN.at(p).item).effect, R.at(RN.at(q).item).effect)
      .implies(L.at(LN.at(p).item).ordered.or(R.at(RN.at(q).item).ordered).not()))),
  g.stepLaw('an ordered pair with an unknown scope conflicts', ({L, R}, after) => forall((i, j) =>
    all(i.lt(L.len), j.lt(R.len), L.at(i).effect, R.at(j).effect, L.at(i).ordered.or(R.at(j).ordered), L.at(i).exact.and(R.at(j).exact).not()).implies(after.conflict.eq(1)))),
  g.stepLaw('an ordered pair naming one resource conflicts', ({L, R, LN, RN}, after) => forall((p, q) =>
    all(p.lt(LN.len), q.lt(RN.len), LN.at(p).name.eq(RN.at(q).name), L.at(LN.at(p).item).effect, R.at(RN.at(q).item).effect,
      L.at(LN.at(p).item).ordered.or(R.at(RN.at(q).item).ordered)).implies(after.conflict.eq(1)))),
]

// The pair rule the groups generalize: two effects, each with its scope as a set of names.
export const pair = rule('resource pair')
  .inputs({leftEffect: bool, rightEffect: bool, leftExact: bool, rightExact: bool, leftOrdered: bool, rightOrdered: bool})
  .state({conflict: 0})
  .carries('Left', 'Right')
  .flags(({Left, Right}) => ({
    bits: everyKey(k => Left.at(k).atMost(1).and(Right.at(k).atMost(1))),
    shared: Left.disjointFrom(Right).not(),
  }))
  .assume(({bits}) => bits)
  .step(({leftEffect, rightEffect, leftExact, rightExact, leftOrdered, rightOrdered, shared}) => ({
    conflict: when(all(leftEffect, rightEffect, leftOrdered.or(rightOrdered), leftExact.and(rightExact).not().or(shared)), 1, 0),
  }))

// An effect as code holds it: a scope of names, or unknown.
export type Held = {effect: boolean, ordered: boolean, scope: {exact: boolean, names: number[]}}
const rowsOf = (side: Held[]) => side.flatMap((e, item) => (e.scope.exact ? e.scope.names : []).map(name => ({item, name})))
const effectsOf = (side: Held[]) => side.map(e => ({effect: e.effect, ordered: e.ordered, exact: e.scope.exact}))
// Both groups through the compiled group rule, and every pair through the compiled pair rule.
const g = groups(), gc = g.compiled(), p = pair.compiled()
export function decide(left: Held[], right: Held[]): {groups: boolean, pairs: boolean} {
  const st = gc.step({}, gc.init({}), g.encodeInput({L: effectsOf(left), R: effectsOf(right), LN: rowsOf(left), RN: rowsOf(right)} as never))
  const one = (l: Held, r: Held) => pair.decode(p.step({}, p.init({}), pair.encodeInput({
    leftEffect: l.effect, rightEffect: r.effect, leftExact: l.scope.exact, rightExact: r.scope.exact, leftOrdered: l.ordered, rightOrdered: r.ordered,
    Left: new Set(l.scope.exact ? l.scope.names : []), Right: new Set(r.scope.exact ? r.scope.names : []),
  } as never))).conflict === 1
  return {groups: g.decode(st).conflict === 1, pairs: left.some(l => right.some(r => one(l, r)))}
}

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const bug of [undefined, 'diagonal only', 'skips the last left effect', 'first right effect only', 'within one side'] as const) {
    const g = groups(bug), v = proveSteps(g, [], groupLaws(g))
    results.push([`resource groups${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  // The group rule against every pair, on drawn groups of up to four effects over four names.
  let seed = 7
  const draw = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
  const held = (): Held => ({effect: draw(4) > 0, ordered: draw(2) === 1, scope: draw(5) === 0 ? {exact: false, names: []} : {exact: true, names: [...new Set(Array.from({length: draw(3) + 1}, () => 2 + draw(4)))]}})
  let agree = true, conflicts = 0
  for (let n = 0; n < 2000; n++) {
    const left = Array.from({length: draw(5)}, held), right = Array.from({length: draw(5)}, held), d = decide(left, right)
    if (d.groups !== d.pairs) { agree = false; console.log('disagree', JSON.stringify({left, right, ...d})); break }
    if (d.pairs) conflicts++
  }
  results.push([`the group rule says what every pair says (2000 drawn groups, ${conflicts} in conflict)`, agree, true])
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}

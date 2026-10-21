// A sub-second check of the cyclic route (core/cyclic.ts): a recurrence, a machine, a fold, each proven and checked.
import {foldNodes, machineNodes, proveCyclic, recurNodes} from '../../core/cyclic.ts'
import {proveLaws} from '../../kernel/prove.ts'
import {counter, counterLaws, growing} from '../../examples/lemmas.ts'
import {rollup, rollupLaws} from '../../examples/folds.ts'
const t0 = performance.now(), rc = growing().recur!
const r = recurNodes({name: 'growing', args: rc.args, zero: rc.zero, next: rc.next, lemmas: rc.lemmas, between: rc.between, facts: []}), rv = proveCyclic(r.facts, r.specs)
const c = counter(), cl = counterLaws(c), cp = proveLaws(c.machine, cl), mn = machineNodes(c.machine, cl, cp.proof!.instances), mv = proveCyclic(mn.facts, mn.specs)
const f = rollup(), fn = foldNodes(f.fold, rollupLaws(f)), fv = proveCyclic(fn.facts, fn.specs)
console.log(JSON.stringify({recur: rv.proven && rv.checked, machine: mv.proven && mv.checked, fold: fv.proven && fv.checked, ms: Math.round(performance.now() - t0)}))

// The TIP translation's abstract sorts, uninterpreted constants and function variables (translate.ts) on small
// problems: true ones proven; false ones a wrong encoding would prove refuted, each counterexample confirmed by TIP's own
// evaluator (tip.ts) on the goal as TIP states it; what stays outside refused with its reason.
import {expect, test} from 'bun:test'
import {Unsupported, type V, evaluate, parseTip, parseSx, sameV, show} from './tip.ts'
import {substituteWitnesses} from './witness.ts'
import {translate} from './translate.ts'
import {evalX, evalY, programOf, proveData, randomValue, rng, samples} from '../../core/data.ts'

const LIST = '(declare-datatype list (par (a) ((nil) (cons (head a) (tail (list a))))))'
const NAT = '(declare-datatype Nat ((Z) (S (p Nat))))'
const APP = '(define-fun-rec ++ (par (a) (((x (list a)) (y (list a))) (list a))) (match x ((nil y) ((cons z xs) (cons z (++ xs y))))))'
const BIND = '(define-fun-rec >>= (par (a b) (((x (list a)) (y (=> a (list b)))) (list b))) (match x ((nil (_ nil b)) ((cons z xs) (++ (@ y z) (>>= xs y))))))'
const MAP = '(define-fun-rec map (par (a b) (((f (=> a b)) (x (list a))) (list b))) (match x ((nil (_ nil b)) ((cons y xs) (cons (@ f y) (map f xs))))))'
const PLUS = '(define-fun-rec plus ((x Nat) (y Nat)) Nat (match x ((Z y) ((S z) (S (plus z y))))))'

const ELEM = '(define-fun-rec elem (par (a) (((x a) (xs (list a))) Bool)) (match xs ((nil false) ((cons h t) (or (= x h) (elem x t))))))'
const LOOKUP = '(declare-const undefined (par (a) a)) (define-fun-rec at (par (a) (((xs (list a)) (n Nat)) a)) (match xs ((nil (_ undefined a)) ((cons h t) (match n ((Z h) ((S p) (at t p))))))))'
const INDEX_GOAL = '(prove (par (a) (forall ((x a) (xs (list a))) (=> (elem x xs) (exists ((n Nat)) (= x (at xs n)))))))'

test('structural index witnesses preserve TIP evaluation at random goals and function arguments', () => {
  for (const ints of [false, true]) {
    const lookup = ints ? `(declare-const undefined (par (a) a))
      (define-fun-rec at (par (a) (((xs (list a)) (n Int)) a))
        (match xs
          ((nil (_ undefined a))
           ((cons h t)
            (ite (= n 0) h (ite (> n 0) (at t (- n 1)) (_ undefined a)))))))` : LOOKUP
    const text = `${NAT} ${LIST} ${ELEM} ${lookup} ${ints ? INDEX_GOAL.replaceAll('Nat', 'Int') : INDEX_GOAL}`
    const original = parseTip(text), count = original.funs.size, tr = translate(original, 'index')
    expect(original.funs.size).toBe(count)
    expect(tr.tip.funs.size).toBe(count + 1)
    expect(tr.changes).toEqual([])
    expect(tr.some?.witnesses.length).toBe(1)
    const p = programOf([tr.law])
    for (const seed of [3, 17, 91]) {
      for (const s of samples(tr.law.vars, p.params, 150, seed)) {
        const globals = new Map(tr.params.filter(x => x.const).map(x => [x.tip, x.eval(s.params)]))
        const env = new Map(tr.vars.map(x => [x.tip, tr.toTip(s.env.get(x.gdp)!, x.ty)]))
        expect(evaluate(tr.tip, tr.goal, env, undefined, globals)).toBe(evalY(tr.law.holds, s.env, s.params))
      }
      const rand = rng(seed)
      const f = tr.fns.find(f => f.tipName.startsWith('$indexWitness'))!
      for (let i = 0; i < 100; i++) {
        const fn = f.callable.fn, vals = fn.params.map(q => randomValue(q.sort, rand, 1 + i % 7))
        const names = vals.map((_, j) => `$arg${j}`)
        const got = evalX({op: 'call', fn: fn.name, args: names.map(name => ({op: 'var', name}))}, new Map(names.map((n, j) => [n, vals[j]!])), {})
        const env = new Map(names.map((n, j) => [n, tr.toTip(vals[j]!, f.argTys[j]!)]))
        expect(sameV(tr.toTip(got, f.retTy), evaluate(tr.tip, [f.tipName, ...names], env))).toBe(true)
      }
    }
  }
})

test('a structural index witness is proven by the kernel, not assumed', () => {
  const tr = translate(parseTip(`${NAT} ${LIST} ${ELEM} ${LOOKUP} ${INDEX_GOAL}`), 'index')
  const v = proveData(tr.some!.witnesses[0]!.law, {ms: 57000})
  expect(v.proven && v.checked).toBe(true)
  // A failed candidate is not an existential refutation. It stays unknown in solve.ts.
  const bad = translate(parseTip(`${NAT} ${LIST} (prove (par (a) (forall ((x a) (xs (list a))) (exists ((n Nat)) (and (= n Z) (= n (S Z)))))))`), 'impossible')
  expect(proveData(bad.law, {ms: 1000}).proven).toBe(false)
}, 120_000)

test('witness substitution is simultaneous and avoids let, match and lambda capture', () => {
  const sx = (s: string) => parseSx(s)[0]!
  expect(show(substituteWitnesses(sx('(= x y)'), new Map([['x', 'y'], ['y', '0']])))).toBe('(= y 0)')
  const source = sx('(and (= n 0) (let ((x 1)) (= n x)))')
  const result = substituteWitnesses(source, new Map([['n', 'x']]))
  const tip = parseTip('(prove true)')
  expect(evaluate(tip, result, new Map([['x', 0n]]))).toBe(false)
  const lam = substituteWitnesses(sx('(lambda ((x Int)) (+ n x))'), new Map([['n', 'x']]))
  expect(show(lam)).toBe('(lambda (($witnessBound0 Int)) (+ x $witnessBound0))')
  const match = substituteWitnesses(sx('(match xs (((cons x t) (= n x)) (nil false)))'), new Map([['n', 'x']]))
  expect(show(match)).toBe('(match xs (((cons $witnessBound0 t) (= x $witnessBound0)) (nil false)))')
  const shadowed = substituteWitnesses(sx('(let ((n n)) (= n 0))'), new Map([['n', 'x']]))
  expect(show(shadowed)).toBe('(let ((n x)) (= n 0))')
})

test('index synthesis uses datatype shape, field order and fresh names, not benchmark names', () => {
  const tip = parseTip('(declare-datatype Chain ((Stop) (Link (rest Chain) (entry Bool)))) (define-fun $indexWitness () Int 9) (prove (forall ((x Bool) (xs Chain)) (exists ((n Int)) (= n n))))')
  const tr = translate(tip, 'reversed')
  const f = tr.fns.find(f => f.tipName === '$indexWitness_')!
  expect(f).toBeDefined()
  const val: V = {c: 'Link', a: [{c: 'Link', a: [{c: 'Stop', a: []}, true]}, false]}
  expect(evaluate(tr.tip, [f.tipName, 'x', 'xs'], new Map<string, V>([['x', true], ['xs', val]]))).toBe(1n)
})

// The answer, as solve.ts gives it: proven, refuted (the counterexample breaks TIP's goal by TIP's evaluator), unknown.
function answer(text: string, ms = 4000): string {
  const tip = parseTip(text), tr = translate(tip, 'test')
  const v = proveData(tr.law, {ms})
  if (v.proven && v.checked) return 'proven'
  if (!v.counterexample) return 'unknown'
  for (const s of samples(tr.law.vars, programOf([tr.law]).params, 400, 7)) {
    if (evalY(tr.law.holds, s.env, s.params)) continue
    const env = new Map<string, V>(), consts = new Map(tr.params.filter(p => p.const).map(p => [p.tip, p.eval(s.params)]))
    for (const x of tr.vars) env.set(x.tip, tr.toTip(s.env.get(x.gdp)!, x.ty))
    for (const p of tr.params) env.set(p.tip, p.eval(s.params))
    return evaluate(tr.tip, tr.goal, env, undefined, consts) === false ? 'refuted' : 'not confirmed'
  }
  return 'not found again'
}

test('abstract sorts: the claim at every sort, proven or refuted as TIP states it', () => {
  // zip of an empty list of an uninterpreted sort (isaplanner/prop_46's shape), ++ associative at every sort
  expect(answer(`(declare-sort Any 0) ${LIST} ${APP} (prove (forall ((xs (list Any)) (ys (list Any)) (zs (list Any))) (= (++ (++ xs ys) zs) (++ xs (++ ys zs)))))`, 20000)).toBe('proven')
  // true at a sort of two elements, false at three; a goal's sort variable is such a sort
  expect(answer('(prove (par (a) (forall ((x a) (y a) (z a)) (or (= x y) (= y z) (= x z)))))')).toBe('refuted')
  expect(answer('(declare-sort S 0) (prove (forall ((x S) (y S)) (= x y)))')).toBe('refuted')
  // an uninterpreted constant is any element: not every element, not another constant
  expect(answer('(declare-sort S 0) (declare-const c S) (prove (forall ((x S)) (= x c)))')).toBe('refuted')
  expect(answer('(declare-sort S 0) (declare-const c S) (declare-const d S) (prove (= c d))')).toBe('refuted')
  // a default an out-of-range lookup returns (tip2015/list_elem's `undefined`), at a sort variable
  expect(answer(`${LIST} (declare-const undefined (par (a) a)) (define-fun-rec hd (par (a) (((x (list a))) a)) (match x ((nil (_ undefined a)) ((cons y z) y)))) (prove (par (a) (forall ((x a)) (= (hd (_ nil a)) x))))`)).toBe('refuted')
  // an uninterpreted function of a sort is any function: not injective
  expect(answer('(declare-sort S 0) (declare-fun g (S) S) (prove (forall ((x S) (y S)) (=> (= (g x) (g y)) (= x y))))')).toBe('refuted')
}, 120_000)

test('function variables into a list and lambdas: told apart, as TIP states them', () => {
  // return of the list monad (tip2015/list_return_1), and a wrong one: f x ++ f x
  expect(answer(`${LIST} ${APP} ${BIND} (prove (par (a b) (forall ((x a) (f (=> a (list b)))) (= (>>= (cons x (_ nil a)) f) (@ f x)))))`, 57000)).toBe('proven')
  expect(answer(`${LIST} ${APP} ${BIND} (prove (par (a b) (forall ((x a) (f (=> a (list b)))) (= (>>= (cons x (_ nil a)) f) (++ (@ f x) (@ f x))))))`)).toBe('refuted')
  // two function variables are two functions
  expect(answer(`${LIST} (prove (par (a b) (forall ((x a) (f (=> a (list b))) (g (=> a (list b)))) (= (@ f x) (@ g x)))))`)).toBe('refuted')
  // two lambdas, and one lambda at two captured values, are not mixed up
  expect(answer(`${NAT} ${LIST} ${MAP} (prove (forall ((x Nat) (xs (list Nat))) (= (map (lambda ((y Nat)) (S y)) (cons x xs)) (map (lambda ((y Nat)) (S (S y))) (cons x xs)))))`)).toBe('refuted')
  expect(answer(`${NAT} ${LIST} ${MAP} ${PLUS} (prove (forall ((n Nat) (m Nat) (x Nat)) (= (map (lambda ((y Nat)) (plus y n)) (cons x (_ nil Nat))) (map (lambda ((y Nat)) (plus y m)) (cons x (_ nil Nat))))))`)).toBe('refuted')
}, 180_000)

test('what stays outside is refused with its reason', () => {
  const why = (text: string) => { try { translate(parseTip(text), 'test'); return 'translated' } catch (e) { return e instanceof Unsupported ? e.message : `error: ${(e as Error).message}` } }
  expect(why('(declare-sort F 1) (prove (forall ((x (F Int))) (= x x)))')).toMatch(/an uninterpreted sort of 1 arguments/)
  // a function variable of a function, and one over the integers where Int is the integers
  expect(why(`${LIST} (prove (par (a) (forall ((f (=> (=> a a) a))) (= f f))))`)).toMatch(/function variable of sort/)
  expect(why('(prove (forall ((f (=> Int Int)) (x Int)) (= (@ f (- x 1)) (@ f (- x 1)))))')).toMatch(/integer/)
})

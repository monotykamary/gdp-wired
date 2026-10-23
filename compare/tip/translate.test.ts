// The TIP translation's abstract sorts, uninterpreted constants and function variables (translate.ts) on small
// problems: true ones proven; false ones a wrong encoding would prove refuted, each counterexample confirmed by TIP's own
// evaluator (tip.ts) on the goal as TIP states it; what stays outside refused with its reason.
import {expect, test} from 'bun:test'
import {Unsupported, type V, evaluate, parseTip} from './tip.ts'
import {translate} from './translate.ts'
import {evalY, programOf, proveData, samples} from '../../core/data.ts'

const LIST = '(declare-datatype list (par (a) ((nil) (cons (head a) (tail (list a))))))'
const NAT = '(declare-datatype Nat ((Z) (S (p Nat))))'
const APP = '(define-fun-rec ++ (par (a) (((x (list a)) (y (list a))) (list a))) (match x ((nil y) ((cons z xs) (cons z (++ xs y))))))'
const BIND = '(define-fun-rec >>= (par (a b) (((x (list a)) (y (=> a (list b)))) (list b))) (match x ((nil (_ nil b)) ((cons z xs) (++ (@ y z) (>>= xs y))))))'
const MAP = '(define-fun-rec map (par (a b) (((f (=> a b)) (x (list a))) (list b))) (match x ((nil (_ nil b)) ((cons y xs) (cons (@ f y) (map f xs))))))'
const PLUS = '(define-fun-rec plus ((x Nat) (y Nat)) Nat (match x ((Z y) ((S z) (S (plus z y))))))'

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
    return evaluate(tip, tr.goal, env, undefined, consts) === false ? 'refuted' : 'not confirmed'
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

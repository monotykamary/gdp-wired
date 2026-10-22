; A broken variant (gdp-wired research/frontier2): qexp x y 1 replaced by qexp y x 1 (base and exponent swapped), so the goal is false
; Property from "Productive Use of Failure in Inductive Proof",
; Andrew Ireland and Alan Bundy, JAR 1996
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(define-fun
  one
  () Nat (S Z))
(define-fun-rec
  +2
  ((x Nat) (y Nat)) Nat
  (match x
    ((Z y)
     ((S z) (S (+2 z y))))))
(define-fun-rec
  *2
  ((x Nat) (y Nat)) Nat
  (match x
    ((Z Z)
     ((S z) (+2 y (*2 z y))))))
(define-fun-rec
  exp
  ((x Nat) (y Nat)) Nat
  (match y
    ((Z (S Z))
     ((S n) (*2 x (exp x n))))))
(define-fun-rec
  qexp
  ((x Nat) (y Nat) (z Nat)) Nat
  (match y
    ((Z z)
     ((S n) (qexp x n (*2 x z))))))
(prove (forall ((x Nat) (y Nat)) (= (exp x y) (qexp y x one))))

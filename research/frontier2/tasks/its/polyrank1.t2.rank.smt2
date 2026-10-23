; polyrank1.t2's loop (l0 -> l1 -> l0, l1 only passes the values on): while x >= 1: x := x - y; y := y + 1.
; A multiphase ranking function of depth 2 (Ben-Amram and Genaim, 2017), f1 = 1 - y, f2 = x, which proves the loop
; terminates: f1 drops by at least 1 each turn; f2 drops by at least 1 minus f1 each turn; f2 >= 0 where the guard holds.
; Each check below is the negation of one condition: three unsat.
(declare-const x Int)
(declare-const y Int)
(declare-const xp Int)
(declare-const yp Int)
(define-fun turn () Bool (and (>= x 1) (= xp (- x y)) (= yp (+ y 1))))
(push 1)
(assert (and turn (not (>= (- (- 1 y) (- 1 yp)) 1))))
(check-sat)
(pop 1)
(push 1)
(assert (and turn (not (>= (+ (- x xp) (- 1 y)) 1))))
(check-sat)
(pop 1)
(push 1)
(assert (and turn (not (>= x 0))))
(check-sat)
(pop 1)

; s_split_01_000.broken.smt2 (the second counter from 4999) is satisfiable: inv(d, c) := (d <= 5000 and c = 4999) or
; (d >= 5000 and c = d - 1) holds at the start, is kept by the step and excludes the query. Each check is unsat.
(define-fun inv ((d Int) (c Int)) Bool (or (and (<= d 5000) (= c 4999)) (and (>= d 5000) (= c (- d 1)))))
(declare-const d Int) (declare-const c Int) (declare-const d1 Int) (declare-const c1 Int)
(push) (assert (and (= c 4999) (= d 0))) (assert (not (inv d c))) (check-sat) (pop)
(push) (assert (inv d c)) (assert (= c1 (ite (>= d 5000) (+ 1 c) c))) (assert (= d1 (+ 1 d))) (assert (not (inv d1 c1))) (check-sat) (pop)
(push) (assert (inv d c)) (assert (and (= d 10000) (= c d))) (check-sat) (pop)

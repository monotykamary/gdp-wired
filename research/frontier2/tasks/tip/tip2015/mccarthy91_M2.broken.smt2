; A broken variant (gdp-wired research/frontier2): n >= 101 replaced by n >= 100 (m 100 = 91), so the goal is false
(define-fun-rec
  m
  ((x Int)) Int (ite (> x 100) (- x 10) (m (m (+ x 11)))))
(prove (forall ((n Int)) (=> (>= n 100) (= (m n) (- n 10)))))

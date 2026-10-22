; A broken variant (gdp-wired research/frontier2): n <= 100 replaced by n <= 102 (m 102 = 92), so the goal is false
(define-fun-rec
  m
  ((x Int)) Int (ite (> x 100) (- x 10) (m (m (+ x 11)))))
(prove (forall ((n Int)) (=> (<= n 102) (= (m n) 91))))

(set-logic HORN)


(declare-fun |inv| ( Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (and (>= D (+ B (* (- 1) C)))
     (>= D (+ B (* (- 1) A)))
     (not (<= B A))
     (>= D (+ C (* (- 2) A) B)))
      )
      (inv A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (inv B C F A)
        (let ((a!1 (and (= D (ite (<= B F) (+ 1 B) (+ (- 1) B))) (= E D) (= B C))))
(let ((a!2 (or (and (= D B) (= E (+ (- 1) C)) (not (= B C))) a!1)))
  (and (= G (+ (- 1) A)) a!2 (not (= C F)))))
      )
      (inv D E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (inv A B C D)
        (and (<= D 0) (not (= B C)))
      )
      false
    )
  )
)

(check-sat)
(exit)

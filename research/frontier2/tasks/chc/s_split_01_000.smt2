(set-logic HORN)


(declare-fun |inv| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (and (= A 5000) (= B 0))
      )
      (inv B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (inv D C)
        (and (= A (ite (>= D 5000) (+ 1 C) C)) (= B (+ 1 D)))
      )
      (inv B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (inv A B)
        (and (= A 10000) (= B A))
      )
      false
    )
  )
)

(check-sat)
(exit)

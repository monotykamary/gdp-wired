(set-logic HORN)


(declare-fun |INV_MAIN_42| ( Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (and (= D 0) (= C F) (= B 0) (= A 1) (= E 0))
      )
      (INV_MAIN_42 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (INV_MAIN_42 G H C I J F)
        (and (= I (+ (- 1) D))
     (= H (+ (- 2) B))
     (= G (+ (- 1) A))
     (>= (+ F (* (- 1) I)) 1)
     (>= C G)
     (= J (+ (- 2) E)))
      )
      (INV_MAIN_42 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_42 G H C D E F)
        (let ((a!1 (not (>= (+ F (* (- 1) D)) 1))))
  (and (= G (+ (- 1) A)) a!1 (>= C G) (= H (+ (- 2) B))))
      )
      (INV_MAIN_42 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (INV_MAIN_42 A B C G H F)
        (and (= G (+ (- 1) D))
     (>= (+ F (* (- 1) G)) 1)
     (not (>= C A))
     (= H (+ (- 2) E)))
      )
      (INV_MAIN_42 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (INV_MAIN_42 F A E D B C)
        (let ((a!1 (not (>= (+ C (* (- 1) D)) 1))))
  (and a!1 (not (>= E F)) (not (= A B))))
      )
      false
    )
  )
)

(check-sat)
(exit)

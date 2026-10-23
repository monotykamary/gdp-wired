(set-logic HORN)


(declare-fun |state| ( Bool Bool Bool Bool Int Int ) Bool)

(assert
  (forall ( (A Bool) (B Int) (C Int) (D Bool) (E Bool) (F Bool) ) 
    (=>
      (and
        (and (= F true) (not E) (not D) (not A))
      )
      (state A F E D B C)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Int) (G Int) (H Int) (I Int) (J Bool) (K Bool) (L Bool) ) 
    (=>
      (and
        (state A L K J G I)
        (let ((a!1 (and (not E) D (not C) (not B) (= G F) (= I H)))
      (a!2 (and (not E) D (not C) B (= I H) (= (+ G (* (- 1) F)) (- 1))))
      (a!3 (and E (not D) (not C) B (= G F) (= I H)))
      (a!4 (and (not E) (not D) (not C) (not B) (= G F) (= I H))))
  (and (or J
           (not K)
           (not A)
           (not L)
           (not (<= G I))
           (and E (not D) (not C) (not B) (= G F) (= I H)))
       (or A J L (not K) (not (<= I G)) (and (not E) D C B (= G F) (= I H)))
       (or A J L (not K) (<= I G) (and (not E) D C (not B) (= G F) (= I H)))
       (or J K L (not A) (<= I 0) a!1)
       (or J
           K
           L
           (not A)
           (not (<= I 0))
           (and (not E) (not D) C B (= G F) (= I H)))
       (or A J (not K) (not L) a!2)
       (or A K L (not J) (and E (not D) C (not B) (= G F) (= I H)))
       (or K L (not J) (not A) a!3)
       (or J L (not K) (not A) a!1)
       (or A J K L a!4)
       (or A K (not J) (not L) a!4)
       (or J K (not A) (not L) a!4)
       (or A J K (not L) (and (not E) (not D) (not C) B (= F 0) (= I H)))
       (or J (not K) (not A) (not L) (<= G I) a!3)))
      )
      (state B C D E F H)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Bool) (E Bool) (F Bool) ) 
    (=>
      (and
        (state A F E D B C)
        (and (not F) (not E) (= D true) (= A true))
      )
      false
    )
  )
)

(check-sat)
(exit)

(set-logic HORN)


(declare-fun |state| ( Bool Bool Bool Bool Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Bool) (F Bool) ) 
    (=>
      (and
        (and (= E true) (not D) (not C) (not F))
      )
      (state F E D C A B)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Int) (F Int) (G Int) (H Int) (I Bool) (J Bool) (K Bool) (L Bool) ) 
    (=>
      (and
        (state L K J I F H)
        (let ((a!1 (and (not D) C (not B) (not A) (= H G) (= (+ F (* (- 1) E) H) 0)))
      (a!2 (and (not D) C (not B) A (= F E) (= (+ H (* (- 1) G)) (- 1))))
      (a!3 (and D (not C) (not B) A (= F E) (= H G)))
      (a!4 (and (not D) (not C) (not B) (not A) (= F E) (= H G))))
  (and (or I K (not J) (not L) (<= H 0) (and (not D) C B A (= F E) (= H G)))
       (or I
           J
           K
           (not L)
           (not (<= 0 F))
           (and (not D) C B (not A) (= F E) (= H G)))
       (or I J K (not L) (<= 0 F) (and (not D) (not C) B A (= F E) (= H G)))
       (or I J (not L) (not K) a!1)
       (or I K L (not J) a!2)
       (or J L (not I) (not K) a!3)
       (or I
           (not J)
           (not L)
           (not K)
           (and D (not C) (not B) (not A) (= F E) (= H G)))
       (or I L (not J) (not K) (and (not D) (not C) B (not A) (= F E) (= H G)))
       (or I J K L a!4)
       (or J K L (not I) a!4)
       (or I J L (not K) (and (not D) (not C) B (not A) (= E (- 50)) (= H G)))
       (or I K (not J) (not L) (not (<= H 0)) a!3)))
      )
      (state B A C D E G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Bool) (F Bool) ) 
    (=>
      (and
        (state F E D C A B)
        (and (= E true) (not D) (= C true) (not F))
      )
      false
    )
  )
)

(check-sat)
(exit)

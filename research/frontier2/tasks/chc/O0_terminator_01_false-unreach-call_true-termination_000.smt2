(set-logic HORN)


(declare-fun |main@entry| ( Int ) Bool)
(declare-fun |main@_bb| ( Int ) Bool)
(declare-fun |main@verifier.error.split| ( ) Bool)

(assert
  (forall ( (A Int) ) 
    (=>
      (and
        true
      )
      (main@entry A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F Int) (G Int) ) 
    (=>
      (and
        (main@entry B)
        (and (or (not E) (not D) (= F C))
     (or (not E) (not D) (= G F))
     (or (not D) (and E D))
     (= D true)
     (= A B))
      )
      (main@_bb G)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Int) (E Bool) (F Bool) (G Int) (H Int) ) 
    (=>
      (and
        (main@_bb C)
        (and (or (not F) B (not A))
     (or (not F) (not E) (= G D))
     (or (not F) (not E) (= H G))
     (or (not E) (and F E))
     (or (not F) (= D (+ 1 C)))
     (or (not F) (and F A))
     (= E true)
     (not (= (<= 100 C) B)))
      )
      (main@_bb H)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) ) 
    (=>
      (and
        (main@_bb A)
        (and (or (not E) (not C) (not B))
     (or (not F) (and E F))
     (or (not J) (and I J))
     (or (not K) (and K J))
     (or (not E) (and E B))
     (or (not E) (not D))
     (or (not H) (and H F))
     (or (not H) G)
     (or (not I) (and I H))
     (= K true)
     (not (= (<= 100 A) C)))
      )
      main@verifier.error.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@verifier.error.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)

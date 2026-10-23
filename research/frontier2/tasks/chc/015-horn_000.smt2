(set-logic HORN)


(declare-fun |REC_f_| ( Int Int ) Bool)
(declare-fun |REC_f_f| ( Int Int Int Int ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |REC__f| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (v_4 Int) ) 
    (=>
      (and
        (REC__f D C)
        (and (not (>= C 0)) (not (<= B 1)) (<= A 1) (= B (+ 1 D)) (= v_4 A))
      )
      (REC_f_f A v_4 B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (v_5 Int) ) 
    (=>
      (and
        (REC__f E D)
        (and (= B (+ 1 E)) (>= D 0) (<= A 1) (not (<= B 1)) (= (+ B D) C) (= v_5 A))
      )
      (REC_f_f A v_5 B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (v_2 Int) (v_3 Int) ) 
    (=>
      (and
        (and (<= A 1) (<= B 1) (= v_2 A) (= v_3 B))
      )
      (REC_f_f A v_2 B v_3)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (REC_f_f F E G D)
        (and (= A (+ 1 F))
     (= C (+ 1 G))
     (not (>= D 0))
     (not (<= A 1))
     (not (<= C 1))
     (= (+ A E) B))
      )
      (REC_f_f A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (REC_f_f G E H F)
        (and (= (+ C F) D)
     (= A (+ 1 G))
     (= C (+ 1 H))
     (>= F 0)
     (not (<= A 1))
     (not (<= C 1))
     (= (+ A E) B))
      )
      (REC_f_f A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (v_5 Int) ) 
    (=>
      (and
        (REC_f_ E D)
        (and (= A (+ 1 E)) (not (<= A 1)) (<= C 1) (= (+ A D) B) (= v_5 C))
      )
      (REC_f_f A B C v_5)
    )
  )
)
(assert
  (forall ( (A Int) (v_1 Int) ) 
    (=>
      (and
        (and (<= A 1) (= v_1 A))
      )
      (REC_f_ A v_1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (REC_f_ D C)
        (and (= A (+ 1 D)) (not (<= A 1)) (= (+ A C) B))
      )
      (REC_f_ A B)
    )
  )
)
(assert
  (forall ( (A Int) (v_1 Int) ) 
    (=>
      (and
        (and (<= A 1) (= v_1 A))
      )
      (REC__f A v_1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (REC__f D C)
        (and (= A (+ 1 D)) (>= C 0) (not (<= A 1)) (= (+ A C) B))
      )
      (REC__f A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (REC__f C B)
        (and (not (>= B 0)) (not (<= A 1)) (= A (+ 1 C)))
      )
      (REC__f A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (REC_f_ D B)
        (and (= A (+ 1 D)) (= A C) (<= C 1) (not (<= A 1)) (not (= (+ A B) C)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (REC_f_f E B F D)
        (and (= A (+ 1 E))
     (= A C)
     (= C (+ 1 F))
     (>= D 0)
     (not (<= A 1))
     (not (<= C 1))
     (not (= (+ A B) (+ C D))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (REC_f_f D B F C)
        (and (= A (+ 1 D))
     (= A E)
     (= E (+ 1 F))
     (not (>= C 0))
     (not (<= A 1))
     (not (<= E 1))
     (not (= (+ A B) C)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (REC__f D C)
        (and (not (= A (+ B C))) (= A B) (>= C 0) (not (<= B 1)) (<= A 1) (= B (+ 1 D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (REC__f D B)
        (and (= A C) (not (= A B)) (not (>= B 0)) (not (<= C 1)) (<= A 1) (= C (+ 1 D)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        CHC_COMP_FALSE
      )
      false
    )
  )
)

(check-sat)
(exit)

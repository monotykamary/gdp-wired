(set-logic HORN)


(declare-fun |state| ( Int Int Bool Bool Int Int Int Int Bool Int Int Int Int Bool Bool Int Int Bool Bool Bool Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Bool) (L Int) (M Int) (N Int) (O Bool) (P Bool) (Q Bool) (R Int) (S Bool) (T Bool) (U Int) (V Int) (W Bool) ) 
    (=>
      (and
        (let ((a!1 (and (or T (not (<= V U))) (or W (not (<= A F))) (<= 1 A) (<= 1 V))))
  (and (= M U)
       (= H G)
       (= H A)
       (= J V)
       (= J I)
       (= L 0)
       (= L F)
       (= N 0)
       (= N R)
       (= (or (not P) K) O)
       (= B a!1)
       (= B Q)
       (= Q P)
       (= K true)
       (= M 0)))
      )
      (state N R B Q M U L F P J V H A K O I G W T S C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) (E Int) (F Bool) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Bool) (O Int) (P Int) (Q Int) (R Bool) (S Bool) (T Bool) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Bool) (B1 Bool) (C1 Int) (D1 Bool) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Bool) (K1 Int) (L1 Bool) (M1 Int) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Bool) (R1 Int) (S1 Int) (T1 Bool) ) 
    (=>
      (and
        (state Q U B T P R1 O I S M S1 K A N R L J T1 Q1 D1 C D E)
        (let ((a!1 (not (<= 0 (+ Z (* (- 1) Y) (* (- 1) X)))))
      (a!2 (and T
                (or J1 (not (<= X K1)))
                (or A1 (not (<= Y I1)))
                (<= 1 Y)
                (<= 1 X)))
      (a!3 (or (not T1) (= (+ R1 (* (- 1) F1)) (- 1))))
      (a!4 (or (not D1) (= (+ U (* (- 1) E1)) (- 1))))
      (a!5 (or (not D1) (= (+ I (* (- 1) C1)) (- 1)))))
  (and (= X V)
       (= Y W)
       (= Z M1)
       (= G1 C1)
       (= H1 F1)
       (= I1 H1)
       (= K1 G1)
       (= M1 E1)
       (= Q U)
       (= P R1)
       (= O I)
       (= M S1)
       (= K A)
       (= A V)
       (= (or N (not S)) R)
       (= (or (not O1) B1) N1)
       (= B1 (or A1 a!1))
       (= L1 a!2)
       (= T S)
       (= P1 L1)
       (= P1 O1)
       (= B T)
       a!3
       (or T1 (= F1 0))
       a!4
       a!5
       (or D1 (= C1 0))
       (or D1 (= E1 0))
       (= S1 W)))
      )
      (state M1 Z L1 P1 H1 I1 G1 K1 O1 W Y V X B1 N1 H G J1 A1 F C1 F1 E1)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Bool) (L Int) (M Int) (N Int) (O Bool) (P Bool) (Q Bool) (R Int) (S Bool) (T Bool) (U Int) (V Int) (W Bool) ) 
    (=>
      (and
        (state N R B Q M U L F P J V H A K O I G W T S C D E)
        (not O)
      )
      false
    )
  )
)

(check-sat)
(exit)

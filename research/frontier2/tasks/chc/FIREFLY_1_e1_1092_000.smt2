(set-logic HORN)


(declare-fun |state| ( Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Int Int Int Int Int Int Bool Int Int Int Int Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool Bool Int Int Int Bool Bool Bool Bool Bool ) Bool)

(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Int) (F Bool) (G Int) (H Bool) (I Int) (J Bool) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Bool) (S Bool) (T Int) (U Int) (V Bool) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Bool) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Bool) (I1 Int) (J1 Int) (K1 Int) (L1 Bool) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Bool) (R1 Int) (S1 Int) (T1 Int) (U1 Bool) (V1 Bool) (W1 Int) (X1 Int) (Y1 Bool) (Z1 Int) (A2 Bool) (B2 Int) (C2 Bool) (D2 Int) (E2 Bool) (F2 Int) (G2 Bool) (H2 Int) (I2 Int) (J2 Int) (K2 Int) (L2 Int) (M2 Bool) (N2 Int) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Bool) (T2 Int) (U2 Int) (V2 Bool) (W2 Bool) (X2 Int) (Y2 Int) ) 
    (=>
      (and
        (let ((a!1 (= S (and R (not (<= K 0)))))
      (a!2 (= (or (and (not L1)
                       (not S2)
                       (not V2)
                       (not A)
                       (not V)
                       (not B1)
                       (not H1)
                       (not Q1))
                  (and (not L1)
                       (not S2)
                       (not V2)
                       (not A)
                       (not V)
                       (not B1)
                       (not H1)
                       Q1)
                  (and (not L1)
                       (not S2)
                       (not V2)
                       (not A)
                       (not V)
                       (not B1)
                       H1
                       (not Q1))
                  (and (not L1)
                       (not S2)
                       (not V2)
                       (not A)
                       (not V)
                       B1
                       (not H1)
                       (not Q1))
                  (and (not L1)
                       (not S2)
                       (not V2)
                       (not A)
                       V
                       (not B1)
                       (not H1)
                       (not Q1))
                  (and (not L1)
                       (not S2)
                       (not V2)
                       A
                       (not V)
                       (not B1)
                       (not H1)
                       (not Q1))
                  (and (not L1)
                       (not S2)
                       V2
                       (not A)
                       (not V)
                       (not B1)
                       (not H1)
                       (not Q1))
                  (and (not L1)
                       S2
                       (not V2)
                       (not A)
                       (not V)
                       (not B1)
                       (not H1)
                       (not Q1))
                  (and L1
                       (not S2)
                       (not V2)
                       (not A)
                       (not V)
                       (not B1)
                       (not H1)
                       (not Q1)))
              R)))
  (and (= (or (not V1) W2) U1)
       (= M2 V1)
       a!1
       (= S M2)
       (= L2 K2)
       (= B2 Z1)
       (= Q 0)
       (= Q L2)
       (= N M)
       (= M B2)
       (= L N)
       (= L K)
       (= O 0)
       (= O X1)
       (= P 0)
       (= P J2)
       (= X1 W1)
       (= J2 I2)
       (or (= P1 A1) Q1)
       (or (not Q1) (= A1 R1))
       (or (not Q1) (= G1 I))
       (or (= G1 U2) Q1)
       (or (not H1) (= O2 I1))
       (or (not H1) (= D1 J1))
       (or (= G1 O2) H1)
       (or (= K1 D1) H1)
       (or (not B1) (= F2 E1))
       (or (not B1) (= R2 C1))
       (or (not B1) (= Z G))
       (or (= A1 R2) B1)
       (or B1 (= D1 Z))
       (or (= F1 F2) B1)
       (or (not V) (= U W))
       (or (= U T) V)
       (or (not V) (= Y X))
       (or (= Z Y) V)
       (or (not J) (= X2 0))
       (or (not H) (= I 1))
       (or (not F) (= G 0))
       (or (not A) (= E D))
       (or (not A) (= Y2 X2))
       (or (not A) (= C B))
       (or (not V2) (= P1 S1))
       (or V2 (= P1 C))
       (or (not V2) (= U2 T2))
       (or V2 (= O1 E))
       (or (not V2) (= O1 T1))
       (or S2 (= F2 D2))
       (or S2 (= R2 T))
       (or S2 (= O2 N2))
       (or (not S2) (= N2 Q2))
       (or (not S2) (= T P2))
       (or (not S2) (= D2 H2))
       (or (not L1) (= F1 N1))
       (or (not L1) (= K1 M1))
       (or L1 (= K1 Y2))
       (or L1 (= O1 F1))
       (= W2 true)
       a!2))
      )
      (state S
       M2
       V
       S2
       B1
       H1
       L1
       Q1
       V2
       A
       R
       L
       N
       Q
       L2
       P
       J2
       O
       X1
       M
       B2
       V1
       K2
       I2
       W1
       Z1
       W2
       U1
       O1
       E
       T1
       P1
       S1
       C
       G1
       U2
       I
       A1
       R1
       F1
       N1
       K1
       M1
       Y2
       D1
       J1
       O2
       I1
       F2
       E1
       Z
       G
       R2
       C1
       Y
       X
       U
       W
       T
       D2
       H2
       N2
       Q2
       P2
       K
       X2
       J
       H
       F
       D
       B
       T2
       Y1
       A2
       C2
       E2
       G2)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Int) (F Bool) (G Int) (H Bool) (I Int) (J Bool) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Bool) (S Bool) (T Int) (U Int) (V Bool) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Bool) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Bool) (I1 Int) (J1 Int) (K1 Int) (L1 Bool) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Bool) (R1 Int) (S1 Int) (T1 Int) (U1 Bool) (V1 Bool) (W1 Int) (X1 Int) (Y1 Bool) (Z1 Int) (A2 Bool) (B2 Int) (C2 Bool) (D2 Int) (E2 Bool) (F2 Int) (G2 Bool) (H2 Int) (I2 Int) (J2 Int) (K2 Int) (L2 Int) (M2 Bool) (N2 Int) (O2 Int) (P2 Int) (Q2 Int) (R2 Bool) (S2 Int) (T2 Bool) (U2 Int) (V2 Int) (W2 Bool) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Bool) (E3 Int) (F3 Bool) (G3 Int) (H3 Bool) (I3 Int) (J3 Bool) (K3 Int) (L3 Bool) (M3 Bool) (N3 Int) (O3 Int) (P3 Bool) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Bool) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Int) (D4 Int) (E4 Int) (F4 Int) (G4 Int) (H4 Int) (I4 Int) (J4 Int) (K4 Bool) (L4 Bool) (M4 Int) (N4 Int) (O4 Bool) (P4 Int) (Q4 Int) (R4 Bool) (S4 Int) (T4 Int) (U4 Bool) (V4 Int) (W4 Int) (X4 Int) (Y4 Bool) (Z4 Int) (A5 Bool) (B5 Int) (C5 Int) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Int) (H5 Int) (I5 Int) (J5 Int) (K5 Bool) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Bool) (S5 Int) (T5 Int) (U5 Bool) (V5 Bool) (W5 Int) (X5 Int) ) 
    (=>
      (and
        (state S
       M2
       V
       R5
       B1
       H1
       L1
       Q1
       U5
       A
       R
       L
       N
       Q
       L2
       P
       J2
       O
       X1
       M
       B2
       V1
       K2
       I2
       W1
       Z1
       V5
       U1
       O1
       E
       T1
       P1
       S1
       C
       G1
       T5
       I
       A1
       R1
       F1
       N1
       K1
       M1
       X5
       D1
       J1
       N5
       I1
       F2
       E1
       Z
       G
       Q5
       C1
       Y
       X
       U
       W
       T
       D2
       H2
       M5
       P5
       O5
       K
       W5
       J
       H
       F
       D
       B
       S5
       Y1
       A2
       C2
       E2
       G2)
        (let ((a!1 (= (or (and (not D5)
                       (not A5)
                       (not Y4)
                       (not U4)
                       (not R4)
                       (not O4)
                       (not W2)
                       (not T2))
                  (and (not D5)
                       (not A5)
                       (not Y4)
                       (not U4)
                       (not R4)
                       (not O4)
                       (not W2)
                       T2)
                  (and (not D5)
                       (not A5)
                       (not Y4)
                       (not U4)
                       (not R4)
                       (not O4)
                       W2
                       (not T2))
                  (and (not D5)
                       (not A5)
                       (not Y4)
                       (not U4)
                       (not R4)
                       O4
                       (not W2)
                       (not T2))
                  (and (not D5)
                       (not A5)
                       (not Y4)
                       (not U4)
                       R4
                       (not O4)
                       (not W2)
                       (not T2))
                  (and (not D5)
                       (not A5)
                       (not Y4)
                       U4
                       (not R4)
                       (not O4)
                       (not W2)
                       (not T2))
                  (and (not D5)
                       (not A5)
                       Y4
                       (not U4)
                       (not R4)
                       (not O4)
                       (not W2)
                       (not T2))
                  (and (not D5)
                       A5
                       (not Y4)
                       (not U4)
                       (not R4)
                       (not O4)
                       (not W2)
                       (not T2))
                  (and D5
                       (not A5)
                       (not Y4)
                       (not U4)
                       (not R4)
                       (not O4)
                       (not W2)
                       (not T2)))
              K4))
      (a!2 (= (or (and (not A)
                       (not V)
                       (not B1)
                       (not H1)
                       (not L1)
                       (not Q1)
                       (not R5)
                       (not U5))
                  (and (not A)
                       (not V)
                       (not B1)
                       (not H1)
                       (not L1)
                       (not Q1)
                       (not R5)
                       U5)
                  (and (not A)
                       (not V)
                       (not B1)
                       (not H1)
                       (not L1)
                       (not Q1)
                       R5
                       (not U5))
                  (and (not A)
                       (not V)
                       (not B1)
                       (not H1)
                       (not L1)
                       Q1
                       (not R5)
                       (not U5))
                  (and (not A)
                       (not V)
                       (not B1)
                       (not H1)
                       L1
                       (not Q1)
                       (not R5)
                       (not U5))
                  (and (not A)
                       (not V)
                       (not B1)
                       H1
                       (not L1)
                       (not Q1)
                       (not R5)
                       (not U5))
                  (and (not A)
                       (not V)
                       B1
                       (not H1)
                       (not L1)
                       (not Q1)
                       (not R5)
                       (not U5))
                  (and (not A)
                       V
                       (not B1)
                       (not H1)
                       (not L1)
                       (not Q1)
                       (not R5)
                       (not U5))
                  (and A
                       (not V)
                       (not B1)
                       (not H1)
                       (not L1)
                       (not Q1)
                       (not R5)
                       (not U5)))
              R))
      (a!3 (and (<= 1 B2) (= X1 0) (= J2 0) (= L2 0)))
      (a!4 (= (and (<= 1 B2) (<= 1 (+ L2 J2))) H3))
      (a!5 (= R2
              (= (+ K2
                    I2
                    W1
                    Z1
                    (* (- 1) Q2)
                    (* (- 1) P2)
                    (* (- 1) O2)
                    (* (- 1) N2))
                 0)))
      (a!6 (= M3 (and (<= 1 B2) (<= 1 (+ L2 J2)))))
      (a!7 (= L4 (and M2 K4 (not (<= J4 0)))))
      (a!8 (or (not D3) (= (+ J2 (* (- 1) R3)) (- 1))))
      (a!9 (or (not D3) (= (+ B2 (* (- 1) C3)) 1)))
      (a!10 (or (not F3) (= (+ L2 (* (- 1) X3)) (- 2))))
      (a!11 (or (not F3) (= (+ B2 (* (- 1) E3)) 1)))
      (a!12 (or (not F3) (= (+ X1 (* (- 1) N3)) 1)))
      (a!13 (or (not H3) (= (+ L2 J2 (* (- 1) W3)) (- 2))))
      (a!14 (or (not H3) (= (+ B2 (* (- 1) G3)) 1)))
      (a!15 (or (not J3) (= (+ B2 (* (- 1) I3)) 1)))
      (a!16 (or (not L3) (= (+ L2 (* (- 1) Z3)) (- 2))))
      (a!17 (or (not L3) (= (+ B2 (* (- 1) K3)) 1)))
      (a!18 (or (not L3) (= (+ X1 (* (- 1) U2)) 1)))
      (a!19 (or (not M3) (= (+ L2 J2 (* (- 1) A3)) (- 1))))
      (a!20 (or (not M3) (= (+ B2 (* (- 1) X2)) 1)))
      (a!21 (or (not P3) (= (+ J2 (* (- 1) T3)) 1)))
      (a!22 (or (not P3) (= (+ X1 (* (- 1) O3)) (- 1))))
      (a!23 (or (not V3) (= (+ J2 (* (- 1) U3)) (- 1)))))
  (and a!1
       a!2
       (= (or (not F5) R2) E5)
       (= (or (not V1) V5) U1)
       (= a!3 D3)
       a!4
       (= (and (<= 1 X1) (<= 1 B2)) F3)
       (= (and (<= 1 X1) (<= 1 B2)) L3)
       a!5
       (= J3 a!3)
       a!6
       (= V3 (= L2 1))
       a!7
       (= K5 L4)
       (= K5 F5)
       (= M2 V1)
       (= S M2)
       (= C4 B4)
       (= E4 D4)
       (= G4 F4)
       (= I4 H4)
       (= G5 N2)
       (= G5 C4)
       (= H5 O2)
       (= H5 E4)
       (= I5 P2)
       (= I5 G4)
       (= J5 Q2)
       (= J5 I4)
       (= L5 A4)
       (= L2 K2)
       (= J2 I2)
       (= B2 Z1)
       (= X1 W1)
       (= Q L2)
       (= P J2)
       (= O X1)
       (= N A4)
       (= M B2)
       (= L N)
       (or (not U5) (= P1 S1))
       (or U5 (= P1 C))
       (or (not U5) (= O1 T1))
       (or U5 (= O1 E))
       (or R5 (= Q5 T))
       (or R5 (= N5 M5))
       (or (not R5) (= M5 P5))
       (or R5 (= F2 D2))
       (or (not R5) (= D2 H2))
       (or (not R5) (= T O5))
       (or (not T2) (= S2 U2))
       (or T2 (= B3 B5))
       (or (not T2) (= K3 C5))
       (or (not T2) (= B5 Z3))
       (or T2 (= C5 V2))
       (or T2 (= X1 S2))
       (or (not W2) (= V2 X2))
       (or (not W2) (= Z2 Y2))
       (or (not W2) (= B3 A3))
       (or W2 (= L2 B3))
       (or W2 (= J2 Z2))
       (or W2 (= B2 V2))
       a!8
       a!9
       (or D3 (= J2 R3))
       (or D3 (= B2 C3))
       a!10
       a!11
       a!12
       (or F3 (= L2 X3))
       (or F3 (= B2 E3))
       (or F3 (= X1 N3))
       a!13
       a!14
       (or (not H3) (= S3 0))
       (or H3 (= L2 W3))
       (or H3 (= J2 S3))
       (or H3 (= B2 G3))
       a!15
       (or (not J3) (= Q3 1))
       (or J3 (= B2 I3))
       (or J3 (= X1 Q3))
       a!16
       a!17
       a!18
       (or L3 (= L2 Z3))
       (or L3 (= B2 K3))
       (or L3 (= X1 U2))
       a!19
       a!20
       (or (not M3) (= Y2 0))
       (or M3 (= L2 A3))
       (or M3 (= J2 Y2))
       (or M3 (= B2 X2))
       a!21
       a!22
       (or P3 (= J2 T3))
       (or P3 (= X1 O3))
       a!23
       (or (not V3) (= Y3 0))
       (or V3 (= L2 Y3))
       (or V3 (= J2 U3))
       (or (not O4) (= D4 N3))
       (or (not O4) (= H4 X3))
       (or (not O4) (= M4 E3))
       (or O4 (= N4 M4))
       (or O4 (= P4 D4))
       (or O4 (= Q4 H4))
       (or (not R4) (= C3 B4))
       (or R4 (= B4 M4))
       (or (not R4) (= F4 R3))
       (or R4 (= S4 F4))
       (or (not U4) (= G3 N4))
       (or (not U4) (= Q4 W3))
       (or (not U4) (= S4 S3))
       (or U4 (= T4 N4))
       (or U4 (= V4 S4))
       (or U4 (= W4 Q4))
       (or (not Y4) (= O3 P4))
       (or (not Y4) (= V4 T3))
       (or Y4 (= X4 P4))
       (or Y4 (= Z4 V4))
       (or (not A5) (= U3 Z4))
       (or (not A5) (= W4 Y3))
       (or A5 (= Z4 Z2))
       (or A5 (= B5 W4))
       (or D5 (= S2 X4))
       (or (not D5) (= I3 T4))
       (or (not D5) (= X4 Q3))
       (or D5 (= C5 T4))
       (or Q1 (= P1 A1))
       (or Q1 (= G1 T5))
       (or (not Q1) (= G1 I))
       (or (not Q1) (= A1 R1))
       (or L1 (= O1 F1))
       (or L1 (= K1 X5))
       (or (not L1) (= K1 M1))
       (or (not L1) (= F1 N1))
       (or (not H1) (= N5 I1))
       (or H1 (= K1 D1))
       (or H1 (= G1 N5))
       (or (not H1) (= D1 J1))
       (or (not B1) (= Q5 C1))
       (or (not B1) (= F2 E1))
       (or B1 (= F1 F2))
       (or B1 (= D1 Z))
       (or B1 (= A1 Q5))
       (or (not B1) (= Z G))
       (or V (= Z Y))
       (or (not V) (= Y X))
       (or (not V) (= U W))
       (or V (= U T))
       (= (<= 1 J2) P3)))
      )
      (state L4
       K5
       R4
       O4
       U4
       Y4
       A5
       D5
       T2
       W2
       K4
       A4
       L5
       I4
       J5
       G4
       I5
       E4
       H5
       C4
       G5
       F5
       Q2
       P2
       O2
       N2
       R2
       E5
       B5
       B3
       Z3
       C5
       K3
       V2
       X4
       S2
       Q3
       T4
       I3
       W4
       Y3
       Z4
       U3
       Z2
       V4
       T3
       P4
       O3
       Q4
       W3
       S4
       S3
       N4
       G3
       F4
       R3
       B4
       C3
       M4
       H4
       X3
       D4
       N3
       E3
       J4
       Y2
       M3
       J3
       H3
       A3
       X2
       U2
       D3
       F3
       P3
       V3
       L3)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Int) (E Int) (F Bool) (G Int) (H Bool) (I Int) (J Bool) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Bool) (S Bool) (T Int) (U Int) (V Bool) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Bool) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Bool) (I1 Int) (J1 Int) (K1 Int) (L1 Bool) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Bool) (R1 Int) (S1 Int) (T1 Int) (U1 Bool) (V1 Bool) (W1 Int) (X1 Int) (Y1 Bool) (Z1 Int) (A2 Bool) (B2 Int) (C2 Bool) (D2 Int) (E2 Bool) (F2 Int) (G2 Bool) (H2 Int) (I2 Int) (J2 Int) (K2 Int) (L2 Int) (M2 Bool) (N2 Int) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Bool) (T2 Int) (U2 Int) (V2 Bool) (W2 Bool) (X2 Int) (Y2 Int) ) 
    (=>
      (and
        (state S
       M2
       V
       S2
       B1
       H1
       L1
       Q1
       V2
       A
       R
       L
       N
       Q
       L2
       P
       J2
       O
       X1
       M
       B2
       V1
       K2
       I2
       W1
       Z1
       W2
       U1
       O1
       E
       T1
       P1
       S1
       C
       G1
       U2
       I
       A1
       R1
       F1
       N1
       K1
       M1
       Y2
       D1
       J1
       O2
       I1
       F2
       E1
       Z
       G
       R2
       C1
       Y
       X
       U
       W
       T
       D2
       H2
       N2
       Q2
       P2
       K
       X2
       J
       H
       F
       D
       B
       T2
       Y1
       A2
       C2
       E2
       G2)
        (not U1)
      )
      false
    )
  )
)

(check-sat)
(exit)

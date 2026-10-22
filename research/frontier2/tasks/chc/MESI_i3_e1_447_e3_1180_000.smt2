(set-logic HORN)


(declare-fun |state| ( Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Bool Int Int Int Int Int Int Int Int Int Int Int Int Bool Int Bool Int Int Bool Bool Int Bool ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Bool) (G Int) (H Int) (I Bool) (J Int) (K Int) (L Int) (M Int) (N Bool) (O Bool) (P Bool) (Q Bool) (R Int) (S Int) (T Bool) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Bool) (E1 Int) (F1 Int) (G1 Bool) (H1 Int) (I1 Int) (J1 Int) (K1 Bool) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Bool) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Bool) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) ) 
    (=>
      (and
        (let ((a!1 (not (= (or (and T G1)
                       (and T S1)
                       (and Z1 S1)
                       (and Z1 G1)
                       (and T Z1)
                       (and G1 S1))
                   N))))
  (and (= (or (not Q) (<= 0 R)) P)
       (= D1 Q)
       (= O D1)
       (= O N)
       (= Z Y)
       (= J 0)
       (= J X)
       (= K 0)
       (= K Z)
       (= L 0)
       (= L A1)
       (= M 3)
       (= M C1)
       (= X W)
       (= A1 R)
       (= C1 B1)
       (or (= F1 S) S1)
       (or (not S1) (= F1 T1))
       (or (not S1) (= I1 U1))
       (or (= I1 U) S1)
       (or (= O1 M1) S1)
       (or (not S1) (= O1 V1))
       (or (= R1 V) S1)
       (or (not S1) (= R1 W1))
       (or (not G1) (= Q1 P1))
       (or (not G1) (= E1 D))
       (or (= F1 E1) G1)
       (or (not G1) (= H1 B))
       (or (= I1 H1) G1)
       (or (not G1) (= N1 J1))
       (or (= O1 N1) G1)
       (or (= R1 Q1) G1)
       (or (not I) (= C2 0))
       (or (not I) (= A2 0))
       (or (not I) (= X1 1))
       (or (not F) (= E 1))
       (or (not F) (= G 0))
       (or (not F) (= H 0))
       (or (not C) (= B 0))
       (or (not C) (= D 0))
       (or (not Z1) (= D2 C2))
       (or (not Z1) (= B2 A2))
       (or (not Z1) (= Y1 X1))
       (or (not Z1) (= A E2))
       (or T (= M1 D2))
       (or (not T) (= M1 H))
       (or T (= V A))
       (or (not T) (= V L1))
       (or T (= U Y1))
       (or (not T) (= U E))
       (or T (= S B2))
       (or (not T) (= S G))
       a!1))
      )
      (state O
       D1
       Z1
       T
       S1
       G1
       N
       M
       C1
       L
       A1
       K
       Z
       J
       X
       R1
       V
       W1
       O1
       M1
       V1
       I1
       U
       U1
       F1
       T1
       S
       Q1
       P1
       N1
       J1
       H1
       B
       E1
       D
       Q
       B1
       R
       Y
       W
       A
       L1
       D2
       H
       Y1
       E
       G
       B2
       P
       C2
       I
       A2
       X1
       F
       C
       E2
       K1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Bool) (G Int) (H Int) (I Bool) (J Int) (K Int) (L Int) (M Int) (N Bool) (O Bool) (P Bool) (Q Bool) (R Int) (S Int) (T Bool) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Bool) (E1 Int) (F1 Int) (G1 Bool) (H1 Int) (I1 Int) (J1 Int) (K1 Bool) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Bool) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Bool) (Z1 Int) (A2 Bool) (B2 Int) (C2 Bool) (D2 Int) (E2 Bool) (F2 Int) (G2 Int) (H2 Int) (I2 Int) (J2 Int) (K2 Int) (L2 Int) (M2 Int) (N2 Int) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Bool) (Z2 Bool) (A3 Bool) (B3 Bool) (C3 Int) (D3 Int) (E3 Bool) (F3 Int) (G3 Int) (H3 Int) (I3 Int) (J3 Int) (K3 Int) (L3 Int) (M3 Int) (N3 Int) (O3 Int) (P3 Bool) (Q3 Int) (R3 Bool) (S3 Int) (T3 Int) (U3 Int) (V3 Bool) (W3 Int) (X3 Int) (Y3 Int) (Z3 Bool) (A4 Int) (B4 Int) (C4 Int) (D4 Int) (E4 Bool) (F4 Int) (G4 Int) (H4 Int) (I4 Int) (J4 Int) ) 
    (=>
      (and
        (state O
       D1
       E4
       T
       S1
       G1
       N
       M
       C1
       L
       A1
       K
       Z
       J
       X
       R1
       V
       W1
       O1
       M1
       V1
       I1
       U
       U1
       F1
       T1
       S
       Q1
       P1
       N1
       J1
       H1
       B
       E1
       D
       Q
       B1
       R
       Y
       W
       A
       L1
       I4
       H
       D4
       E
       G
       G4
       P
       H4
       I
       F4
       C4
       F
       C
       J4
       K1)
        (let ((a!1 (not (= (or (and Z3 V3)
                       (and Z3 R3)
                       (and Z3 E3)
                       (and V3 R3)
                       (and V3 E3)
                       (and R3 E3))
                   Y2)))
      (a!2 (not (= (or (and T S1)
                       (and T G1)
                       (and S1 E4)
                       (and G1 S1)
                       (and T E4)
                       (and G1 E4))
                   N)))
      (a!3 (or (not Y1) (= (+ Z (* (- 1) J2)) 1)))
      (a!4 (or (not Y1) (= (+ X (* (- 1) X1)) 1)))
      (a!5 (or (not A2) (= (+ A1 Z (* (- 1) X) (* (- 1) F2)) 0)))
      (a!6 (or (not A2) (= (+ C1 (* (- 1) O2)) 1)))
      (a!7 (or (not C2) (= (+ C1 A1 Z X (* (- 1) A4)) 1)))
      (a!8 (or (not E2) (= (+ C1 A1 Z X (* (- 1) B4)) 1))))
  (and (= (<= 1 C1) E2)
       (= (<= 1 A1) C2)
       (= (<= 1 Z) Y1)
       a!1
       a!2
       (= (or (not B3) (<= 0 C3)) A3)
       (= (or (not Q) (<= 0 R)) P)
       (= Z2 (and D1 Y2))
       (= P3 Z2)
       (= P3 B3)
       (= D1 Q)
       (= O D1)
       (= R2 Q2)
       (= T2 S2)
       (= V2 U2)
       (= X2 W2)
       (= J3 R2)
       (= J3 I3)
       (= L3 T2)
       (= L3 K3)
       (= M3 V2)
       (= M3 C3)
       (= O3 X2)
       (= O3 N3)
       (= C1 B1)
       (= A1 R)
       (= Z Y)
       (= X W)
       (= M C1)
       (= L A1)
       (= K Z)
       (= J X)
       a!3
       a!4
       (or Y1 (= C1 P2))
       (or (not Y1) (= C1 P2))
       (or Y1 (= A1 M2))
       (or (not Y1) (= A1 M2))
       (or Y1 (= Z J2))
       (or Y1 (= X X1))
       a!5
       a!6
       (or (not A2) (= Z1 0))
       (or (not A2) (= K2 0))
       (or A2 (= C1 O2))
       (or A2 (= A1 F2))
       (or A2 (= Z K2))
       (or A2 (= X Z1))
       a!7
       (or (not C2) (= B2 0))
       (or (not C2) (= L2 1))
       (or (not C2) (= N2 0))
       (or C2 (= C1 A4))
       (or C2 (= A1 N2))
       (or C2 (= Z L2))
       (or C2 (= X B2))
       a!8
       (or (not E2) (= D2 0))
       (or (not E2) (= G2 0))
       (or (not E2) (= W3 1))
       (or E2 (= C1 B4))
       (or E2 (= A1 G2))
       (or E2 (= Z W3))
       (or E2 (= X D2))
       (or (not E3) (= D3 B2))
       (or E3 (= D3 Y3))
       (or (not E3) (= F3 L2))
       (or E3 (= F3 X3))
       (or E3 (= G3 H2))
       (or (not E3) (= G3 N2))
       (or E3 (= H3 I2))
       (or (not E3) (= H3 A4))
       (or (not R3) (= Z1 Q2))
       (or (not R3) (= S2 K2))
       (or (not R3) (= U2 F2))
       (or (not R3) (= W2 O2))
       (or R3 (= Q3 Q2))
       (or R3 (= S3 S2))
       (or R3 (= T3 U2))
       (or R3 (= U3 W2))
       (or (not V3) (= X1 Q3))
       (or V3 (= F3 S3))
       (or V3 (= G3 T3))
       (or V3 (= H3 U3))
       (or V3 (= Q3 D3))
       (or (not V3) (= S3 J2))
       (or (not V3) (= T3 M2))
       (or (not V3) (= U3 P2))
       (or (not Z3) (= H2 G2))
       (or (not Z3) (= I2 B4))
       (or (not Z3) (= X3 W3))
       (or (not Z3) (= Y3 D2))
       (or Z3 (= C1 I2))
       (or Z3 (= A1 H2))
       (or Z3 (= Z X3))
       (or Z3 (= X Y3))
       (or (not S1) (= R1 W1))
       (or S1 (= R1 V))
       (or (not S1) (= O1 V1))
       (or S1 (= O1 M1))
       (or (not S1) (= I1 U1))
       (or S1 (= I1 U))
       (or (not S1) (= F1 T1))
       (or S1 (= F1 S))
       (or G1 (= R1 Q1))
       (or (not G1) (= Q1 P1))
       (or G1 (= O1 N1))
       (or (not G1) (= N1 J1))
       (or G1 (= I1 H1))
       (or (not G1) (= H1 B))
       (or G1 (= F1 E1))
       (or (not G1) (= E1 D))
       (or T (= M1 I4))
       (or (not T) (= M1 H))
       (or (not T) (= V L1))
       (or T (= V A))
       (or T (= U D4))
       (or (not T) (= U E))
       (or T (= S G4))
       (or (not T) (= S G))
       (= (<= 1 C1) A2)))
      )
      (state Z2
       P3
       Z3
       E3
       V3
       R3
       Y2
       X2
       O3
       V2
       M3
       T2
       L3
       R2
       J3
       U3
       H3
       P2
       T3
       G3
       M2
       S3
       F3
       J2
       Q3
       X1
       D3
       W2
       O2
       U2
       F2
       S2
       K2
       Q2
       Z1
       B3
       N3
       C3
       K3
       I3
       I2
       A4
       H2
       N2
       X3
       L2
       B2
       Y3
       A3
       G2
       E2
       D2
       W3
       C2
       A2
       B4
       Y1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Bool) (G Int) (H Int) (I Bool) (J Int) (K Int) (L Int) (M Int) (N Bool) (O Bool) (P Bool) (Q Bool) (R Int) (S Int) (T Bool) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Bool) (E1 Int) (F1 Int) (G1 Bool) (H1 Int) (I1 Int) (J1 Int) (K1 Bool) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Bool) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Bool) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) ) 
    (=>
      (and
        (state O
       D1
       Z1
       T
       S1
       G1
       N
       M
       C1
       L
       A1
       K
       Z
       J
       X
       R1
       V
       W1
       O1
       M1
       V1
       I1
       U
       U1
       F1
       T1
       S
       Q1
       P1
       N1
       J1
       H1
       B
       E1
       D
       Q
       B1
       R
       Y
       W
       A
       L1
       D2
       H
       Y1
       E
       G
       B2
       P
       C2
       I
       A2
       X1
       F
       C
       E2
       K1)
        (not P)
      )
      false
    )
  )
)

(check-sat)
(exit)

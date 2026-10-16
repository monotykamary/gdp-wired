import Std.Tactic.BVDecide
-- The k = 64 enumeration's law as one bitvector statement: no world is reachable, allowed by the policy and refused by
-- the proposal unless atom 30 holds. bv_decide hands it to a SAT solver and checks the LRAT certificate in the kernel.
theorem law64 (w : BitVec 64) :
    let e : BitVec 64 := 0x5555555555555555#64
    let t : BitVec 64 := 0x1249249249249249#64
    let reach := ((w >>> 1) &&& e &&& ~~~w) = 0
    let c := w &&& (w >>> 1) &&& ~~~(w >>> 2) &&& t
    let c2 := (c &&& ~~~1#64) ||| (c &&& 1#64 &&& (if (w &&& (1#64 <<< 63)) = 0 then 0 else 1))
    (reach ∧ c ≠ 0 ∧ c2 = 0) → (w &&& (1#64 <<< 63)) = 0 := by
  intro e t reach c c2 h
  bv_decide

import Std.Tactic.BVDecide
-- The k = 31 enumeration's law as one bitvector statement: no world is reachable, allowed by the policy and refused by
-- the proposal unless atom 30 holds. bv_decide hands it to a SAT solver and checks the LRAT certificate in the kernel.
theorem proposal_only_drops_when_top_atom_off (w : BitVec 31) :
    let e : BitVec 31 := 0x55555555#31
    let t : BitVec 31 := 0x09249249#31
    let reach := ((w >>> 1) &&& e &&& ~~~w) = 0
    let c := w &&& (w >>> 1) &&& ~~~(w >>> 2) &&& t
    let c2 := (c &&& ~~~1#31) ||| (c &&& 1#31 &&& (if (w &&& (1#31 <<< 30)) = 0 then 0 else 1))
    (reach ∧ c ≠ 0 ∧ c2 = 0) → (w &&& (1#31 <<< 30)) ≠ 0 := by
  intro e t reach c c2 h
  bv_decide

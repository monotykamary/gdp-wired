import Std.Tactic.BVDecide
-- The harder identities of run-bv.ts, by bv_decide, for timing against solver.ts + check.ts.
theorem add_comm32 (a b : BitVec 32) : a + b = b + a := by bv_decide
theorem add_assoc8 (a b c : BitVec 8) : (a + b) + c = a + (b + c) := by bv_decide
theorem add_assoc12 (a b c : BitVec 12) : (a + b) + c = a + (b + c) := by bv_decide
theorem ult_trans32 (a b c : BitVec 32) : a < b → b < c → a < c := by bv_decide

import RelationalFragment

/-! A small EPR countermodel need not extend to exactly 64 elements.
    This control justifies excluding fixed-64 sorts in the initial route. -/
namespace Bapa.Relational.Controls

abbrev signature : Signature := {
  sorts := 1
  relations := 0
  constants := fun _ => 0
  arity := Fin.elim0
  argumentSort := fun r => Fin.elim0 r
}

abbrev context : Context signature := {
  witnesses := fun _ => 1
  universals := fun _ => 1
}

def singleton : Matrix signature context :=
  .equal (.witness (s := 0) 0) (.universal (s := 0) 0)

abbrev model (n : Nat) (hn : 0 < n) : Model signature := {
  size := fun _ => n
  nonempty := fun _ => hn
  constant := fun _ i => Fin.elim0 i
  relation := fun r => Fin.elim0 r
}

theorem singleton_cutoff : cutoff signature context 0 = 2 := rfl

theorem singleton_satisfiable : Satisfies (model 1 (by decide)) singleton := by
  refine ⟨fun _ _ => 0, ?_⟩
  intro u
  change (0 : Fin 1) = u 0 0
  apply Fin.ext
  have h := (u 0 0).isLt
  change (u 0 0).val < 1 at h
  change 0 = (u 0 0).val
  omega

theorem singleton_not_at_64 : ¬ Satisfies (model 64 (by decide)) singleton := by
  rintro ⟨w, hu⟩
  have h0 := hu (fun _ _ => 0)
  have h1 := hu (fun _ _ => 1)
  change w 0 0 = (0 : Fin 64) at h0
  change w 0 0 = (1 : Fin 64) at h1
  have bad := congrArg Fin.val (h0.symm.trans h1)
  contradiction

#print axioms singleton_cutoff
#print axioms singleton_satisfiable
#print axioms singleton_not_at_64
end Bapa.Relational.Controls

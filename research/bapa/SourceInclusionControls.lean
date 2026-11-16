import SourceInclusion
namespace Bapa.SourceInclusionControls
open Kern

def accepts : SMachine := ⟨⟨⟨[], [], [], [], [], trueC, trueC⟩, []⟩, [], [], [], [], [], []⟩
def refuses : SMachine := {accepts with f := {accepts.f with m := {accepts.f.m with assume := .lt (.const 0) (.const 0)}}}

/-- The source admits the zero request, while the target refuses it. -/
theorem extra_source_request_refused : ¬ SourceInclusion accepts refuses := by
  intro h
  have bad := h.admission (fun _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ _ => 0) (by rfl)
  change false = true at bad
  cases bad

def trueEntry : SEntry := ⟨⟨trueC, none⟩, 0, [], [], [], [], [], [], ([], [], .leaf [] [] [] []), ([], [], .leaf [] [] [] [])⟩
def falseEntry : SEntry := {trueEntry with law := ⟨.lt (.const 0) (.const 0), none⟩}

/-- True does not imply a source claim of false, even with no binders. -/
theorem unsupported_source_law_refused : ¬ SourceLawImplication trueEntry falseEntry := by
  intro h
  have bad := h (fun _ => 0) (fun _ _ => 0) (by rfl)
  change false = true at bad
  cases bad

#print axioms extra_source_request_refused
#print axioms unsupported_source_law_refused
end Bapa.SourceInclusionControls

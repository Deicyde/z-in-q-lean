import ProjectionSupport

namespace ProjectionDescent

/-- Concatenate checked blocks without reducing the tests for their individual rows again. -/
theorem join_checks (left right : List Nat) (f : Family) (live : Nat → Bool)
    (hl : checkRows left f live=true) (hr : checkRows right f live=true) :
    checkRows (left++right) f live=true := by
  change (left++right).all (fun i => reads live (f i))=true
  rw [List.all_append]; change (checkRows left f live && checkRows right f live)=true
  rw [hl,hr]; rfl

end ProjectionDescent

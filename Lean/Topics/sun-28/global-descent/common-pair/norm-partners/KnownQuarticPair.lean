import CompanionExclusion

namespace Sun28.NormPartners
open Sun28.SelmerRealization Sun28.GlobalSections

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-- The two previously exhibited points for (17,409) have exactly the
ordered cover labels, so this example belongs to the cancelled case. -/
theorem cancelled_17_409 : CancelledFactors 17 409 := by
  have first : Cover ℚ (17*43) 17 1 := by
    exact ⟨7691,18819,13195,944,Or.inr (Or.inr (Or.inr (by norm_num))),by norm_num,by norm_num⟩
  have second : Cover ℚ (17*(43*409)) 17 1 := by
    exact ⟨16834486001,69241267359,16956926695,8855428,
      Or.inr (Or.inr (Or.inr (by norm_num))),by norm_num,by norm_num⟩
  have s17 := (by norm_num : Nat.Prime 17).squarefree
  have s43 := (by norm_num : Nat.Prime 43).squarefree
  have s409 := (by norm_num : Nat.Prime 409).squarefree
  have sq : Squarefree (17*43 : ℕ) := Nat.squarefree_mul_iff.mpr ⟨by decide,s17,s43⟩
  have sd : Squarefree (43*409 : ℕ) := Nat.squarefree_mul_iff.mpr ⟨by decide,s43,s409⟩
  have full : Squarefree (17*(43*409) : ℕ) := Nat.squarefree_mul_iff.mpr ⟨by decide,s17,sd⟩
  exact ⟨43,by decide,sq,by decide,Or.inl (family_of_cover (by decide) (by decide) sq first),
    Or.inl (family_of_cover (by decide) (by decide) full second)⟩

end Sun28.NormPartners
#print axioms Sun28.NormPartners.cancelled_17_409

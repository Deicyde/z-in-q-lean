import ZInQKernel.Contrib.HeckeAll.Provider
import OriginalBranchHeadline

namespace ZInQBlueprint.SelectedTwists

open WeierstrassCurve ZInQ ZInQ.Literature ZInQ.RouteK.Rank5b

/-- Only the (7,3) coefficient on squarefree positive twists congruent to five is used. -/
def BracketDerivative : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ F : ℂ → ℂ,
    IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F →
      deriv F 1 = 0 → T5bCl d = 0

/-- The positive-rank implication restricted to the twists selected by the genus sum. -/
def SelectedGrossZagier : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → T5bCl d = 1 → ∀ F : ℂ → ℂ,
    IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F → deriv F 1 ≠ 0 →
    ∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point, ¬ IsOfFinAddOrder P

/-- Root number minus one supplies the missing zeroth-order vanishing. -/
theorem higherOrder_iff_derivative_zero {d : ℕ} (hd : d % 8 = 5) (hsq : Squarefree d)
    {F : ℂ → ℂ} (hF : IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F) :
    2 ≤ analyticOrderAt F 1 ↔ deriv F 1 = 0 := by
  have zero := rootNumberVanishing_of_functionalEquation ZInQ.Contrib.functionalEquation5 d hd hsq F hF
  have ha := hF.1.analyticAt (1 : ℂ)
  have test := natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := 2) ha
  constructor
  · intro h
    simpa using test.mp h 1 (by decide)
  · intro hdF
    apply test.mpr
    intro i hi
    interval_cases i <;> simp [zero, hdF]

/-- The usual two-row Tian--Yuan--Zhang input supplies the one required derivative test. -/
theorem bracket_of_readingA (h : TYZThm35ReadingA) : BracketDerivative := by
  intro d hd hsq F hF hz
  exact (h d hd hsq F hF ((higherOrder_iff_derivative_zero hd hsq hF).2 hz)).2

/-- The classical positive-rank theorem implies the selected derivative formulation. -/
theorem selected_of_grossZagier (h : GrossZagier) : SelectedGrossZagier := by
  intro d hd hsq _ F hF hder
  have h0 : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have zero := rootNumberVanishing_of_functionalEquation ZInQ.Contrib.functionalEquation5 d hd hsq F hF
  exact h _ (shortCurve_isElliptic (neg_ne_zero.mpr (pow_ne_zero 2 h0))) F hF
    ((hF.1.analyticAt 1).analyticOrderAt_eq_one_of_zero_deriv_ne_zero zero hder)

/-- PR64 supplies the continuation. A single bracket and the selected positive-rank theorem suffice. -/
theorem rank_of_bracket (hB : BracketDerivative) (hG : SelectedGrossZagier) :
    ZInQ.RouteK.Rank.CertifiedRankTYZClRk := by
  intro d hd hsq hodd
  obtain ⟨F, hF⟩ := ZInQ.Contrib.heckeContinuation d (by omega)
  refine hG d hd hsq hodd F hF (fun hz => ?_)
  have hz' := hB d hd hsq F hF hz
  exact zero_ne_one (hz'.symm.trans hodd)

/-- The frozen bounded polynomial from a sextic height and two selected-twist statements. -/
theorem frozen_of_height_bracket (height : ZInQBlueprint.BranchHeight.CanonicalBranchBound)
    (hB : BracketDerivative) (hG : SelectedGrossZagier) : ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk
    (ZInQBlueprint.BranchHeight.sixContactMin_of_branchHeight
      (ZInQBlueprint.BranchHeight.canonical_iff_bounded.mp height))
    (rank_of_bracket hB hG)

end ZInQBlueprint.SelectedTwists

#print axioms ZInQBlueprint.SelectedTwists.higherOrder_iff_derivative_zero
#print axioms ZInQBlueprint.SelectedTwists.bracket_of_readingA
#print axioms ZInQBlueprint.SelectedTwists.selected_of_grossZagier
#print axioms ZInQBlueprint.SelectedTwists.rank_of_bracket
#print axioms ZInQBlueprint.SelectedTwists.frozen_of_height_bracket

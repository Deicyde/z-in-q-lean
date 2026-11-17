import SelectedTwists
import TYZBracket

namespace ZInQBlueprint.SelectedTwists

open WeierstrassCurve ZInQ ZInQ.Literature ZInQ.RouteK.Rank5b

/-- The literal second integer coefficient in the proof on journal page 760. -/
def PrintedBracketDerivative : Prop :=
  ∀ (d : ℕ) (hd : d % 8 = 5), Squarefree d → ∀ F : ℂ → ℂ,
    IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F → deriv F 1 = 0 →
      Even (TYZ.printedCoefficient d hd)

/-- No extra term from the first bracket or from a unit factor enters the implication. -/
theorem printed_iff_bracket : PrintedBracketDerivative ↔ BracketDerivative := by
  constructor
  · intro h d hd hsq F hF hzero
    rw [← TYZ.printedCoefficient_mod_two hd hsq]
    exact (ZMod.natCast_eq_zero_iff _ _).2 (even_iff_two_dvd.mp (h d hd hsq F hF hzero))
  · intro h d hd hsq F hF hzero
    have hcast := (TYZ.printedCoefficient_mod_two hd hsq).trans (h d hd hsq F hF hzero)
    exact (even_iff_two_dvd).2 ((ZMod.natCast_eq_zero_iff _ _).1 hcast)

/-- The three remaining statements use the intrinsic sextic, the printed genus sum and the selected twists. -/
theorem frozen_of_printed_bracket (height : BranchHeight.CanonicalBranchBound)
    (bracket : PrintedBracketDerivative) (rank : SelectedGrossZagier) : ZInQ.FrozenTarget :=
  frozen_of_height_bracket height (printed_iff_bracket.mp bracket) rank

end ZInQBlueprint.SelectedTwists

#print axioms ZInQBlueprint.SelectedTwists.printed_iff_bracket
#print axioms ZInQBlueprint.SelectedTwists.frozen_of_printed_bracket

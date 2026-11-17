import TYZBracket
import ZInQKernel.Hypotheses.CR3Literature

namespace ZInQBlueprint.OriginalRank

open ZInQ ZInQ.Literature

/-- At a zero of order at least two the second genus sum is even. -/
def HigherOrderGenusCoefficient : Prop :=
  ∀ (d : ℕ) (hd : d % 8 = 5), Squarefree d → ∀ F : ℂ → ℂ,
    IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F → 2 ≤ analyticOrderAt F 1 →
      Even (TYZ.printedCoefficient d hd)

end ZInQBlueprint.OriginalRank

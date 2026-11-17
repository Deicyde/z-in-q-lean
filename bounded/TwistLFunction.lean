import TYZBracket
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral

namespace ZInQ.Literature

/-- Entire continuation of the arithmetic Hasse–Weil L-series from its half plane
of absolute convergence. The centre of the functional equation is one. -/
def IsLContinuation (E : WeierstrassCurve ℚ) (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧ ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s

end ZInQ.Literature

namespace ZInQBlueprint.OriginalRank

open ZInQ ZInQ.Literature

/-- The separate genus coefficient of Tian–Yuan–Zhang at a zero of order at least two. -/
def HigherOrderGenusCoefficient : Prop :=
  ∀ (d : ℕ) (hd : d % 8 = 5), Squarefree d → ∀ F : ℂ → ℂ,
    IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F → 2 ≤ analyticOrderAt F 1 →
      Even (TYZ.printedCoefficient d hd)

end ZInQBlueprint.OriginalRank

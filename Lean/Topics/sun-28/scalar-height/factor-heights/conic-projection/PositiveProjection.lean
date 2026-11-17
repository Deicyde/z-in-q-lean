import RemainingFinal
import PositiveSelection
import MarkedArithmeticEndpoint
import OneSignPolynomial
namespace Sun28.ConicProjection
open Sun28.ConicCovers Sun28.ConicRemaining Sun28.ConicSelection Sun28.ScalarRankZero
open Sun28.ScalarDepth Sun28.Ordinary
noncomputable section
set_option maxRecDepth 12000
/-- The positive marked genus-two fibre is empty, including points whose
coordinate has no prescribed representation by the original scalar parameter. -/
theorem no_positive_quintic (descent : TwoIsogenyRank) (reduction : OddGoodReduction)
    {s y : ℚ} (above : 4 < s) (sq : ratSquare s) (shift : ratSquare (7*(s-4)))
    (linear : ratSquare (16*s-15))
    (curve : y^2 = s*(s-4)*(16*s-15)*(1372*s^2-1396*s+439)) : False := by
  have hs : 0 < s := by linarith
  have ha : 0 < s-4 := by linarith
  have hb : 0 < 16*s-15 := by linarith
  have hc : 0 < 1372*s^2-1396*s+439 := by
    have h : 0 < 1372*s-1396 := by linarith
    nlinarith only [mul_pos hs h]
  have nz : y ≠ 0 := by
    intro zero
    have h := mul_pos (mul_pos (mul_pos hs ha) hb) hc
    rw [← curve, zero] at h
    norm_num at h
  have selected := Sun28.ConicArithmetic.positive_selected positive_selmer_selection above sq shift linear nz curve
  obtain ⟨r, hr⟩ := sq
  obtain ⟨z, hz⟩ := shift
  exact negative42_excluded (short_bound_of_rank (@short_rank_of_three descent empty_three) reduction)
    above hr hz selected

/-- The positive marked scalar branch is empty over the rationals, using only
the classical two-isogeny rank formula and good reduction on rational torsion. -/
theorem no_positive (descent : TwoIsogenyRank) (reduction : OddGoodReduction) (x : ℚ) :
    ¬ positiveParameter x :=
  nonpositive_by_elementary_rank positive_selmer_selection descent reduction x

theorem scalar_of_negative (descent : TwoIsogenyRank) (reduction : OddGoodReduction)
    (remaining : NegativeExceptionalScalarBound) : ScalarBound :=
  scalar_of_elementary_rank descent reduction positive_selmer_selection remaining

/-- This alternative inverse argument retains the negative and unconcentrated
scalar cases, the ordinary height bound and the forward arithmetic hypotheses. -/
theorem one_sign_of_negative (realCurves : RealComponents.PublishedProposition72)
    (quadric : ConeCount.PublishedQuadricCount) (units : FiveMarkUnits.PublishedCorollary72)
    (pell : HeightBudget.PublishedAllPell) (classes : HeightExtension.PublishedClassRegulator)
    (disc : HeightFibres.Sharp.QuadraticCharacterDiscriminants) (descent : TwoIsogenyRank)
    (reduction : OddGoodReduction) (remaining : NegativeExceptionalScalarBound)
    (ordinary : OrdinaryBound) (moments : PrimeValues.FirstMomentInputs)
    (points : ZInQBlueprint.FiveMetric.RemainingSections) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 MultiplierChoice.oneSignPolynomial x w=0) ↔ ∃ k : ℤ, x=(k:ℚ) :=
  (MultiplierChoice.compiled_one_sign x).trans (ScalarDepth.fixed_projection realCurves quadric units pell
    classes disc (scalar_of_negative descent reduction remaining) ordinary moments
    (ZInQBlueprint.FiveMetric.remaining_sections_iff.mp points) x)
end
end Sun28.ConicProjection
#print axioms Sun28.ConicProjection.no_positive_quintic
#print axioms Sun28.ConicProjection.no_positive
#print axioms Sun28.ConicProjection.scalar_of_negative
#print axioms Sun28.ConicProjection.one_sign_of_negative

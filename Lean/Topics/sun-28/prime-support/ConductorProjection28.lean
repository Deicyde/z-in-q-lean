import RatioProjection
import PositiveDivisors
import ConductorBudget

namespace Sun28.PointLifts
open Sun28.PointFibres Sun28.PointDescent Sun28.PrescribedPoints Sun28.PairedClasses
  Sun28.PreparedPoles Sun28.TwistRank Sun28.TwistExtension
noncomputable section

def PositiveResidual : Prop := ∀ b θ : ℕ, AdmissiblePair b θ → InputClass b → FixedSquares θ →
  NormConic b θ → ¬FactorPair b θ → ¬OneQuartic (b:ℚ) (θ:ℚ) →
  (∀ t : ℚ, t≠0 → ¬RatioCover (b:ℚ) (θ:ℚ) t) →
  ∃ s : ℚ, AllowedRatio b θ s ∧ padicValRat 3 s=0 ∧ PositiveFibre b θ s.num s.den

theorem residual_iff_positive : LocalRatioResidual ↔ PositiveResidual := by
  have equiv {b θ : ℕ} (a : AdmissiblePair b θ) {s : ℚ} (sn : s≠0) :
      DivisorFibre b θ s.num s.den ↔ PositiveFibre b θ s.num s.den :=
    (integral_iff_divisors ..).symm.trans (integral_iff_positive (by exact_mod_cast a.1)
      (by exact_mod_cast a.2.1) (Rat.num_ne_zero.mpr sn) (by exact_mod_cast s.den_ne_zero))
  rw [residual_iff_divisors]
  constructor
  · intro H b θ a i f N c o t
    obtain ⟨s,r,v,D⟩ := H b θ a i f N c o t
    exact ⟨s,r,v,(equiv a r.1).mp D⟩
  · intro H b θ a i f N c o t
    obtain ⟨s,r,v,D⟩ := H b θ a i f N c o t
    exact ⟨s,r,v,(equiv a r.1).mpr D⟩
end
end Sun28.PointLifts

namespace Sun28.ReducedArithmetic
open Sun28.HeightExtension Sun28.HeightBudget Sun28.HeightFibres.Sharp Sun28.Ordinary

/-- The fixed Diophantine definition with an elliptic conductor bound for
the five forms and a finite positive divisor list for each nonzero ratio. -/
theorem conductor_projection (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (pell : PublishedAllPell)
    (classes : PublishedClassRegulator) (characters : QuadraticCharacterDiscriminants)
    (quadric : ConeCount.PublishedQuadricCount) (elliptic : HeightCubics.Refinement.PublishedElliptic)
    (height : HeightCubics.Refinement.Remaining) (primeCount : RayDensity.CorrelationInputs)
    (points : PointLifts.PositiveResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ, x=(z:ℚ) := by
  have full := (HeightCubics.Refinement.original_iff_conductor units pell classes characters elliptic).mpr height
  have mordell := HeightCubics.Refinement.supported_coordinates elliptic
  exact ordinate_projection realCurves units pell classes characters quadric mordell
    ((HeightCubics.Ordinate.original_iff_ordinate units pell classes characters mordell).mp full)
    primeCount (PointLifts.residual_iff_positive.mpr points) x
end Sun28.ReducedArithmetic
#print axioms Sun28.PointLifts.residual_iff_positive
#print axioms Sun28.ReducedArithmetic.conductor_projection

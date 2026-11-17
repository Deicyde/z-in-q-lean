import QuarticDivisors
import OrdinateProjection28

namespace Sun28.PointLifts
open Sun28.PointFibres Sun28.PointDescent Sun28.PrescribedPoints Sun28.PairedClasses
  Sun28.PreparedPoles Sun28.TwistRank Sun28.TwistExtension
noncomputable section

theorem single_iff_divisors {b θ : ℕ} (bp : 0<b) (s : ℚ) :
    SingleFibre b θ s ↔ DivisorFibre b θ s.num s.den := by
  have iff := (single_iff_integral (b:=(b:ℤ)) (θ:=(θ:ℤ)) (n:=s.num) (m:=(s.den:ℤ))
    (by exact_mod_cast bp.ne') (by exact_mod_cast s.den_ne_zero)).trans (integral_iff_divisors ..)
  simpa only [Int.cast_natCast, Rat.num_div_den] using iff

/-- The residual point problem using only a primitive direction, an integer
ratio in lowest terms, and two quadratic equations for a signed divisor. -/
def DivisorResidual : Prop := ∀ b θ : ℕ, AdmissiblePair b θ → InputClass b → FixedSquares θ →
  NormConic b θ → ¬FactorPair b θ → ¬OneQuartic (b:ℚ) (θ:ℚ) →
  (∀ t : ℚ, t≠0 → ¬RatioCover (b:ℚ) (θ:ℚ) t) →
  ∃ s : ℚ, AllowedRatio b θ s ∧ padicValRat 3 s=0 ∧ DivisorFibre b θ s.num s.den

theorem residual_iff_divisors : LocalRatioResidual ↔ DivisorResidual := by
  constructor
  · intro H b θ a i f N c o t
    obtain ⟨s,allowed,F⟩ := H b θ a i f N c o t
    exact ⟨s,allowed,three_unit_of_fibre a allowed.1 F,(single_iff_divisors a.1 s).mp F⟩
  · intro H b θ a i f N c o t
    obtain ⟨s,allowed,_,D⟩ := H b θ a i f N c o t
    exact ⟨s,allowed,(single_iff_divisors a.1 s).mpr D⟩

end
end Sun28.PointLifts

namespace Sun28.ReducedArithmetic
open Sun28.HeightExtension Sun28.HeightBudget Sun28.HeightFibres.Sharp Sun28.Ordinary
theorem divisor_projection (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (pell : PublishedAllPell)
    (classes : PublishedClassRegulator) (characters : QuadraticCharacterDiscriminants)
    (quadric : ConeCount.PublishedQuadricCount) (mordell : HeightCubics.Ordinate.PublishedCoordinates)
    (height : HeightCubics.Ordinate.Remaining) (primeCount : RayDensity.CorrelationInputs)
    (points : PointLifts.DivisorResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ, x=(z:ℚ) :=
  ordinate_projection realCurves units pell classes characters quadric mordell height primeCount
    (PointLifts.residual_iff_divisors.mpr points) x
end Sun28.ReducedArithmetic
#print axioms Sun28.PointLifts.single_iff_divisors
#print axioms Sun28.PointLifts.residual_iff_divisors
#print axioms Sun28.ReducedArithmetic.divisor_projection

import HeightProjection
import IntrinsicHeight
import OrbitResidual

/-! Two independent directions for the fixed integer polynomial.
The height implication uses one curve and no external height, Pell or elliptic theorem. -/
namespace Sun28.WitnessHeight
open ZInQ Sun28.Ordinary Sun28.Forward Sun28.ScalarHeight Sun28.FixedPreparation
open Sun28.FiveDescent.ResidueField Sun28.MinimalConductors Sun28.PreparedPoles Sun28.WitnessIndices Height
noncomputable section

/-- A height bound on the fixed curve alone suffices for the integer-only direction. -/
theorem integral_of_field_height (height : FieldHeight glazerConstant24) (x : ℚ)
    (zero : ∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) : ∃ z : ℤ, x=(z:ℚ) := by
  obtain ⟨A,η,accepted⟩ := (Concrete.polynomial_iff_certificate _).1 zero
  let t := slope (nineAffine A).doubles η
  obtain ⟨j,largest⟩ := maximum_exists t
  have bound := (original_iff_fieldHeight _).mpr height
  exact integral_of_two_heights A x η accepted j largest
    (bound _ _ (source_primitive (t j)) (source_off (t j) (accepted.scale_guard j).1))
    (bound _ _ (beta_primitive x) (beta_off_forms x))

/-- Only the two published existence inputs are needed if the height is attacked
directly on the fixed curve. The height, prime mass and point assertions are explicit premises. -/
theorem field_projection (realCurves : RealComponents.PublishedProposition72)
    (quadric : ConeCount.PublishedQuadricCount) (height : FieldHeight glazerConstant24)
    (moments : PrimeValues.FirstMomentInputs) (points : GlobalDescent.DescentResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ, x=(z:ℚ) := by
  refine ⟨integral_of_field_height height x,?_⟩
  rintro ⟨k,rfl⟩
  exact fibre_of_integer realCurves quadric moments (GlobalDescent.sections_iff_descent.mpr points) k

end
end Sun28.WitnessHeight
#print axioms Sun28.WitnessHeight.integral_of_field_height
#print axioms Sun28.WitnessHeight.field_projection

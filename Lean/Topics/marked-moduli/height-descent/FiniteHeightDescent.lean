import Mathlib.NumberTheory.Height.NumberField
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-! The nonarchimedean factors of a projective number-field height, using the coordinate ideal. -/
open NumberField
namespace ZInQBlueprint.HeightDescent
noncomputable section
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable {ι : Type*} [Finite ι]

omit [NumberField K] [NumberField L] [Finite ι] in
/-- The integral coordinate ideal is extended by the embedding of the rings of integers. -/
theorem coordinate_ideal_map (x : ι → 𝓞 K) :
    (Ideal.span (Set.range x)).map (algebraMap (𝓞 K) (𝓞 L)) =
      Ideal.span (Set.range (fun i => algebraMap (𝓞 K) (𝓞 L) (x i))) := by
  rw [Ideal.map_span,← Set.range_comp]
  rfl

omit [Finite ι] in
/-- In an extension of number fields the norm of the coordinate ideal is raised to [L:K]. -/
theorem coordinate_ideal_norm (x : ι → 𝓞 K) :
    (Ideal.span (Set.range (fun i => algebraMap (𝓞 K) (𝓞 L) (x i)))).absNorm =
      (Ideal.span (Set.range x)).absNorm ^ Module.finrank K L := by
  have : FiniteDimensional K L := FiniteDimensional.right ℚ K L
  let : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  rw [← coordinate_ideal_map,Ideal.absNorm_algebraMap,← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]

/-- For integral coordinates the product of all nonarchimedean factors is the inverse ideal norm. -/
theorem finite_factors {x : ι → 𝓞 K} (hx : x ≠ 0) :
    (∏ᶠ w : FinitePlace K, ⨆ i, w (x i)) =
      (((Ideal.span (Set.range x)).absNorm:ℝ))⁻¹ := by
  have he := NumberField.absNorm_mul_finprod_finitePlace_eq_one hx
  exact eq_inv_of_mul_eq_one_right he

/-- All the finite factors in a finite extension can be handled by a single ideal norm. -/
theorem finite_factors_map {x : ι → 𝓞 K} (hx : x ≠ 0) :
    (∏ᶠ w : FinitePlace L, ⨆ i, w (algebraMap K L (x i))) =
      (∏ᶠ w : FinitePlace K, ⨆ i, w (x i)) ^ Module.finrank K L := by
  let y := fun i => algebraMap (𝓞 K) (𝓞 L) (x i)
  have hy : y ≠ 0 := by
    intro h
    apply hx
    funext i
    exact (RingOfIntegers.algebraMap.injective K L) (by simpa only [y,Pi.zero_apply,map_zero] using congrFun h i)
  change (∏ᶠ w : FinitePlace L, ⨆ i, w (y i)) = _
  rw [finite_factors hy,finite_factors hx,show y = _ from rfl,coordinate_ideal_norm]
  simp

end
end ZInQBlueprint.HeightDescent
#print axioms ZInQBlueprint.HeightDescent.coordinate_ideal_map
#print axioms ZInQBlueprint.HeightDescent.coordinate_ideal_norm
#print axioms ZInQBlueprint.HeightDescent.finite_factors
#print axioms ZInQBlueprint.HeightDescent.finite_factors_map

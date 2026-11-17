import SignedSexticFibreField
import Mathlib.FieldTheory.RatFunc.Basic

/-! The quadratic field is precisely the field of fractions of the finite sextic chart.
The embedding sends the coordinate and the ordinate to their namesakes and commutes with sign. -/
namespace ZInQBlueprint.FibreDivisors
open BinaryCover Polynomial
open scoped QuadraticAlgebra
noncomputable section

variable {K : Type} [Field K]

abbrev rmap := algebraMap K[X] (RatFunc K)

def chartEmbedding (f : K[X]) : Cover f →+* Cover (rmap f) where
  toFun z := ⟨rmap z.re,rmap z.im⟩
  map_one' := by apply QuadraticAlgebra.ext <;> simp
  map_mul' x y := by apply QuadraticAlgebra.ext <;> simp
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_add' x y := by apply QuadraticAlgebra.ext <;> simp

theorem chartEmbedding_injective (f : K[X]) : Function.Injective (chartEmbedding f) := by
  intro a b e
  exact QuadraticAlgebra.ext ((IsFractionRing.injective K[X] (RatFunc K)) (congrArg QuadraticAlgebra.re e))
    ((IsFractionRing.injective K[X] (RatFunc K)) (congrArg QuadraticAlgebra.im e))

theorem chartEmbedding_star (f : K[X]) (z : Cover f) :
    chartEmbedding f (star z) = ordinateConjugation (rmap f) (chartEmbedding f z) := by
  change chartEmbedding f (star z) = star (chartEmbedding f z)
  apply QuadraticAlgebra.ext <;> simp [chartEmbedding]

theorem chartEmbedding_omega (f : K[X]) : chartEmbedding f ω = ω := by
  apply QuadraticAlgebra.ext <;> simp [chartEmbedding]

theorem chartEmbedding_polynomial (f g : K[X]) :
    chartEmbedding f (algebraMap K[X] _ g) = algebraMap (RatFunc K) _ (rmap g) := by
  apply QuadraticAlgebra.ext <;> simp [chartEmbedding]

variable (f : K[X]) [Fact (¬ IsSquare (rmap f))]
local instance chartAlgebra : Algebra (Cover f) (Cover (rmap f)) := (chartEmbedding f).toAlgebra

private theorem clearCoefficient (a : RatFunc K) : a * rmap a.denom = rmap a.num :=
  (eq_div_iff (RatFunc.algebraMap_ne_zero a.denom_ne_zero)).mp a.num_div_denom.symm

theorem chartIsFractionRing : IsFractionRing (Cover f) (Cover (rmap f)) := by
  let := (faithfulSMul_iff_algebraMap_injective (Cover f) (Cover (rmap f))).mpr (chartEmbedding_injective f)
  apply IsFractionRing.of_field
  intro z
  let x : Cover f := ⟨z.re.num * z.im.denom, z.im.num * z.re.denom⟩
  let y : Cover f := algebraMap K[X] _ (z.re.denom * z.im.denom)
  refine ⟨x,y,?_⟩
  change z = chartEmbedding f x / chartEmbedding f y
  rw [chartEmbedding_polynomial]
  have nonzero : rmap (z.re.denom * z.im.denom) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (mul_ne_zero z.re.denom_ne_zero z.im.denom_ne_zero)
  apply (eq_div_iff ((map_ne_zero (algebraMap (RatFunc K) (Cover (rmap f)))).mpr nonzero)).mpr
  apply QuadraticAlgebra.ext
  · change (z * algebraMap _ _ _).re = rmap (z.re.num * z.im.denom)
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,
      mul_zero,zero_mul,add_zero]
    simp only [map_mul]
    rw [←mul_assoc,clearCoefficient]
  · change (z * algebraMap _ _ _).im = rmap (z.im.num * z.re.denom)
    simp only [QuadraticAlgebra.im_mul,QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,
      mul_zero,zero_mul,add_zero,zero_add]
    simp only [map_mul]
    rw [mul_comm (rmap z.re.denom),←mul_assoc,clearCoefficient]

end
end ZInQBlueprint.FibreDivisors

#print axioms ZInQBlueprint.FibreDivisors.chartEmbedding_star
#print axioms ZInQBlueprint.FibreDivisors.chartEmbedding_omega
#print axioms ZInQBlueprint.FibreDivisors.chartIsFractionRing


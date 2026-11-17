import SixConicInvariant
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Derivation.Basic

/-! The two quotient maps of y²=f(x²), on their affine coordinate rings,
and the pullback formulas for the invariant elliptic differentials. -/
open Polynomial
namespace ZInQBlueprint.CMRepair
open BinaryCover
noncomputable section
variable {K : Type*} [Field K]

private def substitute {f g : K[X]} (c : K[X])
    (relation : expand K 2 g = c^2 * expand K 2 f) :
    Cover g →ₐ[K] Cover (expand K 2 f) where
  toFun a := ⟨expand K 2 a.re, c * expand K 2 a.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := by ext <;> simp [mul_add]
  map_mul' a b := by apply QuadraticAlgebra.ext <;> simp [relation] <;> ring
  commutes' k := by
    change (⟨expand K 2 (C k), c * expand K 2 0⟩ : Cover (expand K 2 f)) = ⟨C k,0⟩
    simp

private theorem substitute_injective {f g : K[X]} {c : K[X]} (hc : c ≠ 0)
    (relation : expand K 2 g = c^2 * expand K 2 f) :
    Function.Injective (substitute c relation) := by
  intro a b h
  have hr := congrArg QuadraticAlgebra.re h
  have hi := congrArg QuadraticAlgebra.im h
  apply QuadraticAlgebra.ext
  · exact expand_injective (by decide : 0 < 2) hr
  · exact expand_injective (by decide : 0 < 2) (mul_left_cancel₀ hc hi)

/-- (x,y) ↦ (x²,y) and (x,y) ↦ (x²,xy), respectively. -/
def firstCover (f : K[X]) : Cover f →ₐ[K] Cover (expand K 2 f) :=
  substitute 1 (by simp)

def secondCover (f : K[X]) : Cover (X*f) →ₐ[K] Cover (expand K 2 f) :=
  substitute X (by simp)

theorem quotient_covers_injective (f : K[X]) :
    Function.Injective (firstCover f) ∧ Function.Injective (secondCover f) :=
  ⟨substitute_injective one_ne_zero _, substitute_injective X_ne_zero _⟩

theorem quotient_coordinates (f : K[X]) :
    firstCover f (algebraMap K[X] (Cover f) X) = algebraMap K[X] _ (X^2) ∧
    firstCover f QuadraticAlgebra.omega = (QuadraticAlgebra.omega : Cover (expand K 2 f)) ∧
    secondCover f (algebraMap K[X] (Cover (X*f)) X) = algebraMap K[X] _ (X^2) ∧
    secondCover f QuadraticAlgebra.omega =
      (algebraMap K[X] _ X) * (QuadraticAlgebra.omega : Cover (expand K 2 f)) := by
  refine ⟨?_,?_,?_,?_⟩ <;> apply QuadraticAlgebra.ext <;>
    simp [firstCover,secondCover,substitute,QuadraticAlgebra.omega]

/-- Evaluating dT/Y and dT/Z on a derivation gives 2x dx/y and 2 dx/y
on the dense open xy≠0. This applies to the function field in characteristic zero. -/
theorem quotient_differentials {L : Type*} [Field L] [Algebra ℚ L] (D : Derivation ℚ L L)
    {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) :
    D (x^2) / y = 2*x*(D x/y) ∧ D (x^2) / (x*y) = 2*(D x/y) := by
  rw [sq,D.leibniz]
  simp only [smul_eq_mul]
  constructor <;> field_simp <;> ring

/-- The coefficient polynomials in this pair of differentials are independent. -/
theorem independent_coefficients [CharZero K] (a b : K)
    (vanishes : C a * (2 * X) + C b * 2 = (0 : K[X])) : a = 0 ∧ b = 0 := by
  have h₀ := congrArg (fun p : K[X] => p.eval 0) vanishes
  have h₁ := congrArg (fun p : K[X] => p.eval 1) vanishes
  have hb : b = 0 := by simpa [mul_eq_zero] using h₀
  subst b
  exact ⟨by simpa [mul_eq_zero] using h₁, rfl⟩

end
end ZInQBlueprint.CMRepair
#print axioms ZInQBlueprint.CMRepair.quotient_covers_injective
#print axioms ZInQBlueprint.CMRepair.quotient_coordinates
#print axioms ZInQBlueprint.CMRepair.quotient_differentials
#print axioms ZInQBlueprint.CMRepair.independent_coefficients

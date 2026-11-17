import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic

/-! In the parameter z=-x/y, the doubled abscissa equals 1/(4z²)-bz². -/
namespace Sun28.Scalar
open WeierstrassCurve.Affine
noncomputable section
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

def curve (b : K) : WeierstrassCurve.Affine K := ⟨0,0,0,b,0⟩

def parameter {b : K} : (curve b).Point → K
  | .zero => 0
  | .some x y _ => -x/y

def reciprocal {b : K} : (curve b).Point → K
  | .zero => 0
  | .some x _ _ => x⁻¹

omit [CharZero K] [DecidableEq K] in
theorem equation {b x y : K} (h : (curve b).Nonsingular x y) :
    y^2=x^3+b*x := by
  simpa [curve,add_comm,add_left_comm,mul_comm] using ((curve b).equation_iff x y).mp h.1

/-- Doubling in the actual group of nonsingular affine points. -/
theorem double_coordinates {b x y : K} (h : (curve b).Nonsingular x y) (hy : y≠0) :
    ∃ (u v : K) (h' : (curve b).Nonsingular u v),
      (2:ℕ) • (Point.some x y h : (curve b).Point) = Point.some u v h' ∧
      u*(4*(-x/y)^2)=1-4*b*(-x/y)^4 := by
  have nv : y ≠ (curve b).negY x y := by
    simpa [curve,negY] using (show y ≠ -y from fun he => hy (by linear_combination he/2))
  have hs : (curve b).slope x x y y = (3*x^2+b)/(2*y) := by
    rw [slope_of_Y_ne rfl nv]
    simp [curve,negY,two_mul]
  have hc := equation h
  refine ⟨_,_,nonsingular_add h h (fun he => nv he.2),?_,?_⟩
  · rw [two_nsmul,Point.add_self_of_Y_ne nv]
  · rw [hs]
    simp only [addX,curve,zero_mul,add_zero,sub_zero]
    field_simp [hy]
    grind

#print axioms double_coordinates
end
end Sun28.Scalar

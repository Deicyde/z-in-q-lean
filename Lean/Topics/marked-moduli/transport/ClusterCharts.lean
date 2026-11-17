import SexticCalibration
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

/-! The two triple-root specializations of the explicit genus-two sextic. -/

namespace ZInQBlueprint.ClusterCharts
open Polynomial ZInQBlueprint.SexticCalibration
noncomputable section

variable {R : Type*} [CommRing R]

def q₀ (x : R) := x^2 + 16*x - 32
def qPole (x : R) := x^2 + 2*x - 1
def first₀ (x : R) := 3*q₀ x*(x^2+32)*(x^2-16*x-32)
def firstPole (x : R) := -4*(x^2+1)*(x^4-22*x^2+1)

/-- At a pole w=1/s. This integral polynomial is w⁷ f(3z/w). -/
def pole (z w : R) : R :=
  let t := 9-32*w^2
  729*(3-4*w)*z^6+1458*t*z^5+243*t*(28*w+9)*z^4-108*t^2*z^3+
    27*t^2*(28*w-9)*z^2+18*t^3*z-t^3*(4*w+3)

theorem pole_identity {K : Type*} [Field K] (z w : K) (hw : w ≠ 0) :
    pole z w = w^7*(sextic w⁻¹).eval (3*z/w) := by
  simp [pole,sextic]
  field_simp
  ring

/-- Constant and linear terms in the degeneration parameter at zero. -/
theorem zero_layers (x : R) :
    ((sextic (X : R[X])).eval (C x)).eval 0 = -4*(q₀ x)^3 ∧
    ((sextic (X : R[X])).eval (C x)).derivative.eval 0 = first₀ x := by
  constructor <;> simp [sextic,q₀,first₀,derivative_add,derivative_sub,derivative_mul,
    derivative_pow,map_ofNat] <;> ring

/-- Constant and linear terms at the pole, with denominators cleared by 3⁶. -/
theorem pole_layers (x : R) :
    (pole (C x) X).eval 0 = 729*3*(qPole x)^3 ∧
    (pole (C x) X).derivative.eval 0 = 729*firstPole x := by
  constructor <;> simp [pole,qPole,firstPole,derivative_add,derivative_sub,derivative_mul,
    derivative_pow,map_ofNat] <;> ring

def slope₀ (x : R) := 3*(2*x+16)*(x^2+32)*(x^2-16*x-32)

theorem first₀_derivative {a : R} (ha : q₀ a = 0) :
    (first₀ (X : R[X])).derivative.eval a = slope₀ a := by
  unfold q₀ at ha
  simp [first₀,q₀,slope₀,derivative_mul,derivative_add,derivative_sub,derivative_pow,map_ofNat,ha]

variable {K : Type*} [Field K] [NeZero (2:K)] [NeZero (3:K)]

theorem zero_units {a : K} (ha : q₀ a = 0) : 2*a+16 ≠ 0 ∧ slope₀ a ≠ 0 := by
  have h2 := NeZero.ne (2:K)
  have h3 := NeZero.ne (3:K)
  unfold q₀ at ha
  have hd : 2*a+16 ≠ 0 := by
    intro h
    apply mul_ne_zero (pow_ne_zero 7 h2) h3
    linear_combination (2*a+16)*h-4*ha
  have hx : a^2+32 ≠ 0 := by
    intro h
    apply mul_ne_zero (pow_ne_zero 12 h2) h3
    linear_combination 16*(a+20)*h-16*(a+4)*ha
  have hy : a^2-16*a-32 ≠ 0 := by
    intro h
    apply pow_ne_zero 10 h2
    linear_combination (a+16)*(ha-h)-32*ha
  exact ⟨hd, mul_ne_zero (mul_ne_zero (mul_ne_zero h3 hd) hx) hy⟩

omit [NeZero (3:K)] in
theorem pole_units {a : K} (ha : qPole a = 0) : 2*a+2 ≠ 0 ∧ firstPole a ≠ 0 := by
  have h2 := NeZero.ne (2:K)
  unfold qPole at ha
  constructor
  · intro h
    apply pow_ne_zero 3 h2
    linear_combination (2*a+2)*h-4*ha
  · intro h
    unfold firstPole at h
    apply pow_ne_zero 8 h2
    linear_combination (7*a+17)*h+4*(7*a^5+3*a^4-146*a^3-62*a^2-169*a-81)*ha

omit [NeZero (3:K)] in
/-- In characteristic different from two, the cubic AX³+BX is separable for B ≠ 0. -/
theorem zero_cubic {A B : K} (hB : B ≠ 0) :
    (C A*X^3 + C B*X).Separable := by
  let P : K[X] := C A*X^3 + C B*X
  have hd : P.derivative = 3*C A*X^2+C B := by simp [P,derivative_mul,map_ofNat]; ring
  have hn := mul_ne_zero (NeZero.ne (2:K)) (pow_ne_zero 2 hB)
  change ∃ c d : K[X], c*P+d*P.derivative=1
  refine ⟨C (2*B^2)⁻¹*(-9*C A*X), C (2*B^2)⁻¹*(3*C A*X^2+2*C B), ?_⟩
  calc
    _ = C (2*B^2)⁻¹*C (2*B^2) := by rw [hd]; simp [P, map_ofNat]; ring
    _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hn, map_one]

omit [NeZero (2:K)] in
/-- In characteristic different from three, the cubic AX³+B is separable for B ≠ 0. -/
theorem pole_cubic {A B : K} (hB : B ≠ 0) :
    (C A*X^3 + C B).Separable := by
  let P : K[X] := C A*X^3+C B
  have hd : P.derivative = 3*C A*X^2 := by simp [P,derivative_mul,map_ofNat]; ring
  have hn := mul_ne_zero (NeZero.ne (3:K)) hB
  change ∃ c d : K[X], c*P+d*P.derivative=1
  refine ⟨C (3*B)⁻¹*3, -C (3*B)⁻¹*X, ?_⟩
  calc
    _ = C (3*B)⁻¹*C (3*B) := by rw [hd]; simp [P,map_ofNat]; ring
    _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hn, map_one]

/-- The two residual cubics at each pair of centres have three simple geometric roots
when the leading coefficient is nonzero. Separability itself follows here for every unit U. -/
theorem residual_cubics {a b U : K} (ha : q₀ a = 0) (hb : qPole b = 0) (hU : U ≠ 0) :
    (C (-4*(2*a+16)^3)*X^3 + C (U*slope₀ a)*X).Separable ∧
    (C (3*(2*b+2)^3)*X^3 + C (U*firstPole b)).Separable :=
  ⟨zero_cubic (mul_ne_zero hU (zero_units ha).2), pole_cubic (mul_ne_zero hU (pole_units hb).2)⟩

end
end ZInQBlueprint.ClusterCharts

#print axioms ZInQBlueprint.ClusterCharts.pole_identity
#print axioms ZInQBlueprint.ClusterCharts.zero_layers
#print axioms ZInQBlueprint.ClusterCharts.pole_layers
#print axioms ZInQBlueprint.ClusterCharts.first₀_derivative
#print axioms ZInQBlueprint.ClusterCharts.zero_units
#print axioms ZInQBlueprint.ClusterCharts.pole_units
#print axioms ZInQBlueprint.ClusterCharts.zero_cubic
#print axioms ZInQBlueprint.ClusterCharts.pole_cubic
#print axioms ZInQBlueprint.ClusterCharts.residual_cubics

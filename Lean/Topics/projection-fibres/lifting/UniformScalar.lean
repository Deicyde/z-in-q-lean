import Std

namespace ProjectionFibres.Lifting.Uniform
open Lean.Grind Std
attribute [local instance] Semiring.natCast Ring.intCast

variable {K : Type} [Field K]

/-- Cleared discriminant of the reciprocal scalar equation. -/
theorem reciprocal_discriminant (r L W t : K)
    (h : W * (1+r*L^2*t^2) + r*t = 0) :
    r*(1+2*L^2*W*t)^2 = r-4*L^2*W^2 := by
  have e : r*(1+2*L^2*W*t)^2 - (r-4*L^2*W^2)
      = 4*L^2*W*(W*(1+r*L^2*t^2)+r*t) := by grobner
  rw [h] at e
  grobner

/-- A square root with nonzero Cayley denominator recovers the rational trace. -/
theorem inverse_discriminant (r L W y t : K) (hr : r ≠ 0) (hy : 1+y ≠ 0)
    (square : r*y^2 = r-4*L^2*W^2) (trace : r*(1+y)*t = -2*W) :
    W*(1+r*L^2*t^2)+r*t = 0 := by
  have vanish : (r*(1+y)^2)*(W*(1+r*L^2*t^2)+r*t) = 0 := by
    calc
      _ = r*(1+y)^2*W + r*(1+y)*(r*(1+y)*t) + L^2*W*(r*(1+y)*t)^2 := by grobner
      _ = W*(r*y^2-r+4*L^2*W^2) := by rw [trace]; grobner
      _ = 0 := by rw [square]; grobner
  have den : r*(1+y)^2 ≠ 0 := by grind
  grind

variable [LE K] [LT K] [LawfulOrderLT K] [IsLinearOrder K] [OrderedRing K]

/-- Negative discriminant excludes the corrected scalar over an ordered field. -/
theorem real_obstruction (r L W t : K) (hr : 0 < r) (large : r < 4*L^2*W^2) :
    W * (1+r*L^2*t^2) + r*t ≠ 0 := by
  intro eqn
  let a := 1+2*L^2*W*t
  have asq : 0 ≤ a*a := by
    by_cases h : 0 ≤ a
    · exact OrderedRing.mul_nonneg h h
    · have h' : 0 ≤ -a := by grind
      have hh := OrderedRing.mul_nonneg h' h'
      rwa [show -a*(-a) = a*a by grobner] at hh
  have sq : 0 ≤ (1+2*L^2*W*t)^2 := by
    rw [show (1+2*L^2*W*t)^2 = a*a by change a^2=a*a; grobner]
    exact asq
  have pos := OrderedRing.mul_nonneg (Preorder.le_of_lt hr) sq
  rw [reciprocal_discriminant r L W t eqn] at pos
  grind

end ProjectionFibres.Lifting.Uniform
#print axioms ProjectionFibres.Lifting.Uniform.reciprocal_discriminant
#print axioms ProjectionFibres.Lifting.Uniform.inverse_discriminant
#print axioms ProjectionFibres.Lifting.Uniform.real_obstruction

import Std

namespace NormalizedHeight
open Lean.Grind Std

section Duplication
variable {K : Type} [CommRing K]

def F (a b : K) := (a^2 + b^2)^2
def G (a b : K) := 4*a*b*(a^2-b^2)

/-- The two identities bound the common finite divisor in both projective charts. -/
theorem bezout (a b : K) :
    4*b*(4*b^2-3*a^2)*F a b + a*(5*b^2+3*a^2)*G a b = 16*b^7 ∧
    4*a*(4*a^2-3*b^2)*F a b - b*(5*a^2+3*b^2)*G a b = 16*a^7 := by
  unfold F G
  constructor <;> grobner

/-- Substitution of x=d*a/b into the original projective duplication forms. -/
theorem conjugacy (d a b : K) :
    ((d*a)^2+d^2*b^2)^2 = d^4*F a b ∧
    4*(d*a)*b*((d*a)^2-d^2*b^2) = d^3*G a b := by
  unfold F G
  constructor <;> grobner
end Duplication

/-- The numerical height at 4P exceeds the threshold for all |n| ≥ 2. -/
theorem seed_comparison :
    16 * (41 : Nat)^16 < 1529752378517906288544325249 := by decide

section Comparison
variable {K : Type} [Field K] [LE K] [LT K] [LawfulOrderLT K]
    [IsLinearOrder K] [OrderedRing K]

/-- Here e=log 4, l=log 41, c is twice the canonical height and s=h(u(4P)). -/
theorem calibration {e l c s : K} (seed : 16*l+2*e < s)
    (lower : 3*s ≤ 48*c+2*e) : 12*l+e < 12*c := by grind

/-- The upper doubling error is absorbed once the square of the index is at least four. -/
theorem sharp {e l c m h : K} (err : 0 ≤ e) (cal : 12*l+e < 12*c)
    (index : 4 ≤ m) (upper : 3*m*c ≤ 3*h+e) : m*l < h := by
  have gap : 0 ≤ c-l := by grind
  have product := OrderedRing.mul_nonneg (show 0 ≤ m-4 by grind) gap
  grind

/-- The weaker bound needed by both source families uses only the height of P. -/
theorem single_point {e l c m h : K} (err : 0 ≤ e) (index : 1 ≤ m)
    (lower : 3*l ≤ 3*c+2*e) (upper : 3*m*c ≤ 3*h+e) : m*(l-e) ≤ h := by
  have index_nonneg : 0 ≤ m := by grind
  have calibrated := OrderedRing.mul_nonneg index_nonneg (show 0 ≤ 3*c+2*e-3*l by grind)
  have budget := OrderedRing.mul_nonneg (show 0 ≤ m-1 by grind) err
  grind
end Comparison

end NormalizedHeight
#print axioms NormalizedHeight.bezout
#print axioms NormalizedHeight.conjugacy
#print axioms NormalizedHeight.seed_comparison
#print axioms NormalizedHeight.calibration
#print axioms NormalizedHeight.sharp
#print axioms NormalizedHeight.single_point

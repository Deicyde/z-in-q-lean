import Mathlib

/-! Genus-two Mumford coordinates for halves of a branch point. These are the explicit
coefficients in Zarhin's Theorem 3.2. The tangent identity verifies divisibility. -/
namespace SixContactFour
open Polynomial
noncomputable section
variable {R : Type*} [CommRing R]

def uHalf (a b c d t : R) : R := t^2-(a*b+a*c+a*d+b*c+b*d+c*d)*t+a*b*c*d
def firstSymm (a b c d : R) : R := a+b+c+d
def thirdSymm (a b c d : R) : R := a*b*c+a*b*d+a*c*d+b*c*d
def tangentValue (a b c d t : R) : R := firstSymm a b c d*t^2-thirdSymm a b c d*t
def vHalf (a b c d t : R) : R := tangentValue a b c d t-firstSymm a b c d*uHalf a b c d t

/-- The intersection with the tangent parabola consists of the distinguished
branch and two copies of the divisor of the quadratic Mumford polynomial. -/
theorem branch_tangent_identity (a b c d t : R) :
    t*(t+a^2)*(t+b^2)*(t+c^2)*(t+d^2)-(tangentValue a b c d t)^2 =
      t*(uHalf a b c d t)^2 := by
  unfold tangentValue firstSymm thirdSymm uHalf
  ring

/-- The actual pair (U,V) satisfies the Mumford congruence U | f−V², including
repeated roots of U. No division by a root or by a symmetric sum is involved. -/
theorem mumford_divides (a b c d z : R) :
    let t := X-C z
    let u := uHalf (C a) (C b) (C c) (C d) t
    let v := vHalf (C a) (C b) (C c) (C d) t
    u ∣ t*(t+(C a)^2)*(t+(C b)^2)*(t+(C c)^2)*(t+(C d)^2)-v^2 := by
  let t := (X:R[X])-C z
  let a' := C a
  let b' := C b
  let c' := C c
  let d' := C d
  let U := uHalf a' b' c' d' t
  let T := tangentValue a' b' c' d' t
  let s := firstSymm a' b' c' d'
  refine ⟨t*U + 2*s*T - s^2*U,?_⟩
  change t*(t+a'^2)*(t+b'^2)*(t+c'^2)*(t+d'^2)-(T-s*U)^2 = _
  have h : t*(t+a'^2)*(t+b'^2)*(t+c'^2)*(t+d'^2)-T^2=t*U^2 :=
    branch_tangent_identity _ _ _ _ _
  linear_combination h

/-- The ordinate V has degree at most one as a polynomial in the translated
abscissa t. This is precisely Zarhin's sign convention for genus two. -/
theorem vHalf_linear (a b c d t : R) :
    vHalf a b c d t =
      (firstSymm a b c d*(a*b+a*c+a*d+b*c+b*d+c*d)-thirdSymm a b c d)*t -
        firstSymm a b c d*(a*b*c*d) := by
  unfold vHalf tangentValue uHalf
  ring

end
end SixContactFour
#print axioms SixContactFour.branch_tangent_identity
#print axioms SixContactFour.mumford_divides
#print axioms SixContactFour.vHalf_linear

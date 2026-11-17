import ScalarIndex

namespace ProjectionFibres
open Lean.Grind StructuralReduction WitnessTransfer BinaryQuartic
attribute [local instance] Semiring.natCast Ring.intCast

variable {K : Type} [Field K]

/-- Coordinates of (t : -1 : s) on Y²Z=X³-DXZ², including infinity (0,0). -/
def OnCurve (D t s : K) : Prop := s=t^3-D*t*s^2

def slopeDen (D v a b : K) := 1+D*v*(a+b)
def slopeNum (D u v a : K) := v^2+u*v+u^2-D*a^2
def slope (D u v a b : K) := slopeNum D u v a / slopeDen D v a b
def leading (D l : K) := 1-D*l^2

/-- The restriction of the homogeneous cubic to Z=lX-bY along (T:-U:lT+bU)
has the three indicated linear factors, with multiplicities. -/
def Intersections (D l b u v h : K) : Prop :=
  leading D l≠0 ∧ ∀ T U : K,
    T^3-D*T*(l*T+b*U)^2-(l*T+b*U)*U^2 =
      leading D l*(T-u*U)*(T-v*U)*(T+h*U)

/-- Subtraction of the two curve equations before division by the unit denominator.
This also determines the slope at coinciding points. -/
theorem difference {D u v a b : K} (hu : OnCurve D u a) (hv : OnCurve D v b) :
    slopeDen D v a b*(b-a) = slopeNum D u v a*(v-u) := by
  unfold OnCurve at hu hv
  unfold slopeDen slopeNum
  grobner

theorem line_through {D u v a b : K} (hu : OnCurve D u a) (hv : OnCurve D v b)
    (live : slopeDen D v a b≠0) :
    let l:=slope D u v a b
    b=l*v+(a-l*u) := by
  dsimp only
  have eq:=difference hu hv
  have sl : slope D u v a b*slopeDen D v a b=slopeNum D u v a := Field.div_mul_cancel live
  apply cancel_unit ⟨_,Field.inv_mul_cancel live⟩
  calc slopeDen D v a b*b = slopeDen D v a b*a+slopeNum D u v a*(v-u) := by grobner
       _=slopeDen D v a b*(slope D u v a b*v+(a-slope D u v a b*u)) := by rw [←sl];grobner

private theorem cubic_factor (A B C b u v h : K)
    (sum : A*h=A*(u+v)+B)
    (secant : A*(u^2+u*v+v^2)+B*(u+v)+C=0)
    (root : A*u^3+B*u^2+C*u-b=0) (T U : K) :
    A*T^3+B*T^2*U+C*T*U^2-b*U^3=A*(T-u*U)*(T-v*U)*(T+h*U) := by
  have expansion :
      A*T^3+B*T^2*U+C*T*U^2-b*U^3-A*(T-u*U)*(T-v*U)*(T+h*U) =
        (A*u^3+B*u^2+C*u-b)*U^3+
        (A*(u^2+u*v+v^2)+B*(u+v)+C)*(T-u*U)*U^2+
        (A*(u+v)+B-A*h)*(T-u*U)*(T-v*U)*U := by grobner
  rw [root,secant,sum] at expansion
  grobner

/-- Exact projective intersection certificate, including tangent multiplicities. -/
theorem chord_factor {D u v a b : K} (hu : OnCurve D u a) (hv : OnCurve D v b)
    (d1 : slopeDen D v a b≠0)
    {l k h : K} (sl : l=slope D u v a b) (intercept : k=a-l*u)
    (d2 : leading D l≠0) (total : h=u+v-2*D*l*k/leading D l) :
    Intersections D l k u v h := by
  have through := line_through hu hv d1
  change b=slope D u v a b*v+(a-slope D u v a b*u) at through
  rw [←sl,←intercept] at through
  have au : a=l*u+k := by grobner
  have slEq : l*slopeDen D v a b=slopeNum D u v a := sl ▸ Field.div_mul_cancel d1
  have co : leading D l*(u^2+u*v+v^2)+(-2*D*l*k)*(u+v)+(-D*k^2-l)=0 := by
    unfold slopeDen slopeNum at slEq
    rw [au,through] at slEq
    unfold leading
    grobner
  have c0 : leading D l*u^3+(-2*D*l*k)*u^2+(-D*k^2-l)*u-k=0 := by
    unfold OnCurve at hu
    rw [au] at hu
    unfold leading
    grobner
  have quot : (2*D*l*k/leading D l)*leading D l=2*D*l*k := Field.div_mul_cancel d2
  have ch : leading D l*h=leading D l*(u+v)+(-2*D*l*k) := by rw [total];grobner
  refine ⟨d2,fun T U=>?_⟩
  calc _=leading D l*T^3+(-2*D*l*k)*T^2*U+(-D*k^2-l)*T*U^2-k*U^3 := by unfold leading;grobner
       _=_ := cubic_factor _ _ _ _ _ _ _ ch co c0 _ _

/-- Reflection in the ordinate takes the third intersection to (h : -1 : lh-k). -/
theorem third_on_curve {D l k u v h : K} (cert : Intersections D l k u v h) :
    OnCurve D h (l*h-k) := by
  have eq:=cert.2 (-h) 1
  unfold OnCurve
  grobner

end ProjectionFibres

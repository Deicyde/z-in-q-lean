import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

namespace ZInQBlueprint.MarkedTorsion
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

section
variable {R : Type*} [CommRing R]

def F (a b c u v : R) : R := u^3 + a*u^2*v + b*u*v^2 + c*v^3
def N (a b c u v : R) : R :=
  u^4 - 2*b*u^2*v^2 - 8*c*u*v^3 + (b^2-4*a*c)*v^4
def D (a b c u v : R) : R := 4*v*F a b c u v
def Psi (a b c u v : R) : R :=
  3*u^4 + 4*a*u^3*v + 6*b*u^2*v^2 + 12*c*u*v^3 + (4*a*c-b^2)*v^4

theorem three_identity (a b c u v:R) :
    N a b c u v*v - D a b c u v*u = -v*Psi a b c u v := by
  unfold N D F Psi; ring

end

def twist (a b c d : ℚ) : WeierstrassCurve ℚ := ⟨0,a*d,0,b*d^2,c*d^3⟩

/-- A homogeneous pair represents the normalized abscissa x/d, including infinity. -/
def Represents {a b c d : ℚ} (P:(twist a b c d).toAffine.Point) (u v : ℚ) : Prop :=
  match P with
  | .zero => v=0
  | .some x _ _ => d*u=x*v

theorem curve_eq {a b c d x y : ℚ} (valid:(twist a b c d).toAffine.Nonsingular x y) :
    y^2 = x^3+(a*d)*x^2+(b*d^2)*x+c*d^3 := by
  have h := valid.1
  rw [WeierstrassCurve.Affine.equation_iff] at h
  dsimp [twist] at h
  linear_combination h

private theorem tangent_identity (a b c d t y : ℚ) (dn:d≠0) (yn:y≠0)
    (e:y^2=d^3*F a b c t 1) :
    d*N a b c t 1 =
      (((3*(d*t)^2+2*(a*d)*(d*t)+b*d^2)/(2*y))^2-a*d-d*t-d*t)*D a b c t 1 := by
  have ff:F a b c t 1=y^2/d^3 := by field_simp;linear_combination -e
  unfold D
  rw [ff]
  unfold N
  field_simp
  unfold F at e
  rw [e];ring

theorem represents_double {a b c d u v : ℚ} (dn:d≠0)
    (P:(twist a b c d).toAffine.Point) (rep:Represents P u v) :
    Represents (P+P) (N a b c u v) (D a b c u v) := by
  cases P with
  | zero => change v=0 at rep; subst v; change D a b c u 0=0; simp [D]
  | some x y valid =>
    change d*u=x*v at rep
    let t:=x/d
    have xt : x=d*t := by dsimp [t];field_simp
    have uv : u=t*v := by dsimp [t];field_simp; linear_combination rep
    have fn : F a b c (t*v) v = v^3*F a b c t 1 := by unfold F; ring
    have dd : D a b c u v = v^4 * D a b c t 1 := by rw [uv]; unfold D; rw [fn]; ring
    have nn : N a b c u v = v^4 * N a b c t 1 := by rw [uv]; unfold N; ring
    have curve:=curve_eq valid
    rw [xt] at curve
    have e:y^2=d^3*F a b c t 1 := by unfold F;linear_combination curve
    by_cases yzero:y=0
    · have hy : y=(twist a b c d).toAffine.negY x y := by simp [twist,negY,yzero]
      rw [add_self_of_Y_eq hy]
      change D a b c u v=0
      have ff:F a b c t 1=0 := by simpa [yzero,dn] using e.symm
      rw [dd];simp [D,ff]
    · have hy : y≠(twist a b c d).toAffine.negY x y := by
        simp [twist,negY];intro eq; apply yzero;linarith
      rw [add_self_of_Y_ne hy]
      change d*N a b c u v=(twist a b c d).toAffine.addX x x
        ((twist a b c d).toAffine.slope x x y y)*D a b c u v
      rw [nn,dd,slope_of_Y_ne rfl hy]
      have h:=tangent_identity a b c d t y dn yzero e
      simp only [twist,addX,negY,zero_mul,sub_zero,add_zero,sub_neg_eq_add]
      rw [show y+y=2*y by ring,xt]
      linear_combination v^4*h

theorem cross {a b c d u v s t : ℚ} (dn:d≠0) (P:(twist a b c d).toAffine.Point)
    (p:Represents P u v) (q:Represents P s t) : u*t=v*s := by
  cases P with
  | zero => change v=0 at p; change t=0 at q; simp [p,q]
  | some x y valid =>
    change d*u=x*v at p;change d*s=x*t at q
    apply mul_left_cancel₀ dn
    linear_combination t*p-v*q

theorem represents_neg {a b c d u v : ℚ} (P:(twist a b c d).toAffine.Point) :
    Represents (-P) u v ↔ Represents P u v := by cases P <;> rfl

end ZInQBlueprint.MarkedTorsion
#print axioms ZInQBlueprint.MarkedTorsion.represents_double
#print axioms ZInQBlueprint.MarkedTorsion.cross

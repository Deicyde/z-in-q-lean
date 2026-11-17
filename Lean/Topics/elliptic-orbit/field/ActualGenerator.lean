import QuadraticFieldBridge
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.LinearCombination

namespace EllipticOrbit.Field
open WeierstrassCurve.Affine

def E : WeierstrassCurve K := ⟨0,0,0,-D,0⟩
abbrev Point := E.toAffine.Point

theorem discriminant : E.Δ=64*D^3 := by
  simp only [WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,
    WeierstrassCurve.b₈,E]
  ring

instance : E.IsElliptic := ⟨isUnit_iff_ne_zero.mpr (by
  rw [discriminant]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ D_ne_zero))⟩

theorem equation (x y : K) : E.toAffine.Equation x y ↔ y^2=x^3-D*x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [E,sub_eq_add_neg]

def coordinates : Point → Option (K×K)
  | .zero => none
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y _ => some (x,y)

theorem coordinates_injective : Function.Injective coordinates := by
  intro S T eq
  cases S <;> cases T <;> simp_all [coordinates]

theorem negY (x y : K) : E.toAffine.negY x y= -y := by simp [WeierstrassCurve.Affine.negY,E]

def xR : K := ofPair (1,1)
def yR : K := ofPair (0,2)

theorem generator_affine : (xR,yR)=(1+r,2*r) := by
  apply Prod.ext <;> ext <;>
    norm_num [xR,yR,ofPair,r,QuadraticAlgebra.omega,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat,
      QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]

theorem generator_equation : E.toAffine.Equation xR yR := by
  apply (equation ..).mpr
  ext <;> norm_num [xR,yR,ofPair,pow_succ,D]

theorem generator_nonsingular : E.toAffine.Nonsingular xR yR :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular (W:=E)).mp generator_equation

def R : Point := .some generator_nonsingular
def P : Point := (2:ℕ) • R

theorem R_coordinates : coordinates R=some (1+r,2*r) := congrArg some generator_affine
theorem P_is_double : P=R+R := two_nsmul R

def doubleX (x y : K) : K := E.toAffine.addX x x (E.toAffine.slope x x y y)
def doubleY (x y : K) : K := E.toAffine.addY x x y (E.toAffine.slope x x y y)

theorem nonvertical {x y : K} (hy : y≠0) : y≠E.toAffine.negY x y := by
  rw [negY]
  exact fun h=>hy (by linear_combination h/2)

theorem double_coordinates {x y : K} (nonsing : E.toAffine.Nonsingular x y) (hy : y≠0) :
    coordinates ((2:ℕ) • (WeierstrassCurve.Affine.Point.some nonsing : Point))=
      some (doubleX x y,doubleY x y) := by
  rw [two_nsmul,WeierstrassCurve.Affine.Point.add_self_of_Y_ne (nonvertical hy)]
  rfl

theorem tangent {x y : K} (hy : y≠0) : E.toAffine.slope x x y y=(3*x^2-D)/(2*y) := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl (nonvertical hy),negY]
  simp [E,sub_eq_add_neg,two_mul]

private theorem slopeR : E.toAffine.slope xR xR yR yR=ofPair (3,-1/4) := by
  rw [tangent (by decide : yR≠0)]
  apply (div_eq_iff (mul_ne_zero (by norm_num) (by decide : yR≠0))).mpr
  ext <;> norm_num [ofPair,xR,yR,D,pow_two,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]

theorem P_pair :
    coordinates P=some (ofPair (57/8,-7/2),ofPair (-165/8,417/32)) := by
  rw [P,R,double_coordinates generator_nonsingular (by decide : yR≠0)]
  apply congrArg some
  apply Prod.ext <;>
    simp only [doubleX,doubleY,slopeR,WeierstrassCurve.Affine.addX,WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY,negY] <;>
    ext <;> norm_num [E,ofPair,xR,yR,pow_two]

theorem P_abscissa :
    (coordinates P).map Prod.fst=some ((57-28*r)/8) := by
  rw [P_pair]
  apply congrArg some
  change ofPair (57/8,-7/2)=(57-28*r)/8
  apply (eq_div_iff (by norm_num : (8:K)≠0)).mpr
  ext <;> norm_num [ofPair,r,QuadraticAlgebra.omega,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]

#print axioms discriminant
#print axioms equation
#print axioms coordinates_injective
#print axioms generator_nonsingular
#print axioms R_coordinates
#print axioms P_is_double
#print axioms double_coordinates
#print axioms tangent
#print axioms P_pair
#print axioms P_abscissa
end EllipticOrbit.Field

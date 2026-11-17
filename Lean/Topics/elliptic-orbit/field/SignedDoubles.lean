import ActualGenerator

namespace EllipticOrbit.Field
open PhysicalProjection.Comparison (Q2)
open PhysicalProjection.RootOrdinate (root)

theorem quartic_nonsingular {h j : Q2} (chart : root h j) :
    E.toAffine.Nonsingular ((ofPair h)^2) (ofPair h*ofPair j) := by
  apply (WeierstrassCurve.Affine.equation_iff_nonsingular (W:=E)).mp
  apply (equation ..).mpr
  rw [mul_pow,(root_iff ..).mp chart]
  ring

def chartPoint {h j : Q2} (chart : root h j) : Point := .some (quartic_nonsingular chart)

/-- A finite signed point presented in the literal two rational coefficients. -/
def SignedPoint (Q : Point) : Prop :=
  ∃ (h j : Q2) (chart : root h j), Q=chartPoint chart

def rootParameter (x y : K) := (x^2+D)/(2*y)

theorem double_abscissa_square {x y : K} (onCurve : y^2=x^3-D*x) (hy : y≠0) :
    doubleX x y=(rootParameter x y)^2 := by
  let s:=(3*x^2-D)/(2*y)
  have nz : 2*y≠0 := mul_ne_zero (by norm_num) hy
  have sl : s*(2*y)=3*x^2-D := div_mul_cancel₀ _ nz
  have rt : rootParameter x y*(2*y)=x^2+D := div_mul_cancel₀ _ nz
  have xcoord : doubleX x y=s^2-2*x := by
    rw [doubleX,tangent hy]
    simp only [WeierstrassCurve.Affine.addX,E,s,zero_mul,add_zero,sub_zero]
    ring
  rw [xcoord]
  apply mul_right_cancel₀ (pow_ne_zero 2 nz)
  calc
    (s^2-2*x)*(2*y)^2 = (s*(2*y))^2-8*x*y^2 := by ring
    _ = (x^2+D)^2 := by rw [sl,onCurve]; ring
    _ = (rootParameter x y)^2*(2*y)^2 := by rw [←rt];ring

theorem finite_double_signed {x y : K} (nonsing : E.toAffine.Nonsingular x y) (hy : y≠0) :
    SignedPoint ((2:ℕ) • (WeierstrassCurve.Affine.Point.some nonsing : Point)) := by
  let h:=rootParameter x y
  let j:=doubleY x y/h
  have hn : h≠0 := div_ne_zero (square_plus_D_ne_zero x) (mul_ne_zero (by norm_num) hy)
  have ordinate : h*j=doubleY x y := by
    rw [mul_comm]; exact div_mul_cancel₀ _ hn
  have abscissa : doubleX x y=h^2 := double_abscissa_square ((equation ..).mp nonsing.1) hy
  have doubleNS := WeierstrassCurve.Affine.nonsingular_add nonsing nonsing
    (fun bad=>nonvertical hy bad.2)
  have cubic : (doubleY x y)^2=(doubleX x y)^3-D*doubleX x y :=
    (equation ..).mp doubleNS.1
  have quartic : j^2=h^4-D := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hn)
    calc
      h^2*j^2 = (h*j)^2 := by rw [mul_pow]
      _ = (h^2)^3-D*h^2 := by rw [ordinate,←abscissa,cubic]
      _ = h^2*(h^4-D) := by ring
  have physical : root (coeffs h) (coeffs j) := (root_iff ..).mpr (by simpa using quartic)
  refine ⟨coeffs h,coeffs j,physical,coordinates_injective ?_⟩
  rw [double_coordinates nonsing hy]
  change some (doubleX x y,doubleY x y)=some ((ofPair (coeffs h))^2,ofPair (coeffs h)*ofPair (coeffs j))
  rw [ofPair_coeffs,ofPair_coeffs,ordinate,abscissa]

/-- Every nonzero double has an actual finite signed quartic presentation. -/
theorem double_signed (Q : Point) : (2:ℕ) • Q=0 ∨ SignedPoint ((2:ℕ) • Q) := by
  cases Q with
  | zero => exact Or.inl (nsmul_zero 2)
  | @some x y nonsing =>
    by_cases hy : y=0
    · left
      rw [two_nsmul]
      apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
      rw [negY,hy,neg_zero]
    · exact Or.inr (finite_double_signed nonsing hy)

theorem nsmul_P_signed (n : ℕ) : n • P=0 ∨ SignedPoint (n • P) := by
  have eq : n • P=(2:ℕ) • (n • R) := by rw [P_is_double,nsmul_add,two_nsmul]
  rw [eq]
  exact double_signed _

theorem zsmul_P_signed (n : ℤ) : n • P=0 ∨ SignedPoint (n • P) := by
  have eq : n • P=(2:ℕ) • (n • R) := by rw [P_is_double,zsmul_add,two_nsmul]
  rw [eq]
  exact double_signed _

#print axioms quartic_nonsingular
#print axioms double_abscissa_square
#print axioms finite_double_signed
#print axioms double_signed
#print axioms nsmul_P_signed
#print axioms zsmul_P_signed
end EllipticOrbit.Field

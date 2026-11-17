import DiscEquations

/-! Explicit factorizations of the residual cubics at the two singular branches. -/
namespace ZInQBlueprint.ResidualFactors
open Polynomial ZInQBlueprint.DiscEquations ZInQBlueprint.ClusterCharts
noncomputable section
variable {R : Type*} [CommRing R]

def contactProduct (A B : R) : R := A*(A+15*B)*(A+20*B)*(A+24*B)*(A+30*B)*(A+60*B)
def poleForm (A B : R) : R := 7*A^2+300*A*B+3600*B^2

/-- Homogeneous division by the pole quadratic leaves a cube. -/
theorem pole_remainder (A B : R) :
    343*contactProduct A B-14400*B^3*(A-30*B)^3 =
      poleForm A B*(49*A^4+5201*A^3*B+156150*A^2*B^2+1215000*A*B^3+108000*B^4) := by
  unfold contactProduct poleForm
  ring

theorem zero_centres {d : R} (hd : d^2 = 6) :
    q₀ (-8+4*d) = 0 ∧ q₀ (-8-4*d) = 0 := by
  unfold q₀
  constructor <;> linear_combination 16*hd

/-- The two residual radicands are signed prime-field scalars times squares. -/
theorem zero_coefficients {d : R} (hd : d^2=6) (u : R) :
    let a := -8+4*d
    let b := -8-4*d
    (d*u)*slope₀ a = 4*(2*a+16)^3*((-48*u)*(d-2)^2) ∧
    (d*u)*slope₀ b = 4*(2*b+16)^3*((48*u)*(d+2)^2) := by
  dsimp [slope₀]
  constructor
  · linear_combination 6144*d^2*u*(d^2+4*d-10)*hd
  · linear_combination -6144*d^2*u*(d^2-4*d-10)*hd

private theorem zero_factor {a U w : R} (h : U*slope₀ a = 4*(2*a+16)^3*w^2) :
    zeroResidual a U = C (-4*(2*a+16)^3)*X*(X-C w)*(X+C w) := by
  rw [zeroResidual,h]
  simp [map_ofNat]
  ring

theorem zero_factors {d u v z : R} (hd : d^2=6) (hv : v^2= -48*u) (hz : z^2=48*u) :
    let a := -8+4*d
    let b := -8-4*d
    zeroResidual a (d*u) =
      C (-4*(2*a+16)^3)*X*(X-C (v*(d-2)))*(X+C (v*(d-2))) ∧
    zeroResidual b (d*u) =
      C (-4*(2*b+16)^3)*X*(X-C (z*(d+2)))*(X+C (z*(d+2))) := by
  constructor
  · apply zero_factor
    rw [mul_pow,hv]
    exact (zero_coefficients hd u).1
  · apply zero_factor
    rw [mul_pow,hz]
    exact (zero_coefficients hd u).2

theorem pole_centres {s : R} (hs : s^2=2) :
    qPole (-1+s)=0 ∧ qPole (-1-s)=0 := by
  unfold qPole
  constructor <;> linear_combination hs

theorem pole_first {a : R} (ha : qPole a=0) :
    firstPole a = 8*(2*a+2)^3*a^3 := by
  unfold firstPole
  unfold qPole at ha
  linear_combination (-68*a^4-56*a^3-64*a^2+8*a+4)*ha

/-- A cube root of unity and a single chosen cube root work at both centres. -/
theorem pole_factor {a U v z : R} (ha : qPole a=0)
    (hv : 3*v^3= -8*U) (hz : z^2+z+1=0) :
    poleResidual a U = C (729*3*(2*a+2)^3)*
      ((X-C (a*v))*(X-C (z*(a*v)))*(X-C (z^2*(a*v)))) := by
  rw [poleResidual,pole_first ha]
  have z3 : z^3 = 1 := by linear_combination (z-1)*hz
  have prod_id (b : R) : (X-C b)*(X-C (z*b))*(X-C (z^2*b)) = X^3-C (b^3) := by
    have H : (C z : R[X])^2+C z+1=0 := by simpa using congrArg (C : R →+* R[X]) hz
    have H3 : (C z : R[X])^3=1 := by simpa using congrArg (C : R →+* R[X]) z3
    simp only [map_mul,map_pow]
    linear_combination (-C b*X^2+(C b)^2*X)*H + ((C b)^2*X-(C b)^3)*H3
  rw [prod_id]
  have H : 3*(C v : R[X])^3= -8*C U := by simpa [map_ofNat] using congrArg (C : R →+* R[X]) hv
  simp [map_ofNat]
  linear_combination (729*(2*C a+2)^3*(C a)^3)*H

variable {K : Type*} [Field K] [NeZero (2:K)] [NeZero (3:K)] [NeZero (5:K)] [NeZero (7:K)]
/-- The actual inverse-parameter unit is a cube after multiplication by −8/3. -/
theorem pole_cube {A B d D U : K} (hG : poleForm A B=0) (hF : contactProduct A B ≠ 0)
    (hd : d^2=6) (hU : 240*d*contactProduct A B*U = D^3) :
    ∃ v : K, 3*v^3 = -8*U := by
  have h7 := NeZero.ne (7:K)
  have h3240 : (3240:K) ≠ 0 := by
    have hfac : (3240:K) = 2^3*3^4*5 := by norm_num
    rw [hfac]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (NeZero.ne (2:K)))
      (pow_ne_zero _ (NeZero.ne (3:K)))) (NeZero.ne (5:K))
  let b := 360*B*(30*B-A)/7
  have hb : b^3 = -3240*contactProduct A B := by
    dsimp [b]
    field_simp
    have h := pole_remainder A B
    rw [hG,zero_mul] at h
    linear_combination 3240*h
  have hb0 : b ≠ 0 := by
    intro h
    rw [h,zero_pow (by decide : 3 ≠ 0)] at hb
    exact (mul_ne_zero (neg_ne_zero.mpr h3240) hF) hb.symm
  refine ⟨d*D/b, ?_⟩
  field_simp
  rw [hb,← hU]
  linear_combination 720*(d^2+6)*contactProduct A B*U*hd

omit [NeZero (7:K)] in
/-- At a pole the base residue field already contains the third roots of unity. -/
theorem pole_unity {A B : K} (hG : poleForm A B=0) (hB : B ≠ 0) :
    ∃ z : K, z^2+z+1=0 := by
  have h60 : (60:K) ≠ 0 := by
    have h : (60:K)=2^2*3*5 := by norm_num
    rw [h]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (NeZero.ne (2:K))) (NeZero.ne (3:K))) (NeZero.ne (5:K))
  refine ⟨(7*A+120*B)/(60*B),?_⟩
  field_simp
  unfold poleForm at hG
  linear_combination 7*hG

end
end ZInQBlueprint.ResidualFactors
#print axioms ZInQBlueprint.ResidualFactors.pole_remainder
#print axioms ZInQBlueprint.ResidualFactors.zero_centres
#print axioms ZInQBlueprint.ResidualFactors.zero_coefficients
#print axioms ZInQBlueprint.ResidualFactors.zero_factors
#print axioms ZInQBlueprint.ResidualFactors.pole_centres
#print axioms ZInQBlueprint.ResidualFactors.pole_first
#print axioms ZInQBlueprint.ResidualFactors.pole_factor
#print axioms ZInQBlueprint.ResidualFactors.pole_cube
#print axioms ZInQBlueprint.ResidualFactors.pole_unity

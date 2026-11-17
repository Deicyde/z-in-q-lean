import JointKernels
import QuotientGroup

/-! Five simultaneous squareclasses, and the elliptic curve from the four finite branch points. -/
namespace ZInQBlueprint.FiveCovers
open Finset Height Sun28.Ordinary Sun28.HeightFibres Sun28.FiveMarkUnits Sun28.ScalarQuotients
open ZInQBlueprint.OriginalHeightCount ZInQ.RouteK
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
noncomputable section
set_option exponentiation.threshold 1000
attribute [local irreducible] glazerConstant24

theorem weight_at_failure {x : ℚ} {B K : ℕ} (atx : x∈exceptions B)
    (threshold : Real.log (B:ℝ) ≤ ((K+1:ℕ):ℝ)^24) : weight x.num x.den≤K := by
  obtain ⟨box,off,fail⟩ := (mem_exceptions x B).mp atx
  have cop : Int.gcd x.num (x.den:ℤ)=1 := by simpa [Int.gcd] using x.reduced.gcd_eq_one
  have cap : (weight x.num x.den:ℝ) ≤ 22050*(heightRadical x.num x.den:ℝ) := by
    exact_mod_cast weight_bound cop off
  have c : (22050:ℝ)^24≤2^810 := by norm_num
  have p := pow_le_pow_left₀ (by positivity) cap 24
  rw [mul_pow] at p
  have small := (p.trans ((mul_le_mul_of_nonneg_right c (by positivity)).trans
    (original_margin x.num x.den))).trans_lt fail
  rw [Rat.logHeight₁_eq_log_max] at small
  have live : 0 < max x.num.natAbs x.den := x.den_pos.trans_le (le_max_right ..)
  have upper := Real.log_le_log (by exact_mod_cast live : 0<((max x.num.natAbs x.den:ℕ):ℝ))
    (by exact_mod_cast box : ((max x.num.natAbs x.den:ℕ):ℝ)≤(B:ℝ))
  by_contra! large
  have g : ((K+1:ℕ):ℝ)≤weight x.num x.den := by exact_mod_cast large
  exact (not_le_of_gt ((small.trans_le upper).trans_le threshold)) (pow_le_pow_left₀ (by positivity) g 24)

/-- A single diagonal system with a joint product bound for all five coefficients. -/
theorem simultaneous_squareclasses {x : ℚ} {B K : ℕ} (atx : x∈exceptions B)
    (threshold : Real.log (B:ℝ) ≤ ((K+1:ℕ):ℝ)^24) :
    ∃ d u : Fin 5 → ℤ, (∀ i, Squarefree (d i) ∧ u i≠0 ∧ oldForm i x.num x.den=d i*(u i)^2) ∧
      (∏ i,(d i).natAbs)≤K := by
  have off := ((mem_exceptions x B).mp atx).2.1
  have rows (i : Fin 5) : ∃ u : ℤ, Squarefree (kernel i x.num x.den) ∧ u≠0 ∧
      oldForm i x.num x.den=kernel i x.num x.den*u^2 := by
    obtain ⟨s,u,nu,e⟩:=sqfInt_spec (off i)
    exact ⟨u,s,nu,e⟩
  choose u hu using rows
  exact ⟨fun i=>kernel i x.num x.den,u,hu,weight_at_failure atx threshold⟩

def finiteProduct (A B : ℤ) := A*(A-B)*(A-2401*B)*(32*A+343*B)
def twistCoefficient (A B : ℤ) := sqfInt (finiteProduct A B)
def finiteQuartic (s : ℚ) := s*(s-1)*(s-2401)*(32*s+343)
def coordinate (s : ℚ) := (2401-s)/(75*s)

theorem four_mark_identity {s : ℚ} (nz : s≠0) :
    21*cubic 1 (coordinate s)=finiteQuartic s*(343/(375*s^2))^2 := by
  unfold cubic coordinate finiteQuartic
  field_simp
  ring

theorem four_mark_squareclass {A B : ℤ} (b : B≠0) (off : ∀ i,oldForm i A B≠0) :
    ∃ y : ℚ, y≠0 ∧ finiteQuartic ((A:ℚ)/B)=(twistCoefficient A B:ℚ)*y^2 := by
  have an : A≠0 := off 1
  have all := mul_ne_zero (mul_ne_zero (mul_ne_zero an (off 2)) (off 3)) (off 4)
  obtain ⟨_,u,nu,eq⟩:=sqfInt_spec (show finiteProduct A B≠0 from all)
  have den : (B:ℚ)≠0 := by exact_mod_cast b
  have re : (A:ℚ)*(A-B)*(A-2401*B)*(32*A+343*B)=(twistCoefficient A B:ℚ)*(u:ℚ)^2 := by
    exact_mod_cast eq
  refine ⟨(u:ℚ)/(B:ℚ)^2,div_ne_zero (by exact_mod_cast nu) (pow_ne_zero _ den),?_⟩
  unfold finiteQuartic
  field_simp
  linear_combination re

/-- Every original off-mark slope supplies an infinite-order rational point on its four-mark twist. -/
theorem infinite_order_of_slope (mazur : MazurExponentList) {A B : ℤ} (off : ∀ i,oldForm i A B≠0) :
    ∃ P:(elliptic (21*(twistCoefficient A B:ℚ))).toAffine.Point, ¬IsOfFinAddOrder P := by
  let s:ℚ:=(A:ℚ)/B
  let d:ℚ:=twistCoefficient A B
  have b:B≠0:=off 0
  have a:A≠0:=off 1
  have nz : s≠0 := div_ne_zero (by exact_mod_cast a) (by exact_mod_cast b)
  obtain ⟨y,ny,eq⟩:=four_mark_squareclass b off
  have dn : d≠0 := by
    have all := mul_ne_zero (mul_ne_zero (mul_ne_zero a (off 2)) (off 3)) (off 4)
    change ((sqfInt (finiteProduct A B):ℤ):ℚ)≠0
    exact_mod_cast (sqfInt_spec (show finiteProduct A B≠0 from all)).1.ne_zero
  let m:=21*d
  let X:=m*coordinate s
  let c:ℚ:=343/(375*s^2)
  let Y:=21*d^2*y*c
  have mn : m≠0 := mul_ne_zero (by norm_num) dn
  have yn : Y≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ dn)) ny)
    (div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) (pow_ne_zero _ nz)))
  have q:=four_mark_identity nz
  change finiteQuartic s=d*y^2 at eq
  rw [eq] at q
  have e : Y^2=cubic m X := by
    dsimp only [X,Y,m,c,cubic] at *
    linear_combination -441*d^3*q
  have delta:(elliptic m).Δ≠0:=by rw [discriminant];positivity [mn]
  have ns:=(WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero delta).mp ((Sun28.ScalarQuotients.equation_iff ..).mpr e)
  refine ⟨some X Y ns,fun tors=>?_⟩
  have two := (torsion_iff_two mazur mn _).mp tors
  rw [two_nsmul] at two
  have neg : Y≠(elliptic m).toAffine.negY X Y := by
    simp only [elliptic,WeierstrassCurve.Affine.negY,zero_mul,sub_zero]; intro h;apply yn;linarith
  rw [add_self_of_Y_ne neg] at two
  exact some_ne_zero _ two

end
end ZInQBlueprint.FiveCovers
#print axioms ZInQBlueprint.FiveCovers.weight_at_failure
#print axioms ZInQBlueprint.FiveCovers.simultaneous_squareclasses
#print axioms ZInQBlueprint.FiveCovers.four_mark_identity
#print axioms ZInQBlueprint.FiveCovers.four_mark_squareclass
#print axioms ZInQBlueprint.FiveCovers.infinite_order_of_slope

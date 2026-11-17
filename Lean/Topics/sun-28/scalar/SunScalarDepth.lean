import SunDouble
import Mathlib.Algebra.Order.GroupWithZero.WithZero

namespace Sun28.Scalar
open WeierstrassCurve.Affine
noncomputable section
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]
variable (w : AddValuation K (WithTop ℤ))

omit [CharZero K] [DecidableEq K] in
theorem finite_order {a : K} (hn : a≠0) : ∃ d : ℤ, w a=(d:WithTop ℤ) := by
  obtain ⟨d,hd⟩ := WithTop.ne_top_iff_exists.mp ((w.ne_top_iff).mpr hn)
  exact ⟨d,hd.symm⟩

omit [CharZero K] [DecidableEq K] in
private theorem positive_sum {c t : K} (hc : 0≤w c) {d : ℤ} (hd : 0<d)
    (ht : w t=(d:WithTop ℤ)) (n : ℕ) (hn : 0<n) :
    0 < w (c*t^n) := by
  rw [w.map_mul,w.map_pow,ht]
  have hnz : (0:WithTop ℤ)<n • (d:WithTop ℤ) := by
    exact_mod_cast (show (0:ℤ)<n • d from by simp only [nsmul_eq_mul]; positivity)
  exact lt_of_lt_of_le hnz (by simpa using add_le_add_left hc (n • (d:WithTop ℤ)))

omit [DecidableEq K] in
/-- The reciprocal abscissa has twice the parameter order in the neighborhood of infinity. -/
theorem formal_parameter {b x y : K} (hb : 0≤w b) (h : (curve b).Nonsingular x y)
    {a : ℤ} (ha : 0<a) (hx : w x⁻¹=(a:WithTop ℤ)) :
    ∃ d : ℤ, 0<d ∧ w (-x/y)=(d:WithTop ℤ) ∧ a=2*d := by
  have xn : x≠0 := by rintro rfl; simp at hx
  have plus : w (1+b*(x⁻¹)^2)=0 := by
    rw [w.map_add_eq_of_lt_left]
    · exact w.map_one
    · rw [w.map_one];exact positive_sum w hb ha hx 2 (by decide)
  have un : 1+b*(x⁻¹)^2≠0 := by
    intro he
    rw [he,w.map_zero] at plus
    exact WithTop.top_ne_coe (a:=0) plus
  have fact : y^2=x^3*(1+b*(x⁻¹)^2) := by
    rw [equation h]
    field_simp [xn]
  have yn : y≠0 := fun hy => (mul_ne_zero (pow_ne_zero 3 xn) un) (by rw [←fact,hy];norm_num)
  have he : x⁻¹=(-x/y)^2*(1+b*(x⁻¹)^2) := by
    field_simp [xn,yn]
    grind [equation h]
  obtain ⟨d,hd⟩ := finite_order w (div_ne_zero (neg_ne_zero.mpr xn) yn)
  have e := congrArg w he
  rw [hx,w.map_mul,w.map_pow,hd,plus,add_zero] at e
  have ed : a=2*d := by exact_mod_cast e
  exact ⟨d,by omega,hd,ed⟩

/-- Positive parameter order on either zero branch implies that the actual doubled point
is formal and has exactly the original order. -/
theorem double_parameter {b : K} (hb : 0≤w b) (h2 : w (2:K)=0)
    (Q : (curve b).Point) {d : ℤ} (hd : 0<d) (hz : w (parameter Q)=(d:WithTop ℤ)) :
    w (parameter ((2:ℕ) • Q))=(d:WithTop ℤ) ∧
    w (reciprocal ((2:ℕ) • Q))=((2*d:ℤ):WithTop ℤ) := by
  cases Q with
  | zero => simp [parameter] at hz
  | some x y h =>
    change w (-x/y)=(d:WithTop ℤ) at hz
    have yn : y≠0 := by rintro rfl; simp at hz
    obtain ⟨u,v,hu,q,e⟩ := double_coordinates h yn
    let t := -x/y
    have h4 : w (4:K)=0 := by rw [show (4:K)=2*2 by norm_num,w.map_mul,h2,zero_add]
    have h4b : 0≤w ((4:K)*b) := by simpa only [w.map_mul,h4,zero_add] using hb
    have rhs : w (1-4*b*t^4)=0 := by
      rw [w.map_sub_eq_of_lt_left]
      · exact w.map_one
      · rw [w.map_one]; exact positive_sum w h4b hd hz 4 (by decide)
    change u*(4*t^2)=1-4*b*t^4 at e
    have un : u≠0 := by
      intro he
      rw [←e,he,zero_mul,w.map_zero] at rhs
      exact WithTop.top_ne_coe (a:=0) rhs
    obtain ⟨i,hi⟩ := finite_order w un
    rw [←e,w.map_mul,w.map_mul,hi,h4,w.map_pow,hz,zero_add] at rhs
    have ev : i+2*d=0 := by exact_mod_cast rhs
    have hr : w u⁻¹=((2*d:ℤ):WithTop ℤ) := by
      rw [w.map_inv,hi,show 2*d= -i by omega]
      rfl
    obtain ⟨j,_,hj,eq⟩ := formal_parameter w hb hu (by omega) hr
    obtain rfl : j=d := by omega
    rw [q]
    exact ⟨hj,hr⟩

#print axioms formal_parameter
#print axioms double_parameter
end
end Sun28.Scalar

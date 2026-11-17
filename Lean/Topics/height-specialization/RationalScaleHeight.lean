import Assembly

namespace HeightSpecialization
open IndependentIndices IndependentIndices.Assembly

abbrev H := multiplicativeHeight

theorem height_mul (x y : Rat) : H (x*y) ≤ H x * H y := by
  obtain ⟨g, nz, en, ed⟩ := Rat.normalize_num_den' (x.num*y.num) (x.den*y.den)
    (Nat.mul_ne_zero x.den_nz y.den_nz)
  rw [← Rat.mul_def] at en ed
  have one : 1 ≤ g := by omega
  have num := congrArg Int.natAbs en
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at num
  have lower (n : Nat) : n ≤ n*g := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left n one
  apply Nat.max_le.mpr
  constructor
  · apply Nat.le_trans (lower _)
    rw [←num]
    exact Nat.mul_le_mul (Nat.le_max_left ..) (Nat.le_max_left ..)
  · apply Nat.le_trans (lower _)
    rw [←ed]
    exact Nat.mul_le_mul (Nat.le_max_right ..) (Nat.le_max_right ..)

theorem height_inv (x : Rat) (nz : x≠0) : H x⁻¹=H x := by
  have live : x.num≠0 := fun eq => nz (Rat.num_eq_zero.mp eq)
  simp only [H, multiplicativeHeight, Rat.num_inv, Rat.den_inv, if_neg live, Int.natAbs_mul,
    Int.natAbs_sign_of_ne_zero live, Int.natAbs_natCast, Nat.one_mul, Nat.max_comm x.den]

theorem height_pow (x : Rat) (n : Nat) : H (x^n)=(H x)^n := by
  simp only [H, multiplicativeHeight, Rat.den_pow, Rat.num_pow, Int.natAbs_pow]
  rcases Nat.le_total x.num.natAbs x.den with h|h
  · rw [Nat.max_eq_right h, Nat.max_eq_right (Nat.pow_le_pow_left h n)]
  · rw [Nat.max_eq_left h, Nat.max_eq_left (Nat.pow_le_pow_left h n)]

/-- Translation by 1 leaves the denominator of a rational square in lowest terms. -/
theorem one_add_square_num (x : Rat) :
    (1+x^2).num = ((x.den^2+x.num.natAbs^2 : Nat) : Int) := by
  have e := reduced_num 1 (-(x^2))
  have h : ((1:Int):Rat)-(-(x^2))=1+x^2 := by grobner
  rw [h] at e
  change (1+x^2).num = 1*((x.den^2 : Nat) : Int) - -(x.num^2) at e
  have sq : ((x.num.natAbs^2 : Nat) : Int)=x.num^2 := by
    rw [← Int.natAbs_pow]
    exact Int.natAbs_of_nonneg (Int.sq_nonnneg x.num)
  rw [Int.natCast_add, sq]
  omega

theorem height_one_add_square (x : Rat) : (H x)^2 ≤ H (1+x^2) := by
  have numle : (1+x^2).num.natAbs ≤ H (1+x^2) := Nat.le_max_left ..
  rw [one_add_square_num, Int.natAbs_natCast] at numle
  change (max x.num.natAbs x.den)^2 ≤ H (1+x^2)
  rcases Nat.le_total x.num.natAbs x.den with h|h
  · rw [Nat.max_eq_right h]; omega
  · rw [Nat.max_eq_left h]; omega

/-- The three rational slopes bound the two coefficients at once, also when one is zero. -/
theorem scale_heights {l a b : Rat} {U : Nat} (nz : l≠0) (base : H l≤U)
    (first : H (a^2*l)≤U) (second : H ((1+b^2)^2*l)≤U) :
    H a≤U ∧ (H b)^2≤U ∧ (H a*H b)^2≤U^3 := by
  have cancel (x : Rat) (bound : H (x^2*l)≤U) : H x≤U := by
    have e := height_mul (x^2*l) l⁻¹
    rw [← Rat.div_def, Rat.mul_div_cancel nz, height_pow, height_inv l nz] at e
    have ee : (H x)^2 ≤ U^2 := by
      exact Nat.le_trans e (by simpa only [Nat.pow_two] using Nat.mul_le_mul bound base)
    exact Nat.le_of_not_gt fun bad => (Nat.not_lt_of_ge ee) (Nat.pow_lt_pow_left bad (by decide))
  have ha := cancel a first
  have hb := Nat.le_trans (height_one_add_square b) (cancel (1+b^2) second)
  refine ⟨ha,hb,?_⟩
  rw [Nat.mul_pow, Nat.pow_succ U 2]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left ha 2) hb

#print axioms height_mul
#print axioms height_pow
#print axioms one_add_square_num
#print axioms height_one_add_square
#print axioms scale_heights
end HeightSpecialization

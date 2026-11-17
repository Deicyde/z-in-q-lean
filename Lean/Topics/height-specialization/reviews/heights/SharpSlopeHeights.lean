import RationalScaleHeight

namespace HeightSpecialization
open IndependentIndices.Assembly

/-- A nonzero reduced fraction has nonzero numerator and denominator. -/
theorem strict_square_height {x : Rat} (nz : x ≠ 0) :
    (H x)^2 + 1 ≤ H (1+x^2) := by
  have a : 0 < x.num.natAbs :=
    Int.natAbs_pos.mpr (fun eq => nz (Rat.num_eq_zero.mp eq))
  have b := x.den_pos
  have a2 := Nat.pow_pos a (n:=2)
  have b2 := Nat.pow_pos b (n:=2)
  have bound : (1+x^2).num.natAbs ≤ H (1+x^2) := Nat.le_max_left ..
  rw [one_add_square_num, Int.natAbs_natCast] at bound
  change (max x.num.natAbs x.den)^2+1 ≤ H (1+x^2)
  rcases Nat.le_total x.num.natAbs x.den with h|h
  · rw [Nat.max_eq_right h]; omega
  · rw [Nat.max_eq_left h]; omega

/-- For nonzero second coefficient the cubic upper bound loses exactly U²
on the extremal family below. -/
theorem refined_scale_heights {l a b : Rat} {U : Nat} (live : l ≠ 0)
    (nonzero : b ≠ 0) (base : H l ≤ U) (first : H (a^2*l) ≤ U)
    (second : H ((1+b^2)^2*l) ≤ U) :
    (H a*H b)^2 ≤ U^2*(U-1) := by
  have ha := (scale_heights live base first second).1
  have z : (1+(0:Rat)^2)^2=1 := by grobner
  have hb := (scale_heights (b:=0) live base second
    (by simpa only [z,Rat.one_mul] using base)).1
  have gap := strict_square_height nonzero
  rw [Nat.mul_pow]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left ha 2) (by omega)

private theorem natural_height (n : Nat) (pos : 0 < n) : H (n : Rat) = n := by
  simp only [H, multiplicativeHeight, Rat.num_natCast, Rat.den_natCast, Int.natAbs_natCast]
  exact Nat.max_eq_left pos

/-- All three slope heights attain U, and their two coefficient heights
attain the refined bound for every U = 1+n² with n positive. -/
theorem sharp_scale_family (n : Nat) (pos : 0 < n) :
    let U : Nat := 1+n^2
    let a : Rat := U
    let b : Rat := n
    let l := a⁻¹
    H l = U ∧ H (a^2*l) = U ∧ H ((1+b^2)^2*l) = U ∧
      (H a*H b)^2 = U^2*(U-1) := by
  dsimp only
  let U : Nat := 1+n^2
  have up : 0 < U := by dsimp [U]; omega
  have live : (U : Rat) ≠ 0 := by
    exact fun h => (Nat.ne_of_gt up) (Rat.natCast_eq_zero_iff.mp h)
  have divide : (U : Rat)^2*(U : Rat)⁻¹=(U : Rat) := by
    rw [Rat.pow_succ, Rat.pow_one, Rat.mul_assoc, Rat.mul_inv_cancel _ live, Rat.mul_one]
  have cast : (1:Rat)+(n:Rat)^2=(U:Rat) := by simp [U]
  change H (U:Rat)⁻¹=U ∧ H ((U:Rat)^2*(U:Rat)⁻¹)=U ∧
    H (((1:Rat)+(n:Rat)^2)^2*(U:Rat)⁻¹)=U ∧ (H (U:Rat)*H (n:Rat))^2=U^2*(U-1)
  rw [cast, divide, height_inv _ live, natural_height U up, natural_height n pos, Nat.mul_pow]
  have sub : U-1=n^2 := by dsimp [U]; omega
  simp [sub]

#print axioms strict_square_height
#print axioms refined_scale_heights
#print axioms sharp_scale_family
end HeightSpecialization

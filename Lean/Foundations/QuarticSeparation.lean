import Std

/-! Integer separation for the order-52 and order-16 divisibility tests. -/
namespace QuarticSeparation

private theorem eq_zero_of_abs_lt_divisor {z : Int} {m : Nat}
    (divides : (m : Int) ∣ z) (small : z.natAbs < m) : z = 0 := by
  by_cases hn : z = 0
  · exact hn
  · have hz : 0 < z.natAbs := Int.natAbs_pos.mpr hn
    have le := Nat.le_of_dvd hz (Int.ofNat_dvd_left.mp divides)
    omega

/-- The Lucas residual vanishes under the stated separation and magnitude bounds. -/
theorem lucas_residual_eq_zero {B R : Nat} {Δ : Int}
    (separation : 2*B < R^13) (magnitude : Δ.natAbs < 5*B^4)
    (divides : ((R^52 : Nat) : Int) ∣ Δ) : Δ = 0 := by
  apply eq_zero_of_abs_lt_divisor divides
  calc Δ.natAbs < 5*B^4 := magnitude
       _ ≤ (2*B)^4 := by rw [Nat.mul_pow]; omega
       _ < (R^13)^4 := Nat.pow_lt_pow_left separation (by decide)
       _ = R^52 := (Nat.pow_mul R 13 4).symm

/-- The numerator of beta minus its putative label vanishes. -/
theorem label_numerator_eq_zero {B R D : Nat} {n : Int}
    (separation : 2*B < R^13) (denHeight : D < R^3)
    (magnitude : n.natAbs ≤ 2*B*D)
    (divides : ((R^16 : Nat) : Int) ∣ n) : n = 0 := by
  apply eq_zero_of_abs_lt_divisor divides
  calc n.natAbs ≤ 2*B*D := magnitude
       _ ≤ R^13*D := Nat.mul_le_mul_right D (Nat.le_of_lt separation)
       _ < R^13*R^3 := Nat.mul_lt_mul_of_pos_left denHeight (by omega)
       _ = R^16 := (Nat.pow_add R 13 3).symm

/-- A cleared square of a reduced signed fraction has no nontrivial denominator. -/
theorem reduced_square_den_eq_one {a k : Int} {b : Nat} (reduced : Nat.Coprime a.natAbs b)
    (cleared : a^2 = k*(b : Int)^2) : b = 1 := by
  have h := congrArg Int.natAbs cleared
  have magnitude : a.natAbs^2 = k.natAbs*b^2 := by
    simpa only [Int.natAbs_pow, Int.natAbs_mul, Int.natAbs_natCast] using h
  apply (reduced.symm.pow_right 2).eq_one_of_dvd
  exact ⟨k.natAbs*b, by rw [magnitude]; grobner⟩

/-- The same endpoint directly on Lean's canonical rational representation. -/
theorem integer_of_integral_square {x : Rat} {k : Int} (square : x^2 = (k : Rat)) :
    ∃ z : Int, x = (z : Rat) := by
  have hd : x.den^2 = 1 := by
    simpa only [Rat.den_pow, Rat.den_intCast] using congrArg Rat.den square
  have d : x.den ∣ 1 := ⟨x.den, by rw [← hd, Nat.pow_two]⟩
  exact ⟨x.num, Rat.ext rfl (Nat.eq_one_of_dvd_one d)⟩

/-- The ordinary input is integral once the source identifies x² + 2 with an integer. -/
theorem integer_of_label {x : Rat} {n : Int} (label : x^2+2 = (n : Rat)) :
    ∃ z : Int, x = (z : Rat) := by
  apply integer_of_integral_square (k := n-2)
  rw [Rat.intCast_sub]
  grobner

end QuarticSeparation

#print axioms QuarticSeparation.lucas_residual_eq_zero
#print axioms QuarticSeparation.label_numerator_eq_zero
#print axioms QuarticSeparation.reduced_square_den_eq_one
#print axioms QuarticSeparation.integer_of_label

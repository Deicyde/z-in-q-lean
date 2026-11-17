import ZInQKernel.Hypotheses.JHeight
import ZInQKernel.Multiplication.Soundness.RationalHeights

/-!
# Height of the parameter from the genus-two invariant

Writing `j = a/b` and `igusaRatio j = P/Q` in lowest terms gives
`Q (a + 4b)^5 = 200000 P a³ b²` whenever `j ≠ 0`. The two endpoint
coefficients of this equation give a height bound using only `Q`.
-/

namespace ZInQ.QualitativeHeight

/-- The rational expression for the invariant in the Hauptmodul coordinate. -/
noncomputable def igusaRatio (j : ℚ) : ℚ := (j + 4)^5 / (200000 * j^3)

private theorem ratio_fraction {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    igusaRatio (a / b) = (a + 4*b)^5 / (200000 * a^3 * b^2) := by
  unfold igusaRatio
  field_simp [ha, hb]

private theorem rational_root_divisibilities {a b P Q : ℤ} (cop : IsCoprime a b)
    (cross : Q * (a + 4*b)^5 = 200000 * P * a^3 * b^2) :
    b ∣ Q ∧ a ∣ 1024 * Q := by
  constructor
  · have hshift : IsCoprime b (a + 4*b) := by
      obtain ⟨x, y, hxy⟩ := cop
      exact ⟨y - 4*x, x, by linear_combination hxy⟩
    have hc : IsCoprime b ((a + 4*b)^5) := by
      simpa only [pow_one] using hshift.pow (m := 1) (n := 5)
    apply hc.dvd_of_dvd_mul_right
    rw [cross]
    exact ⟨200000 * P * a^3 * b, by ring⟩
  · have hmod : a + 4*b ≡ 4*b [ZMOD a] := Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
    have hdiff := Int.modEq_iff_dvd.mp ((hmod.pow 5).mul_left Q)
    have hterm : a ∣ Q * (a + 4*b)^5 := by
      rw [cross]
      exact ⟨200000 * P * a^2 * b^2, by ring⟩
    have hprod := dvd_add hdiff hterm
    rw [sub_add_cancel, show Q * (4*b)^5 = (1024*Q) * b^5 by ring] at hprod
    have hc : IsCoprime a (b^5) := by
      simpa only [pow_one] using cop.pow (m := 1) (n := 5)
    exact hc.dvd_of_dvd_mul_right hprod

/-- The reduced denominator of `j` divides `Q`, and its signed numerator
divides `1024 Q`, where `Q` is the reduced denominator of the invariant. -/
theorem ratio_divisibilities {j : ℚ} (hj : j ≠ 0) :
    j.den ∣ (igusaRatio j).den ∧ j.num ∣ 1024 * ((igusaRatio j).den : ℤ) := by
  let a := j.num
  let b : ℤ := j.den
  let R := igusaRatio j
  let P := R.num
  let Q : ℤ := R.den
  have ha : (a : ℚ) ≠ 0 := by exact_mod_cast Rat.num_ne_zero.mpr hj
  have hb : (b : ℚ) ≠ 0 := by dsimp [b]; exact_mod_cast j.den_nz
  have hQ : (Q : ℚ) ≠ 0 := by dsimp [Q]; exact_mod_cast R.den_nz
  have hjfrac : (a : ℚ) / (b : ℚ) = j := by
    simpa only [a, b, Int.cast_natCast] using Rat.num_div_den j
  have hrfrac : (P : ℚ) / (Q : ℚ) = R := by
    simpa only [P, Q, Int.cast_natCast] using Rat.num_div_den R
  have eqfrac : (P : ℚ) / (Q : ℚ) =
      ((a : ℚ) + 4*(b : ℚ))^5 / (200000 * (a : ℚ)^3 * (b : ℚ)^2) :=
    hrfrac.trans ((congrArg igusaRatio hjfrac.symm).trans (ratio_fraction ha hb))
  have eqprod := (div_eq_div_iff hQ
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 ha)) (pow_ne_zero 2 hb))).mp eqfrac
  have cross : Q * (a + 4*b)^5 = 200000 * P * a^3 * b^2 := by
    have he : (Q : ℚ) * ((a : ℚ) + 4*(b : ℚ))^5 =
        200000 * (P : ℚ) * (a : ℚ)^3 * (b : ℚ)^2 := by linear_combination -eqprod
    exact_mod_cast he
  have cop : IsCoprime a b := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact j.reduced
  obtain ⟨den, num⟩ := rational_root_divisibilities cop cross
  exact ⟨Int.natCast_dvd_natCast.mp den, num⟩

/-- The denominator divisibility also holds at the totalized value `j = 0`. -/
theorem ratio_den_dvd (j : ℚ) : j.den ∣ (igusaRatio j).den := by
  by_cases hj : j = 0
  · subst j
    simp
  · exact (ratio_divisibilities hj).1

/-- Height of the Hauptmodul in terms of the invariant, including `j = 0`
and the zero of the numerator at `j = -4`. -/
theorem height_le_ratio (j : ℚ) :
    ratHeight j ≤ ratHeight (igusaRatio j) + Real.log 1024 := by
  by_cases hj : j = 0
  · subst j
    have hz : ratHeight 0 = 0 := by norm_num [ratHeight]
    rw [hz]
    exact add_nonneg (Mult.ratHeight_nonneg _) (Real.log_nonneg (by norm_num))
  let R := igusaRatio j
  obtain ⟨hd, hn⟩ := ratio_divisibilities hj
  have hdn : j.den ≤ R.den := Nat.le_of_dvd R.den_pos hd
  have habs : j.num.natAbs ∣ 1024 * R.den := by
    simpa [R, Int.natAbs_mul] using Int.natAbs_dvd_natAbs.mpr hn
  have hnum := Nat.le_of_dvd (Nat.mul_pos (by decide : 0 < 1024) R.den_pos) habs
  have hnr : (j.num.natAbs : ℝ) ≤ 1024 * (R.den : ℝ) := by exact_mod_cast hnum
  rw [Nat.cast_natAbs, Int.cast_abs] at hnr
  have hdr : (j.den : ℝ) ≤ (R.den : ℝ) := by exact_mod_cast hdn
  have hR : (0 : ℝ) < R.den := by exact_mod_cast R.den_pos
  have hpos : 0 < max |(j.num : ℝ)| (j.den : ℝ) :=
    (show (0 : ℝ) < j.den by exact_mod_cast j.den_pos).trans_le (le_max_right _ _)
  calc
    ratHeight j ≤ Real.log (1024 * (R.den : ℝ)) :=
      Real.log_le_log hpos (max_le hnr (by linarith))
    _ = Real.log (R.den : ℝ) + Real.log 1024 := by
      rw [Real.log_mul (by norm_num) hR.ne', add_comm]
    _ ≤ ratHeight R + Real.log 1024 :=
      add_le_add (Real.log_le_log hR (le_max_right _ _)) le_rfl

/-- The invariant bounds the height of every noncontact rational parameter. -/
theorem parameter_height_le_ratio (t : ℚ) (ht : t ∉ contactSet) :
    12 * ratHeight t ≤ ratHeight (igusaRatio (JHeight.Jmap t)) + 450 + Real.log 1024 := by
  linarith [JHeight.twelve_mul_ratHeight_le t ht, height_le_ratio (JHeight.Jmap t)]

end ZInQ.QualitativeHeight

#print axioms ZInQ.QualitativeHeight.ratio_divisibilities
#print axioms ZInQ.QualitativeHeight.ratio_den_dvd
#print axioms ZInQ.QualitativeHeight.height_le_ratio
#print axioms ZInQ.QualitativeHeight.parameter_height_le_ratio

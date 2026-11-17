import SixShimuraEndpoint

/-! Rational slopes on the real-multiplication quotient and the rational
CM list of Errthum, Table 2. The row of discriminant −24 occurs at zero. -/
namespace ZInQBlueprint.QuaternionLift

def slopeTest (a : CMRow) : Prop :=
  a.2.1 ≠ 0 ∧ IsSquare (27 * ((a.2.2 : ℚ) - a.2.1) / a.2.1)

instance (a : CMRow) : Decidable (slopeTest a) := by
  unfold slopeTest
  infer_instance

/-- The complete calculation for the rational affine chart. -/
theorem rational_slope_table :
    rationalCMRows.filter (fun a => decide (slopeTest a)) = [(-24, 1, 1)] := by
  decide +kernel

private theorem denominator_of_zero_numerator {a : CMRow} (ha : a ∈ rationalCMRows)
    (hm : a.2.1 = 0) : a.2.2 = 1 := by
  have h : rationalCMRows.filter (fun b => decide (b.2.1 = 0)) = [(-4,0,1)] := by decide +kernel
  have mem : a ∈ rationalCMRows.filter (fun b => decide (b.2.1 = 0)) :=
    List.mem_filter.mpr ⟨ha, by simp [hm]⟩
  rw [h, List.mem_singleton] at mem
  subst a
  rfl

/-- On the rational-slope chart the full rational CM table cuts out the
single slope t=0. This holds independently of the six-contact family. -/
theorem outsideCM_iff_slope_ne_zero {j t : ℚ} (chart : j*(t^2+27) = -16) :
    OutsideCM j ↔ t ≠ 0 := by
  have hden : 0 < t^2+27 := by positivity
  let x := -27*j/16
  have prod : x*(t^2+27) = 27 := by
    dsimp [x]
    linear_combination -27*chart/16
  have xpos : 0 < x := by
    rw [(eq_div_iff hden.ne').mpr prod]
    positivity
  constructor
  · intro off zero
    have row : ((-24,1,1) : CMRow) ∈ rationalCMRows := by decide +kernel
    have reject := off _ row
    subst t
    have hj : j = -16/27 := by norm_num at chart; linarith
    norm_num [hj] at reject
  · intro hnonzero a ha he
    change |x*(a.2.2 : ℚ)| = (a.2.1 : ℚ) at he
    rw [abs_of_nonneg (mul_nonneg xpos.le (by positivity))] at he
    by_cases hm : a.2.1 = 0
    · have hn := denominator_of_zero_numerator ha hm
      rw [hn, hm] at he
      exact xpos.ne' (by simpa using he)
    · have hm' : (a.2.1 : ℚ) ≠ 0 := by exact_mod_cast hm
      have rel : (a.2.1 : ℚ)*(t^2+27) = 27*(a.2.2 : ℚ) := by
        linear_combination (a.2.2 : ℚ)*prod - (t^2+27)*he
      have hit : slopeTest a := ⟨hm, t, (div_eq_iff hm').mpr (by linear_combination -rel)⟩
      have mem : a ∈ rationalCMRows.filter (fun b => decide (slopeTest b)) :=
        List.mem_filter.mpr ⟨ha, by simp [hit]⟩
      rw [rational_slope_table, List.mem_singleton] at mem
      subst a
      norm_num at rel
      exact hnonzero rel

/-- The three factors controlling the Mestre equation vanish on the same
single rational slope. -/
theorem mestre_open_iff_slope_ne_zero {j t : ℚ} (chart : j*(t^2+27) = -16) :
    j*(64*j-81)*(27*j+16) ≠ 0 ↔ t ≠ 0 := by
  have hden : 0 < t^2+27 := by positivity
  have hj : j < 0 := by
    rw [(eq_div_iff hden.ne').mpr chart]
    exact div_neg_of_neg_of_pos (by norm_num) hden
  have last : 27*j+16 = -(j*t^2) := by linear_combination chart
  constructor
  · intro determinant ht
    apply determinant
    rw [last, ht]
    ring
  · intro ht
    rw [last]
    exact mul_ne_zero (mul_ne_zero hj.ne (by linarith)) (neg_ne_zero.mpr (mul_ne_zero hj.ne (pow_ne_zero _ ht)))

end ZInQBlueprint.QuaternionLift

#print axioms ZInQBlueprint.QuaternionLift.rational_slope_table
#print axioms ZInQBlueprint.QuaternionLift.outsideCM_iff_slope_ne_zero
#print axioms ZInQBlueprint.QuaternionLift.mestre_open_iff_slope_ne_zero

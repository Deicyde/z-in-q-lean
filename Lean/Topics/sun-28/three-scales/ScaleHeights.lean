import MarkedHeights
import ZInQKernel.Multiplication.Soundness.FieldHeights

/-! Heights of the two rational coefficients of Sun's three scales. -/
namespace Sun28.Ordinary
open Height ZInQ ZInQ.Mult

/-- Squaring and adding one to a rational introduces no cancellation at finite primes. -/
theorem twice_height_le_one_add_square (r : ℚ) :
    2 * logHeight₁ r ≤ logHeight₁ (1+r^2) := by
  have trans := translated_numerator (r^2) (-1)
  have en : (1+r^2).num = r.num^2 + (r.den:ℤ)^2 := by
    simpa only [Int.cast_neg,Int.cast_one,sub_neg_eq_add,neg_one_mul,
      Rat.num_pow,Rat.den_pow,Nat.cast_pow,add_comm] using trans
  have sq : (r.num.natAbs^2:ℤ)=r.num^2 := by rw [Int.natCast_natAbs,sq_abs]
  have em : (1+r^2).num.natAbs = r.num.natAbs^2+r.den^2 := by
    apply Int.ofNat_inj.mp
    rw [Int.natCast_natAbs, en,abs_of_nonneg (by positivity),Nat.cast_add,Nat.cast_pow,Nat.cast_pow,sq]
  have bound : (max r.num.natAbs r.den)^2 ≤ max (1+r^2).num.natAbs (1+r^2).den := by
    refine le_trans ?_ (le_max_left _ _)
    rw [em]
    rcases le_total r.num.natAbs r.den with h|h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega
  have hR : ((max r.num.natAbs r.den:ℕ):ℝ)^2 ≤ (max (1+r^2).num.natAbs (1+r^2).den:ℕ) := by exact_mod_cast bound
  have pos : 0 < (max r.num.natAbs r.den:ℕ) := lt_of_lt_of_le r.den_pos (le_max_right _ _)
  have logs := Real.log_le_log (by positivity : 0<((max r.num.natAbs r.den:ℕ):ℝ)^2) hR
  simpa only [Rat.logHeight₁_eq_log_max,Real.log_pow,Nat.cast_ofNat] using logs

theorem coefficient_heights (a b η : ℚ) (nonzero : η≠0) {H : ℝ}
    (tests : ∀ j, logHeight₁ ((scaleRoot a b j)^2*η) ≤ H) :
    logHeight₁ a ≤ H ∧ 2*logHeight₁ b ≤ H := by
  have base : logHeight₁ η ≤ H := by simpa [scaleRoot] using tests 0
  have bound (c : ℚ) (h : logHeight₁ (c^2*η) ≤ H) : logHeight₁ c ≤ H := by
    have u := logHeight₁_mul_le (c^2*η) η⁻¹
    rw [mul_inv_cancel_right₀ nonzero,logHeight₁_pow,logHeight₁_inv] at u
    norm_num only [Nat.cast_ofNat] at u
    linarith
  exact ⟨bound a (by simpa [scaleRoot] using tests 1),
    (twice_height_le_one_add_square b).trans (bound (1+b^2) (by simpa [scaleRoot] using tests 2))⟩

theorem three_scale_product_height (C : K0) (η : ℚ) (nonzero : η≠0) {H : ℝ}
    (tests : ∀ j, logHeight₁ ((scaleRoot C.re C.im j)^2*η) ≤ H) :
    hK0 C ≤ 3/2*H + 3/2*Real.log 2 := by
  obtain ⟨a,b⟩ := coefficient_heights C.re C.im η nonzero tests
  have c := hK0_ratCast_add_mul_sqrt2_le C.re C.im
  rw [←K0.eq_re_add_im_mul_sqrt2,ratHeight_eq_logHeight₁,ratHeight_eq_logHeight₁] at c
  linarith

end Sun28.Ordinary
#print axioms Sun28.Ordinary.twice_height_le_one_add_square
#print axioms Sun28.Ordinary.coefficient_heights
#print axioms Sun28.Ordinary.three_scale_product_height

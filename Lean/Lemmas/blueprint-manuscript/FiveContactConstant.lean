import PrimorialCertificate

/-! The numerical part of the cubic five-contact estimate of V15. -/
namespace ManuscriptV15.Arithmetic

/-- The pointwise geometric estimate on the original five marks. -/
def FiveContactParameters : Prop :=
  ∀ a : ℚ, ¬ marked a → ratHeight a ≤ C3 * (M5 a : ℝ)^3 * (1 + Real.log (M5 a))

/-- The cutoff 76,176 and the specified coefficient give this explicit bound. -/
theorem fiveContact_constant_bound : C3 ≤ (2:ℝ)^330683 := by
  let b : ℝ := badProduct
  have hn : 0 < badProduct :=
    Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos
  have hbpos : (0:ℝ) < (badProduct:ℝ) := Nat.cast_pos.mpr hn
  have hb_one : (1:ℝ) ≤ (badProduct:ℝ) := by exact_mod_cast (show 1 ≤ badProduct from hn)
  have hb : b ≤ (2:ℝ)^109445 := by
    calc (badProduct:ℝ) ≤ ((2^109445 : ℕ) : ℝ) := Nat.cast_le.mpr badProduct_bit_bound.le
         _ = (2:ℝ)^109445 := by rw [Nat.cast_pow]; norm_num only [Nat.cast_ofNat]
  have hlog : Real.log b ≤ (2:ℝ)^17 := by
    calc Real.log b ≤ Real.log ((2:ℝ)^109445) := Real.log_le_log hbpos hb
         _ = 109445 * Real.log 2 := by rw [Real.log_pow]; norm_num
         _ ≤ 109445 * (1:ℝ) := by
           apply mul_le_mul_of_nonneg_left _ (by norm_num)
           linarith [Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))]
         _ ≤ (2:ℝ)^17 := by norm_num
  have hD : (19:ℝ)*(4608*210^300) ≤ 2^2331 := by
    exact_mod_cast (by decide +kernel : (19:ℕ)*(4608*210^300) ≤ 2^2331)
  have hprod := mul_le_mul hD (pow_le_pow_left₀ hbpos.le hb 3)
    (pow_nonneg hbpos.le 3) (by positivity)
  calc C3 ≤ ((2:ℝ)^2331*((2:ℝ)^109445)^3)*((2:ℝ)^17) :=
         mul_le_mul hprod hlog (Real.log_nonneg hb_one) (by positivity)
       _ = (2:ℝ)^330683 := by rw [← pow_mul, ← pow_add, ← pow_add]

theorem fiveContact_iff_parameters : FiveContact ↔ FiveContactParameters := by
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  exact fiveContact_constant_bound.trans_lt
    (pow_lt_pow_right₀ (by norm_num : (1:ℝ)<2) (by decide : 330683 < 330770))

/-- Both predecessor estimates follow directly from the single pointwise estimate. -/
theorem predecessorHeights_of_parameters (h : FiveContactParameters) : QuarticHeight19 ∧ O8Height :=
  predecessorHeights (fiveContact_iff_parameters.mpr h)

end ManuscriptV15.Arithmetic

#print axioms ManuscriptV15.Arithmetic.fiveContact_constant_bound
#print axioms ManuscriptV15.Arithmetic.fiveContact_iff_parameters
#print axioms ManuscriptV15.Arithmetic.predecessorHeights_of_parameters

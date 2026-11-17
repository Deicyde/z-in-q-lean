import FixedData

namespace Sun28.FixedPreparation
open ZInQ Sun28.Forward Sun28.Ordinary Sun28.ScalarHeight Sun28.WitnessIndices
noncomputable section

def ordinary : ℝ := 11+(3/2)*(glazerConstant24+Real.log 3)
def logConstant : ℝ := Real.log (32*ordinary^2)
def fixedMultiplier : ℕ := Sun28.multiplier ordinary logConstant glazerConstant24

private theorem empty_extra : extraPrimes oldCutoff oldCutoff=∅ := by simp [extraPrimes]

theorem fixed_coefficients :
    scalarCoefficient oldCutoff=glazerConstant24 ∧ ordinaryCoefficient oldCutoff=ordinary := by
  have c : 1 ≤ glazerConstant24 := by
    unfold glazerConstant24
    have h : (0:ℝ) ≤ 2*(4608^165888+6^100)*(∏ p ∈ oldCutoff,(p:ℝ))^24 := by positivity
    exact (by norm_num : (1:ℝ)≤0+128).trans (add_le_add h (le_refl (128:ℝ)))
  have w : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  refine ⟨by simp [scalarCoefficient,empty_extra],?_⟩
  simp only [ordinaryCoefficient,fiveHeightConstant,empty_extra,Finset.prod_empty,one_pow,
    mul_one,max_eq_right (by linarith : 1≤glazerConstant24+Real.log 3),ordinaryConstant,ordinary]
  ring

theorem multiplier_at_cutoff : forwardMultiplier oldCutoff=fixedMultiplier := by
  rw [forwardMultiplier,fixed_coefficients.1,fixed_coefficients.2]
  rfl

theorem fixed_multiplier_spec : 6∣fixedMultiplier ∧ 8≤fixedMultiplier ∧
    (∀ B : ℝ, (fixedMultiplier:ℝ)-1≤B → ¬ B^2 ≤ ordinary*(1+(10*B^4)^(3/8:ℝ))) ∧
    (∀ c : ℝ, (fixedMultiplier:ℝ)≤c → logConstant+3*glazerConstant24*Real.sqrt c<c-4) := by
  have sp : 0≤glazerConstant24 := by unfold glazerConstant24; positivity
  have op : 0≤ordinary := by unfold ordinary; have : 0≤Real.log 3 := Real.log_nonneg (by norm_num); linarith
  exact Sun28.multiplier_spec op sp

/-- Forward soundness for fixed integer preparation data and one fixed multiplier. -/
theorem fixed_witness_sound (A : Fin 9 → AffineInput) (x η : ℚ)
    (chart : OrdinaryCharts oldCutoff K0) (five : OriginalFiveHeight glazerConstant24 oldCutoff)
    (accepted : PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers) :
    ∃ k : ℤ, x=(k:ℚ) ∧ (nineAffine A).doubles.N=(2*k^2+3) • P := by
  apply rational_witness_sound A anchor x η (gamma:ℚ) denominator smallMultipliers smallMultipliers
    anchor_nonzero (by exact_mod_cast gamma_positive.ne')
  · rwa [fixed_cutoff]
  · exact five
  · rwa [fixed_cutoff,multiplier_at_cutoff]

end
end Sun28.FixedPreparation
#print axioms Sun28.FixedPreparation.fixed_coefficients
#print axioms Sun28.FixedPreparation.multiplier_at_cutoff
#print axioms Sun28.FixedPreparation.fixed_multiplier_spec
#print axioms Sun28.FixedPreparation.fixed_witness_sound

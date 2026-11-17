import HeightEquivalence
import ZInQKernel.Multiplication.Certificate.ConstantsProperties

/-! Sufficient and necessary rational point bounds with the exact public
six-contact constants. The sufficient coefficient is strictly positive. -/
open ZInQ ZInQ.Mult
namespace ZInQBlueprint.OddSupport
noncomputable section

/-- The largest H permitted by the explicit forward comparison. -/
def publicTwistConstant : ℝ := (heightH6 (heightD:ℝ) - Real.log 1800) /
    ((∏ p ∈ S_mul, p : ℕ) : ℝ)^24

private theorem positivePrimeProduct : (0:ℝ)<((∏ p ∈ S_mul,p : ℕ):ℝ) := by
  exact_mod_cast Finset.prod_pos (fun p hp => (prime_of_mem_S_mul hp).pos)

theorem publicTwistConstant_pos : 0 < publicTwistConstant := by
  have base := le_max_left (1:ℝ) (max (heightCcm:ℝ) (heightQ (heightD:ℝ)^17))
  have bound : (2*10^13:ℝ) ≤ heightH6 (heightD:ℝ) := by
    unfold heightH6
    linear_combination (2*10^13:ℝ)*base
  have small := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1800)
  exact div_pos (by linarith) (pow_pos positivePrimeProduct _)

theorem sixContactMin_of_twistBound (estimate : TwistBound publicTwistConstant) :
    SixContactMin := by
  have h := contact_of_twists S_mul (fun _ hp => prime_of_mem_S_mul hp)
    publicTwistConstant_pos.le estimate
  have row : publicTwistConstant*(((∏ p ∈ S_mul,p : ℕ):ℝ)^24)+Real.log 1800 =
      heightH6 (heightD:ℝ) := by
    unfold publicTwistConstant
    rw [div_mul_cancel₀ _ (pow_ne_zero _ positivePrimeProduct.ne')]
    ring
  rw [row] at h
  exact h

theorem twistBound_of_sixContactMin (estimate : SixContactMin) :
    TwistBound (heightH6 (heightD:ℝ) + Real.log 1800) := by
  apply twists_of_contact S_mul (fun p hp hS => lt_trans (by norm_num) (not_mem_S_mul hp hS).1)
    (heightH6_nonneg _) estimate

#print axioms publicTwistConstant_pos
#print axioms sixContactMin_of_twistBound
#print axioms twistBound_of_sixContactMin
end
end ZInQBlueprint.OddSupport

import GenusTwoThetaSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Symmetry of the literal genus-two theta series at odd characteristics. -/
namespace ZInQBlueprint.ThetaPeriod
open ThetaQuotient
noncomputable section

private def bit (j : Fin 16) (k : ℕ) : ℤ := (j.val / 2^k % 2 : ℕ)

private theorem halfBit_eq (j : Fin 16) (k : ℕ) : halfBit j k = (bit j k : ℂ)/2 := by
  unfold halfBit bit
  rw [Int.cast_natCast]

private def flip (j : Fin 16) : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun n := (-n.1 - bit j 2, -n.2 - bit j 3)
  invFun n := (-n.1 - bit j 2, -n.2 - bit j 3)
  left_inv := by intro n; ext <;> dsimp <;> ring
  right_inv := by intro n; ext <;> dsimp <;> ring

private theorem odd_dot :
    ∀ j : Fin 16, (¬ ∃ k, evenIndices k = j) →
      bit j 2 * bit j 0 + bit j 3 * bit j 1 = 1 := by decide

private theorem term_flip (Z : SiegelPeriod) (j : Fin 16) (hj : ¬ ∃ k, evenIndices k = j)
    (n : ℤ × ℤ) : term Z j (flip j n) = -term Z j n := by
  have hd : (bit j 2 : ℂ)*bit j 0 + (bit j 3 : ℂ)*bit j 1 = 1 := by
    exact_mod_cast odd_dot j hj
  unfold term
  simp only [halfBit_eq]
  rw [← neg_one_mul (Complex.exp _),← Complex.exp_pi_mul_I,← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-(n.1*bit j 0 + n.2*bit j 1)-1,?_⟩
  simp only [flip,Equiv.coe_fn_mk]
  push_cast
  linear_combination -(Real.pi:ℂ)*Complex.I*hd

theorem thetaNull_odd (Z : SiegelPeriod) (j : Fin 16) (hj : ¬ ∃ k, evenIndices k = j) :
    thetaNull Z j = 0 := by
  have h := (flip j).tsum_eq (term Z j)
  simp only [term_flip Z j hj,tsum_neg] at h
  unfold thetaNull
  linear_combination -(1/2:ℂ)*h

end
end ZInQBlueprint.ThetaPeriod
#print axioms ZInQBlueprint.ThetaPeriod.thetaNull_odd

import CellAverage

namespace Sun28.ArtinCube
open Finset
open scoped Classical
noncomputable section
variable {ι α Ω : Type*} [DecidableEq α]

/-- Removing cells of total volume at most τ incurs an additive error μτ. -/
theorem truncated_error (C : Finset ι) (vol fac : ι → ℝ) (μ ε η τ observed : ℝ)
    (cap : ∑ c ∈ C, vol c ≤ 1) (lost : 1 - ∑ c ∈ C, vol c ≤ τ)
    (positive : ∀ c ∈ C, 0 ≤ vol c) (mu : 0 ≤ μ) (en : 0 ≤ ε)
    (good : ∀ c ∈ C, |fac c - 1| ≤ ε)
    (linear : |observed - ∑ c ∈ C, vol c * μ * fac c| ≤ η) :
    |observed - μ| ≤ η + μ * (ε + τ) := by
  let mass := ∑ c ∈ C, vol c
  have center : (∑ c ∈ C, vol c * μ * fac c) - mass * μ =
      ∑ c ∈ C, vol c * μ * (fac c - 1) := by
    simp only [mul_sub, mul_one, sum_sub_distrib, mass, sum_mul]
  have err : |(∑ c ∈ C, vol c * μ * fac c) - mass * μ| ≤ μ * ε := calc
    _ = |∑ c ∈ C, vol c * μ * (fac c - 1)| := by rw [center]
    _ ≤ ∑ c ∈ C, |vol c * μ * (fac c - 1)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ c ∈ C, vol c * (μ * ε) := by
      apply sum_le_sum
      intro c hc
      rw [abs_mul, abs_of_nonneg (mul_nonneg (positive c hc) mu), ←mul_assoc]
      exact mul_le_mul_of_nonneg_left (good c hc) (mul_nonneg (positive c hc) mu)
    _ = mass * (μ * ε) := (sum_mul ..).symm
    _ ≤ μ * ε := by simpa using mul_le_mul_of_nonneg_right cap (mul_nonneg mu en)
  have gap : |mass * μ - μ| ≤ μ * τ := by
    rw [show mass * μ - μ = -((1 - mass) * μ) by ring, abs_neg,
      abs_of_nonneg (mul_nonneg (sub_nonneg.mpr cap) mu), mul_comm μ τ]
    exact mul_le_mul_of_nonneg_right lost mu
  calc
    _ ≤ |observed - ∑ c ∈ C, vol c * μ * fac c| +
          |(∑ c ∈ C, vol c * μ * fac c) - μ| := abs_sub_le ..
    _ ≤ η + (μ * ε + μ * τ) := add_le_add linear ((abs_sub_le _ (mass * μ) _).trans (add_le_add err gap))
    _ = _ := by ring

/-- Centring a wrapped cube after deleting boundary strips in every raw moment. -/
theorem centered_of_truncated_cells (X : Finset Ω) (weight : Ω → ℝ) (f : α → Ω → ℝ)
    (V : Finset α) (hv : V.Nonempty) (μ ε η τ : ℝ) (mu : 0 ≤ μ) (cap : μ ≤ 1)
    (en : 0 ≤ ε) (tn : 0 ≤ τ)
    (cells : ∀ I ∈ V.powerset, ∃ (C : Finset ι) (vol fac : ι → ℝ),
      (∑ c ∈ C, vol c) ≤ 1 ∧ 1 - ∑ c ∈ C, vol c ≤ τ ∧ (∀ c ∈ C, 0 ≤ vol c) ∧
      (∀ c ∈ C, |fac c - 1| ≤ ε) ∧
      |moment X weight f I - ∑ c ∈ C, vol c * μ ^ I.card * fac c| ≤ η) :
    |moment X weight (fun i x => f i x - μ) V| ≤ (1 + μ)^V.card * (η + (ε + τ)) := by
  have H : ∀ I ∈ V.powerset, |moment X weight f I - μ^I.card| ≤ η + (ε + τ) := by
    intro I hi
    obtain ⟨C, v, g, upper, lower, pos, localErr, approx⟩ := cells I hi
    have est := truncated_error C v g (μ^I.card) ε η τ _ upper lower pos
      (pow_nonneg mu _) en localErr approx
    have up : μ^I.card ≤ 1 := pow_le_one₀ mu cap
    exact est.trans (add_le_add_right (by simpa using mul_le_mul_of_nonneg_right up (add_nonneg en tn)) _)
  simpa only [abs_of_nonneg mu] using centered_bound X weight f V hv μ (η + (ε + τ)) H

end
end Sun28.ArtinCube
#print axioms Sun28.ArtinCube.truncated_error
#print axioms Sun28.ArtinCube.centered_of_truncated_cells

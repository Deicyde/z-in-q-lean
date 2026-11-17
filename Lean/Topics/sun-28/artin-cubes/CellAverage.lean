import CubeUniformity

namespace Sun28.ArtinCube
open Finset
open scoped Classical
noncomputable section
variable {ι α Ω : Type*} [DecidableEq α]

/-- Volumes of the wrap cells add to one. If the arithmetic factor in
every cell is close to one, summing the errors costs no factor for the
number of cells. A separate error covers the linear counting formula. -/
theorem cell_error (C : Finset ι) (vol fac : ι → ℝ) (μ ε observed η : ℝ)
    (volume : ∑ c ∈ C,vol c = 1) (positive : ∀ c ∈ C,0 ≤ vol c)
    (mu : 0 ≤ μ) (good : ∀ c ∈ C, |fac c - 1| ≤ ε)
    (linear : |observed - ∑ c ∈ C,vol c * μ * fac c| ≤ η) :
    |observed - μ| ≤ η + μ * ε := by
  have mass : ∑ c ∈ C,vol c*μ = μ := by rw [←sum_mul,volume,one_mul]
  have center : (∑ c ∈ C,vol c*μ*fac c) - μ = ∑ c ∈ C,vol c*μ*(fac c-1) := by
    simp only [mul_sub,mul_one,sum_sub_distrib,mass]
  have residual : |(∑ c ∈ C,vol c*μ*fac c)-μ| ≤ μ*ε := calc
    _ = |∑ c ∈ C,vol c*μ*(fac c-1)| := by rw [center]
    _ ≤ ∑ c ∈ C,|vol c*μ*(fac c-1)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ c ∈ C,vol c*μ*ε := by
      apply sum_le_sum;intro c hc
      rw [abs_mul,abs_of_nonneg (mul_nonneg (positive c hc) mu)]
      exact mul_le_mul_of_nonneg_left (good c hc) (mul_nonneg (positive c hc) mu)
    _ = μ*ε := by rw [←sum_mul,mass]
  calc
    _ ≤ |observed-∑ c ∈ C,vol c*μ*fac c| + |(∑ c ∈ C,vol c*μ*fac c)-μ| := abs_sub_le ..
    _ ≤ _ := add_le_add linear residual

/-- The quantitative implication from linear prime correlations on wrap cells
to the centred cube moment. Each subset may have a different volume partition. -/
theorem centered_of_cells (X : Finset Ω) (weight : Ω → ℝ) (f : α → Ω → ℝ)
    (V : Finset α) (hv : V.Nonempty) (μ ε η : ℝ) (mu : 0≤μ) (cap : μ≤1) (en : 0≤ε)
    (cells : ∀ I ∈ V.powerset, ∃ (C : Finset ι) (vol fac : ι → ℝ),
      (∑ c ∈ C,vol c)=1 ∧ (∀ c ∈ C,0 ≤ vol c) ∧ (∀ c ∈ C, |fac c-1| ≤ ε) ∧
      |moment X weight f I - ∑ c ∈ C,vol c*μ^I.card*fac c| ≤ η) :
    |moment X weight (fun i x => f i x - μ) V| ≤ (1+μ)^V.card * (η+ε) := by
  have H : ∀ I ∈ V.powerset, |moment X weight f I - μ^I.card| ≤ η+ε := by
    intro I hi
    obtain ⟨C,v,g,total,pos,localErr,approx⟩ := cells I hi
    have est := cell_error C v g (μ^I.card) ε (moment X weight f I) η total pos
      (pow_nonneg mu _) localErr approx
    have up : μ^I.card ≤ 1 := pow_le_one₀ mu cap
    exact est.trans (add_le_add_right (by simpa using mul_le_mul_of_nonneg_right up en) _)

  simpa only [abs_of_nonneg mu] using centered_bound X weight f V hv μ (η+ε) H

end
end Sun28.ArtinCube
#print axioms Sun28.ArtinCube.cell_error
#print axioms Sun28.ArtinCube.centered_of_cells

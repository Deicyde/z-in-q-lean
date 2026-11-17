import ModularBranchHeight
import SexticIgusaPole
import HPPlaceSums
import ReducedPeriods

/-! The published genus-two discriminant formula as a sufficient input for the bounded theorem. -/
namespace ZInQBlueprint.JacobianHeight
open Polynomial ZInQ SixContactHP
noncomputable section

private theorem numeric_allowance : 30 * Real.log Real.pi + 3 * Real.log archConstant < 150 := by
  have h : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have piBound : Real.log Real.pi < 3/2 := by
    have hs : Real.pi^2 < Real.exp 3 := calc
         Real.pi^2 < (4:ℝ)^2 := pow_lt_pow_left₀ Real.pi_lt_four Real.pi_pos.le (by decide)
         _ < (2.7 : ℝ)^3 := by norm_num
         _ < (Real.exp 1)^3 := pow_lt_pow_left₀ h (by norm_num) (by decide)
         _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
    have hh := (Real.log_lt_iff_lt_exp (sq_pos_of_pos Real.pi_pos)).mpr hs
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh]
  have b : archConstant < Real.exp 35 := calc
    _ < (2 : ℝ)^47 := archConstant_lt
    _ < (2.7 : ℝ)^35 := by norm_num
    _ < (Real.exp 1)^35 := pow_lt_pow_left₀ h (by norm_num) (by decide)
    _ = Real.exp 35 := by rw [← Real.exp_nat_mul]; norm_num
  have pos : 0 < archConstant := by norm_num [archConstant]
  linarith only [piBound, (Real.log_lt_iff_lt_exp pos).mpr b]

/-- The normalized finite contribution over a pole prime, evaluated on the actual
signed paper equation. The degree sum counts all prime ideals of K above p. -/
def paperPoleTerm (K : Type) [Field K] [NumberField K] (u : ℚ) (p : ℕ) : ℝ :=
  let f := BinaryCover.paper ℚ u false
  degreeSum K p ((max (0 : ℤ) (padicValRat p (igusaJ10 f / (igusaJ2 f)^5)) : ℝ) * Real.log p)

/-- This comparison can be used after any number-field extension on which Habegger--Pazuki
applies. All sums and the coefficient in the final bound use the absolute degree of that field. -/
theorem modular_height_of_discriminant (K : Type) [Field K] [NumberField K]
    {u : ℚ} (hu : u ∉ contactSet) (hF : ℝ) (S : Finset ℕ) (term : ℕ → ℝ)
    (arch : (K →ₐ[ℚ] ℂ) → ℝ)
    (contains : (SixContact.J u).den.primeFactors ⊆ S)
    (nonnegative : ∀ p ∈ S, 0 ≤ term p)
    (poles : ∀ p ∈ (SixContact.J u).den.primeFactors, paperPoleTerm K u p ≤ term p)
    (positive : ∀ σ, 0 < arch σ) (bounds : ∀ σ, arch σ ≤ archConstant)
    (height_formula : (Module.finrank ℚ K : ℝ) * (hF + Real.log Real.pi) =
      (∑ p ∈ S, term p)/60 - (∑ σ, Real.log (arch σ))/10) :
    ratHeight (SixContact.J u) < 30*hF + 150 := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ (by decide : (0 : ℚ) ∈ contactSet))
  have hp (p : ℕ) (hp : p ∈ (SixContact.J u).den.primeFactors) := poles p hp
  simp only [paperPoleTerm, (paper_igusa_quotient hu).2] at hp
  have hf := finite_log_lower K u hu0 term contains nonnegative hp rfl
  have hi := arch_log_upper K arch positive bounds
  have hj := j_height_of_place_formula K u hf hi height_formula
  change ratHeight (SixContact.J u) ≤ _ at hj
  linarith only [hj, numeric_allowance]

/-- Data supplied by the two applications on one polarized Jacobian. Its stable height `hF`
uses von Känel's normalization. The finite terms are grouped by rational primes and the
infinite terms are the positive Petersson norms from Habegger--Pazuki's formula. -/
structure DiscriminantComparison (K : Type) [Field K] [NumberField K] (u : ℚ) where
  hF : ℝ
  support : Finset ℕ
  term : ℕ → ℝ
  period : (K →ₐ[ℚ] ℂ) → ThetaPeriod.SiegelPeriod
  contains : (SixContact.J u).den.primeFactors ⊆ support
  nonnegative : ∀ p ∈ support, 0 ≤ term p
  poles : ∀ p ∈ (SixContact.J u).den.primeFactors, paperPoleTerm K u p ≤ term p
  reduced : ∀ σ, InStrengDomain (period σ)
  evenNonzero : ∀ σ i, ThetaPeriod.thetaNull (period σ) (ThetaQuotient.evenIndices i) ≠ 0
  formula : (Module.finrank ℚ K : ℝ) * (hF + Real.log Real.pi) =
    (∑ p ∈ support, term p)/60 - (∑ σ, Real.log (peterssonFactor (period σ)))/10
  stableBound : hF ≤ HeightBudget.vonKaenelBudget u

/-- Full specialization to the original endpoint. The structure records the per-fibre
height formula and reduction bound that remain to be supplied by geometry. -/
theorem original_of_discriminant_comparison
    (streng : StrengEstimates)
    (fibres : ∀ u : ℚ, u ∉ contactSet → ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Nonempty (DiscriminantComparison K u))
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget := by
  apply original_of_modular_height _ genus rank
  intro u hu
  obtain ⟨K,_,_,⟨d⟩⟩ := fibres u hu
  have h := modular_height_of_discriminant K hu d.hF d.support d.term _ d.contains d.nonnegative
    d.poles (fun σ => petersson_positive (d.evenNonzero σ))
    (fun σ => petersson_bound streng _ (d.reduced σ)) d.formula
  linarith only [h, d.stableBound]

end
end ZInQBlueprint.JacobianHeight
#print axioms ZInQBlueprint.JacobianHeight.paperPoleTerm
#print axioms ZInQBlueprint.JacobianHeight.modular_height_of_discriminant
#print axioms ZInQBlueprint.JacobianHeight.original_of_discriminant_comparison

import SignedThetaEndpoint
import StableDiscriminantNorm

/-! A single reduced period and just the stable-discriminant orders above the
denominator of j suffice for the original bounded polynomial. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.ThetaClass
open QuaternionMarking GeometricMarking AbelianModel NormalDescent
open JacobianHeight JacobianConductor LocalJacobians ZInQ NumberField Real ThetaPeriod
open UniqueFactorizationMonoid
noncomputable section

structure PolePeriod (K : Type) [Field K] [NumberField K] (hF : GroupScheme ℚ → ℝ)
    {u : ℚ} (hu : u ∉ contactSet) where
  period : SiegelPeriod
  reduced : InStrengDomain period
  discriminant : Ideal (𝓞 K)
  nonzero : discriminant ≠ ⊥
  orders : ∀ P ∈ normalizedFactors (Ideal.span {((SixContact.J u).den : 𝓞 K)}),
    2*(normalizedFactors (Ideal.span {((SixContact.J u).den : 𝓞 K)})).count P ≤
      (normalizedFactors discriminant).count P
  formula : (Module.finrank ℚ K:ℝ)*(hF (SixJacobian.jacobian hu)+log π) =
    log (discriminant.absNorm:ℝ)/60 -
      (Module.finrank ℚ K:ℝ)*log (peterssonFactor period)/10

theorem original_of_pole_period (hF : GroupScheme ℚ → ℝ) (effective : EffectiveSurfaceHeight hF)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (embedding : ∀ (u : ℚ) (hu : u ∉ contactSet), SixAbelMap.PaperEmbedding hu)
    (coords : ∀ (u : ℚ) (hu : u ∉ contactSet), SixAbelMap.OpenCurveLifts hu)
    (theta : ∀ (u : ℚ) (hu : u ∉ contactSet), DeterminantPolarization hu)
    (bg : ∀ (u : ℚ) (hu : u ∉ contactSet), PrintedField hu)
    (periods : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Nonempty (PolePeriod K hF hu))
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget := by
  apply original_of_modular_height _ genus rank
  intro u hu
  obtain ⟨K,_,_,⟨D⟩⟩ := periods u hu
  have divides := PeriodGaussian.denominator_ideal_dvd _ (SixContact.J u).den_pos.ne'
    D.discriminant D.nonzero D.orders
  have lower := PeriodGaussian.height_of_stable_discriminant K hu _ D.period D.reduced D.discriminant
    D.nonzero divides D.formula
  have marked := marked_signed_jacobian hu (embedding u hu) (coords u hu) (theta u hu) (bg u hu)
  have primes : ∀ p ∈ HeightBudget.conductorPrimes Mult.S_mul u, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_union.mp hp).elim (fun h => Mult.prime_of_mem_S_mul h) Nat.prime_of_mem_primeFactors
  have upper := effective _ _ primes (SixJacobian.isAbelian hu) (SixJacobian.jacobian_dimension_two hu)
    (marked.elim rationalRM_of_marked) (good_outside ddmm hu)
  change hF (SixJacobian.jacobian hu) ≤ HeightBudget.vonKaenelBudget u at upper
  linarith only [lower,upper]

end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.PolePeriod
#print axioms ZInQBlueprint.ThetaClass.original_of_pole_period

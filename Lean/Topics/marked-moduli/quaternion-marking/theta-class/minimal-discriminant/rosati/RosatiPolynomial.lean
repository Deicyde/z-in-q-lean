import GlobalHeight
import RosatiPrincipalEndpoint

/-! The original bounded polynomial from the integral endomorphism order and
its principal polarization on the ordinary Shimura surface. -/
open CategoryTheory AlgebraicGeometry NumberField
namespace ZInQBlueprint.MinimalDiscriminant
open BinaryCover AbelianModel LocalJacobians QuaternionMarking GeometricMarking NormalDescent
open JacobianHeight JacobianConductor ThetaClass QuaternionLift TorsionHeight RosatiSigns ZInQ
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The height upper and lower bounds use real and quaternionic multiplication
on the same signed Jacobian. The two geometric hypotheses have distinct uses. -/
theorem original_of_signed_actions (hF : GroupScheme ℚ → ℝ) (hp : GlobalHeightFormula hF)
    (effective : EffectiveSurfaceHeight hF) (pqm : QuaternionPotentialReduction)
    (st : ∀ A : GroupScheme ℚ, IsAbelianScheme A → SerreTateCriterion A)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (actions : ∀ (u : ℚ) (hu : u ∉ contactSet), PrintedField hu ∧ RationalRM (SixJacobian.jacobian hu))
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget := by
  apply original_of_modular_height _ genus rank
  intro u hu
  obtain ⟨field,rm⟩ := actions u hu
  have lower := signed_height hp pqm st hu field
  have primes : ∀ p ∈ HeightBudget.conductorPrimes Mult.S_mul u, Nat.Prime p := by
    intro p h
    exact (Finset.mem_union.mp h).elim (fun t => Mult.prime_of_mem_S_mul t) Nat.prime_of_mem_primeFactors
  have upper := effective _ _ primes (SixJacobian.isAbelian hu) (SixJacobian.jacobian_dimension_two hu)
    rm (good_outside ddmm hu)
  change hF (SixJacobian.jacobian hu) ≤ HeightBudget.vonKaenelBudget u at upper
  linarith only [lower,upper]

/-- A polarized ordinary representative with the printed integral Rosati form
gives both actions. The Galois correction is a scalar order unit. -/
theorem original_of_rosati_comparison (hF : GroupScheme ℚ → ℝ) (hp : GlobalHeightFormula hF)
    (effective : EffectiveSurfaceHeight hF) (pqm : QuaternionPotentialReduction)
    (st : ∀ A : GroupScheme ℚ, IsAbelianScheme A → SerreTateCriterion A)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (factor : CartierPrimeFactorization) (U : ShimuraClassMap) (models : RosatiPrintedComparison U)
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget := by
  apply original_of_signed_actions hF hp effective pqm st ddmm _ genus rank
  intro u hu
  exact ⟨printedField_of_rosati U models hu, (marked_of_shimura U models factor hu).elim rationalRM_of_marked⟩

/-- A bare isomorphism of the printed Jacobian with the ordinary Shimura
surface suffices under two uniform polarization theorems for discriminant six. -/
theorem original_of_ordinary_comparison (hF : GroupScheme ℚ → ℝ) (hp : GlobalHeightFormula hF)
    (effective : EffectiveSurfaceHeight hF) (pqm : QuaternionPotentialReduction)
    (st : ∀ A : GroupScheme ℚ, IsAbelianScheme A → SerreTateCriterion A)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (factor : CartierPrimeFactorization) (U : ShimuraClassMap) (models : UnpolarizedPrintedComparison U)
    (uniquePol : UniqueD6Polarization) (primitive : PrimitivePrincipalExists)
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget := by
  apply original_of_signed_actions hF hp effective pqm st ddmm _ genus rank
  intro u hu
  exact ⟨printedField_of_unpolarized U uniquePol models hu,
    (marked_of_unpolarized U models uniquePol primitive factor hu).elim rationalRM_of_marked⟩

end
end ZInQBlueprint.MinimalDiscriminant
#print axioms ZInQBlueprint.MinimalDiscriminant.original_of_signed_actions
#print axioms ZInQBlueprint.MinimalDiscriminant.original_of_rosati_comparison
#print axioms ZInQBlueprint.MinimalDiscriminant.original_of_ordinary_comparison

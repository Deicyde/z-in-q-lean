import RosatiPolynomial
import SixCanonicalPeriods

/-! The original bound from the genus-two sextic defined by the modular
forms on the discriminant-six Shimura curve. -/
open CategoryTheory AlgebraicGeometry NumberField
namespace ZInQBlueprint.MinimalDiscriminant
open BinaryCover AbelianModel LocalJacobians QuaternionMarking GeometricMarking NormalDescent
open JacobianHeight JacobianConductor ThetaClass QuaternionLift TorsionHeight RosatiSigns ShimuraAtlas ZInQ
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The point of the coarse scheme, its modular sextic, the literal printed
Jacobian and the two height bounds refer to the same rational parameter. -/
theorem original_of_modular_comparison (hF : GroupScheme ℚ → ℝ) (hp : GlobalHeightFormula hF)
    (effective : EffectiveSurfaceHeight hF) (pqm : QuaternionPotentialReduction)
    (st : ∀ A : GroupScheme ℚ, IsAbelianScheme A → SerreTateCriterion A)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (factor : CartierPrimeFactorization) {M : Over (Spec (.of ℚ))}
    (C : CoarseInterpretation M) (chart : Line ⟶ M)
    (ι : Qbar →+* ℂ) (hom : HomBaseChange ι) (uniformization : ModularComparison C chart ι hom)
    (uniquePol : UniqueD6Polarization) (primitive : PrimitivePrincipalExists)
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget :=
  original_of_ordinary_comparison hF hp effective pqm st ddmm factor (shimuraClassMap C chart)
    (unpolarized_of_modular C chart ι hom uniformization) uniquePol primitive genus rank

/-- The modular coordinates, their lifts, and the period theorem on the same
point of the upper half-plane give the bounded polynomial conclusion. -/
theorem original_of_canonical_periods (hF : GroupScheme ℚ → ℝ) (hp : GlobalHeightFormula hF)
    (effective : EffectiveSurfaceHeight hF) (pqm : QuaternionPotentialReduction)
    (st : ∀ A : GroupScheme ℚ, IsAbelianScheme A → SerreTateCriterion A)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (factor : CartierPrimeFactorization) {M : Over (Spec (.of ℚ))}
    (C : CoarseInterpretation M) (chart : Line ⟶ M)
    (ι : Qbar →+* ℂ) (hom : HomBaseChange ι) (periods : CanonicalPeriods C chart ι hom)
    (uniquePol : UniqueD6Polarization) (primitive : PrimitivePrincipalExists)
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget :=
  original_of_modular_comparison hF hp effective pqm st ddmm factor C chart ι hom
    (modular_of_canonical periods) uniquePol primitive genus rank

end
end ZInQBlueprint.MinimalDiscriminant
#print axioms ZInQBlueprint.MinimalDiscriminant.original_of_modular_comparison
#print axioms ZInQBlueprint.MinimalDiscriminant.original_of_canonical_periods

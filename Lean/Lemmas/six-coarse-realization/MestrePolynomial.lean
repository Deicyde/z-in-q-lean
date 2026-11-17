import AlgebraicCoarse
import RosatiPolynomial

/-! The original bounded-existence theorem through the algebraic Mestre
equation and the ordinary algebraic quotient. -/
open CategoryTheory AlgebraicGeometry NumberField
namespace ZInQBlueprint.MinimalDiscriminant
open BinaryCover AbelianModel LocalJacobians QuaternionMarking GeometricMarking NormalDescent
open JacobianHeight JacobianConductor ThetaClass QuaternionLift TorsionHeight RosatiSigns ShimuraAtlas ZInQ
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem original_of_mestre (hF : GroupScheme ℚ → ℝ) (hp : GlobalHeightFormula hF)
    (effective : EffectiveSurfaceHeight hF) (pqm : QuaternionPotentialReduction)
    (st : ∀ A : GroupScheme ℚ, IsAbelianScheme A → SerreTateCriterion A)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (factor : CartierPrimeFactorization) {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (E : Qbar → GroupIsoClass Qbar)
    (algebraic : AlgebraicOrdinaryClasses C chart) (forget : AlgebraicForgetfulMap C chart E)
    (mestre : MestreEquation E) (uniquePol : UniqueD6Polarization) (primitive : PrimitivePrincipalExists)
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget :=
  original_of_ordinary_comparison hF hp effective pqm st ddmm factor (shimuraClassMap C chart)
    (unpolarized_of_mestre C chart algebraic forget mestre) uniquePol primitive genus rank

end
end ZInQBlueprint.MinimalDiscriminant
#print axioms ZInQBlueprint.MinimalDiscriminant.original_of_mestre

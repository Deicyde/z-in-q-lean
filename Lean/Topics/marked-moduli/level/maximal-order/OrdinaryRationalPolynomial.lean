import OrdinaryMestrePolynomial
import RationalMestre

/-! The rational part of the ordinary real-labelled Shimura chart suffices for
Glazer's bounded polynomial. Either of the two rational slopes can be used. -/
open CategoryTheory AlgebraicGeometry NumberField
namespace ZInQBlueprint.ShimuraAtlas
open QuaternionLift NormalDescent
noncomputable section

/-- At one of the two rational slopes, find a labelled ordinary surface with
a finite integral endomorphism ring inside a rational algebra of dimension at most four. -/
def RationalQMClasses {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) : Prop :=
  ∀ (t j : ℚ), OutsideCM j → j*(64*j-81)*(27*j+16) ≠ 0 → j*(t^2+27) = -16 →
    ∃ v : ℚ, v^2 = t^2 ∧
      C.read (linePoint (v : Qbar) ≫ chart) ∈ Set.range OrdinaryQMPoint.coarseClass

theorem rationalOrdinary_of_qm {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (ordinary : RationalQMClasses C chart) : RationalOrdinaryClasses C chart := by
  intro t j nonCM openLocus quotient
  obtain ⟨v, hv, w, hw⟩ := ordinary t j nonCM openLocus quotient
  exact ⟨v, hv, w.asOrdinary, w.asOrdinary_coarseClass.trans hw⟩

end
end ZInQBlueprint.ShimuraAtlas

namespace ZInQBlueprint.MinimalDiscriminant
open BinaryCover AbelianModel LocalJacobians QuaternionMarking GeometricMarking NormalDescent
open JacobianHeight JacobianConductor ThetaClass QuaternionLift TorsionHeight RosatiSigns ShimuraAtlas ZInQ
noncomputable section

/-- The original bound from the rational ordinary locus and the algebraic Mestre equation. -/
theorem original_of_rational_ordinary_mestre (hF : GroupScheme ℚ → ℝ) (hp : GlobalHeightFormula hF)
    (effective : EffectiveSurfaceHeight hF) (pqm : QuaternionPotentialReduction)
    (st : ∀ A : GroupScheme ℚ, IsAbelianScheme A → SerreTateCriterion A)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (factor : CartierPrimeFactorization) {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (E : Qbar → GroupIsoClass Qbar)
    (ordinary : RationalQMClasses C chart) (forget : RationalForgetfulMap C chart E)
    (mestre : RationalMestreEquation E) (uniquePol : UniqueD6Polarization) (primitive : PrimitivePrincipalExists)
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget :=
  original_of_rational_mestre hF hp effective pqm st ddmm factor C chart E
    (rationalOrdinary_of_qm C chart ordinary) forget mestre uniquePol primitive genus rank

end
end ZInQBlueprint.MinimalDiscriminant

#print axioms ZInQBlueprint.ShimuraAtlas.rationalOrdinary_of_qm
#print axioms ZInQBlueprint.MinimalDiscriminant.original_of_rational_ordinary_mestre

import OrdinaryRationalPolynomial
import IgusaPolynomial
import RationalSlopeCM

/-! The bounded polynomial from the polarized Igusa class on the ordinary
rational chart. The Rosati condition is stated on the original order action. -/
open CategoryTheory AlgebraicGeometry NumberField
open scoped ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ShimuraAtlas
open QuaternionLift NormalDescent LevelThree RosatiSigns
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Polarized automorphisms preserve the printed Riemann form under the
specified integral action of the discriminant-six order. -/
def OrdinaryQMPoint.rosatiAction (w : OrdinaryQMPoint) : Prop :=
  ∀ (a : w.surface ≅ w.surface) (x : O), w.action x = End.of a.hom →
    Compatible a w.theta w.theta → dagger (embed x) * embed x = 1

theorem OrdinaryQMPoint.rosatiPresentation (w : OrdinaryQMPoint) (h : w.rosatiAction) :
    IsRosatiPresentation w.asOrdinary.theta w.asOrdinary.order := by
  intro a preserves
  exact h a (w.asOrdinary.order.symm (End.of a.hom))
    (w.asOrdinary.order.apply_symm_apply (End.of a.hom)) preserves

/-- On the punctured rational slope line, one choice of sign carries the
given quaternion action and its Rosati form. The underlying surface and
polarization are part of that single representative. -/
def OrdinaryRosatiLocus {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) : Prop :=
  ∀ t : ℚ, t ≠ 0 → ∃ v : ℚ, v^2 = t^2 ∧ ∃ w : OrdinaryQMPoint,
    w.coarseClass = C.read (linePoint (v : Qbar) ≫ chart) ∧ w.rosatiAction

theorem rationalRosati_of_locus {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (ordinary : OrdinaryRosatiLocus C chart) : RationalRosatiClasses C chart := by
  intro t j nonCM _det quotient
  obtain ⟨v,hv,w,point,rosati⟩ := ordinary t ((outsideCM_iff_slope_ne_zero quotient).mp nonCM)
  exact ⟨v,hv,w.asOrdinary,w.asOrdinary_coarseClass.trans point,w.rosatiPresentation rosati⟩

/-- Forgetting the generator on the punctured rational chart yields the
polarized Igusa class at the arithmetic coordinate -16/(t²+27). -/
def OrdinaryForgetfulLocus {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (read : IgusaCoordinates → ModuliClass) : Prop :=
  ∀ t : ℚ, t ≠ 0 →
    C.read (linePoint (t : Qbar) ≫ chart) ∈ Set.range OrdinarySurface.coarseClass →
    forgetOrder (C.read (linePoint (t : Qbar) ≫ chart)) = read (bgCoordinates (-16 / (t^2+27)))

theorem rationalForgetful_iff_locus {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (read : IgusaCoordinates → ModuliClass) :
    RationalPolarizedForgetful C chart read ↔ OrdinaryForgetfulLocus C chart read := by
  constructor
  · intro h t ht point
    have den : t^2+27 ≠ 0 := by positivity
    have eqn : (-16 / (t^2+27)) * (t^2+27) = -16 := div_mul_cancel₀ _ den
    exact h _ _ ((outsideCM_iff_slope_ne_zero eqn).mpr ht) ((mestre_open_iff_slope_ne_zero eqn).mpr ht) eqn point
  · intro h t j nonCM _det eqn point
    have den : t^2+27 ≠ 0 := by positivity
    have hj : j = -16 / (t^2+27) := (eq_div_iff den).mpr eqn
    rw [hj]
    exact h t ((outsideCM_iff_slope_ne_zero eqn).mp nonCM) point

end
end ZInQBlueprint.ShimuraAtlas

namespace ZInQBlueprint.MinimalDiscriminant
open BinaryCover AbelianModel LocalJacobians QuaternionMarking GeometricMarking NormalDescent
open JacobianHeight JacobianConductor ThetaClass QuaternionLift TorsionHeight RosatiSigns ShimuraAtlas ZInQ
noncomputable section

/-- The original bounded integer-defining polynomial from the polarized
Igusa classification, the labelled ordinary Shimura chart, and the
height, reduction, Cartier divisor and rank inputs. -/
theorem original_of_ordinary_igusa (hF : GroupScheme ℚ → ℝ) (hp : GlobalHeightFormula hF)
    (effective : EffectiveSurfaceHeight hF) (pqm : QuaternionPotentialReduction)
    (st : ∀ A : GroupScheme ℚ, IsAbelianScheme A → SerreTateCriterion A)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (factor : CartierPrimeFactorization) {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (read : IgusaCoordinates → ModuliClass)
    (classification : PolarizedIgusaClassification read) (ordinary : OrdinaryRosatiLocus C chart)
    (forget : OrdinaryForgetfulLocus C chart read) (genus : OriginalRank.HigherOrderGenusCoefficient)
    (rank : OriginalRank.ModularSimpleZero) : FrozenTarget :=
  original_of_polarized_igusa hF hp effective pqm st ddmm factor C chart read classification
    (rationalRosati_of_locus C chart ordinary) ((rationalForgetful_iff_locus C chart read).mpr forget) genus rank

end
end ZInQBlueprint.MinimalDiscriminant

#print axioms ZInQBlueprint.ShimuraAtlas.OrdinaryQMPoint.rosatiPresentation
#print axioms ZInQBlueprint.ShimuraAtlas.rationalRosati_of_locus
#print axioms ZInQBlueprint.ShimuraAtlas.rationalForgetful_iff_locus
#print axioms ZInQBlueprint.MinimalDiscriminant.original_of_ordinary_igusa

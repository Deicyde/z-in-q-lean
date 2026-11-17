import SignedWeierstrassChart
import OrdinaryCurveMarked

/-! The change of coordinates on the standard Weierstrass model supplies
the all-point coordinate hypothesis required for descent of the marking. -/
open CategoryTheory AlgebraicGeometry Polynomial NumberField Real
open scoped ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.CMRepair
open WeierstrassCoordinates BinaryCover AbelianModel NormalDescent GeometricMarking MarkedForm SixAbelMap
open WeightedCurvePoints ThetaClass JacobianHeight TorsionHeight MinimalDiscriminant
open QuaternionLift ShimuraAtlas CanonicalTheta JacobianConductor LocalJacobians ArchimedeanHeight ZInQ
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every actual automorphism of the scalar-extended curve has the indicated
homogeneous lift, including at the two points above infinity. -/
theorem curveCoordinateLifts_of_voight (coordinates : VoightCoordinateFormula) {u : ℚ}
    (hu : u ∉ contactSet) : CurveCoordinateLifts hu := by
  intro e
  obtain ⟨g,k,eq,affine⟩ := signed_pullback_action coordinates hu e
  let t : Lift u (δ u) := ⟨g,k,eq⟩
  refine ⟨t,weighted_action_of_voight hu e t ?_⟩
  intro p
  exact affine p (denominator_ne hu t p.1.1)

theorem original_of_ordinary_marking_and_voight (hF : GroupScheme ℚ → ℝ)
    (hp : GlobalHeightFormula hF) (effective : EffectiveSurfaceHeight hF)
    (pqm : QuaternionPotentialReduction)
    (st : ∀ A : GroupScheme ℚ, IsAbelianScheme A → SerreTateCriterion A)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (field : OrdinaryRationalCurveMarking) (coordinates : VoightCoordinateFormula)
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget :=
  original_of_ordinary_rational_curve_marking hF hp effective pqm st ddmm field
    (curveCoordinateLifts_of_voight coordinates) genus rank

end
end ZInQBlueprint.CMRepair
#print axioms ZInQBlueprint.CMRepair.curveCoordinateLifts_of_voight
#print axioms ZInQBlueprint.CMRepair.original_of_ordinary_marking_and_voight

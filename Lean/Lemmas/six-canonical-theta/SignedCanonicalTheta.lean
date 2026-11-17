import ThetaPicardModel
import SignedPoincare
import ThetaDivisorMarking

/-! The theta line is the pointed Poincaré determinant on the Jacobian of the signed rational sextic. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve GoodReductionJacobian NeronModelInfra MonoidalCategory
open JacobianVarieties.Picard.Unpointed
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.CanonicalTheta
open BinaryCover SixAbelMap NormalDescent GeometricMarking QuaternionMarking
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

private theorem signedProper (u : ℚ) : IsProper (paperCurve u).hom := by
  let := paper_proper ℚ u
  exact inferInstanceAs (IsProper (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))

private theorem signedIntegral {u : ℚ} (hu : u ∉ ZInQ.contactSet) : GeometricallyIntegral (paperCurve u).hom := by
  let := geometricallyIntegral_paperModel hu
  exact inferInstanceAs (GeometricallyIntegral (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))

private theorem signedDimension {u : ℚ} (hu : u ∉ ZInQ.contactSet) : SmoothOfRelativeDimension 1 (paperCurve u).hom := by
  let c := (paperModel ℚ u).hom
  let : Smooth c := smooth_paperModel hu
  let : AlgebraicGeometry.IsIntegral (paperModel ℚ u).left := paper_reglued_integral ℚ hu
  let : SmoothOfRelativeDimension 1 c := SixJacobian.relative_dimension_one c (paper_dimension ℚ u)
  exact inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd c (scalarMap ℚ Qbar)))

variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)
local notation "J" => geometricJacobian hu

def signedPointed :
    letI := signedProper u
    letI := signedIntegral hu
    letI := signedDimension hu
    let e := IntegralPicard.paperJacobian_baseChangeIso Qbar hu (paperCurve u) (Iso.refl _)
    Pointed (basepoint hu) e (rigidMorphism hu) := by
  letI := signedProper u
  letI := signedIntegral hu
  letI := signedDimension hu
  letI := sourceIntegral hu
  letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
  have h := rigid_classifies hu
  exact Classical.choice (show Nonempty (Pointed (basepoint hu) _ (rigidMorphism hu)) by
    obtain ⟨Z,R,aj,k,c⟩ := h
    exact ⟨⟨Z,R,aj,k,c⟩⟩)

/-- The line itself remembers the universal pointed Picard representation. -/
def signedThetaLine : (geometricJacobian hu).X.left.Modules := by
  letI := signedProper u
  letI := signedIntegral hu
  letI := signedDimension hu
  exact (signedPointed hu).determinantLine

theorem signedThetaLine_determinant :
    letI := signedProper u
    letI := signedIntegral hu
    letI := signedDimension hu
    let P := signedPointed hu
    signedThetaLine hu = (Scheme.Modules.pullback P.toRepresenting.hom.left).obj
      (thetaBundle (paperCurve u).hom (schemePoint (basepoint hu)) P.J.toBase P.represents.poincare 4 3) := rfl

theorem signed_theta_witness : (signedThetaLine hu).IsInvertible ∧
    ∃ θ : 𝟙_ (geometricJacobian hu).X.left.Modules ⟶ signedThetaLine hu, θ ≠ 0 ∧
      {x : sections J | Scheme.Modules.pullbackSection x.toMul.left θ = 0} = Set.range (rigidDivisors hu).abel := by
  let := signedProper u
  let := signedIntegral hu
  let := signedDimension hu
  let := sourceIntegral hu
  let := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let N := signedModel hu
  let := N.curve
  let : Algebra.EssFiniteType Qbar (paperCurve u).left.functionField :=
    AlgebraicCurve.essFiniteType_functionField (paperCurve u).hom
  obtain ⟨invL,θ,ne,read⟩ := (signedPointed hu).exists_theta N.model N.iso N.hbase (paper_functionField_genus hu)
  refine ⟨invL,θ,ne,?_⟩
  ext x
  change Scheme.Modules.pullbackSection x.toMul.left θ = 0 ↔ _
  rw [read x.toMul]
  constructor
  · rintro ⟨p,hp⟩
    obtain ⟨y,hy⟩ := (WeightedCurvePoints.weightedEquiv_pullback hu).surjective p
    exact ⟨y,(rigid_on_points hu y).trans (congrArg Additive.ofMul ((congrArg (· ≫ rigidMorphism hu) hy).trans hp))⟩
  · rintro ⟨y,rfl⟩
    exact ⟨WeightedCurvePoints.weightedEquiv_pullback hu y,congrArg Additive.toMul (rigid_on_points hu y).symm⟩

def signedThetaSection : 𝟙_ (geometricJacobian hu).X.left.Modules ⟶ signedThetaLine hu :=
  (signed_theta_witness hu).2.choose

theorem signedThetaLine_invertible : (signedThetaLine hu).IsInvertible := (signed_theta_witness hu).1

theorem signedThetaSection_ne_zero : signedThetaSection hu ≠ 0 := (signed_theta_witness hu).2.choose_spec.1

theorem signedThetaSection_zeros :
    {x : sections J | Scheme.Modules.pullbackSection x.toMul.left (signedThetaSection hu) = 0} =
        Set.range (rigidDivisors hu).abel := (signed_theta_witness hu).2.choose_spec.2
end
end ZInQBlueprint.CanonicalTheta
#print axioms ZInQBlueprint.CanonicalTheta.signedThetaLine_determinant
#print axioms ZInQBlueprint.CanonicalTheta.signed_theta_witness
#print axioms ZInQBlueprint.CanonicalTheta.signedThetaLine_invertible
#print axioms ZInQBlueprint.CanonicalTheta.signedThetaSection_ne_zero
#print axioms ZInQBlueprint.CanonicalTheta.signedThetaSection_zeros

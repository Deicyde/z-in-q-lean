import SignedPointDifferences
import PointedAbelClass
import AbelScalarTransport
import SignedPoincare

/-! The Poincaré-normalized Abel map on the signed complete curve agrees
with the rational Jacobian's class of the two actual relative graph ideals. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open JacobianVarieties.Picard.Unpointed
open scoped CategoryTheory.MonObj CategoryTheory.Obj
namespace ZInQBlueprint.AbelGalois
open BinaryCover GeometricMarking SixAbelMap NormalDescent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)

theorem rigid_point_class (p : CurvePoints u) :
    Additive.ofMul (p ≫ rigidMorphism hu) = signedDifference hu p (basepoint hu) := by
  let C := paperModel ℚ u
  let D := paperCurve u
  let b := basepoint hu
  let : IsProper C.hom := paper_proper ℚ u
  let : GeometricallyIntegral C.hom := geometricallyIntegral_paperModel hu
  let : Smooth C.hom := smooth_paperModel hu
  let : AlgebraicGeometry.IsIntegral C.left := paper_reglued_integral ℚ hu
  let : SmoothOfRelativeDimension 1 C.hom := SixJacobian.relative_dimension_one C.hom (paper_dimension ℚ u)
  let : IsProper D.hom := inferInstanceAs (IsProper (pullback.snd C.hom (specExtension ℚ Qbar)))
  let : SmoothOfRelativeDimension 1 D.hom := inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd C.hom (specExtension ℚ Qbar)))
  let : GeometricallyIntegral D.hom := inferInstanceAs (GeometricallyIntegral (pullback.snd C.hom (specExtension ℚ Qbar)))
  let e := IntegralPicard.paperJacobian_baseChangeIso Qbar hu D (Iso.refl D)
  let E := CommGrp.forget (Over (Spec (.of Qbar))) |>.mapIso e
  have pt := pointed_abel_class D b (rigidMorphism hu ≫ E.hom) (rigid_classifies hu) p
  have bc := baseChange_difference C p b
  apply Additive.toMul.injective
  apply (cancel_mono E.hom).1
  calc
    (p ≫ rigidMorphism hu) ≫ E.hom = p ≫ (rigidMorphism hu ≫ E.hom) := Category.assoc .. 
    _ = (pointDifference D.hom p b).toMul := congrArg Additive.toMul pt
    _ = (signedDifference hu p b).toMul ≫ E.hom := bc.symm

theorem rigid_translated_image (σ : Qbar ≃ₐ[ℚ] Qbar) :
    geometricAction (SixJacobian.jacobian hu) σ ''
      Set.range (fun p : CurvePoints u => Additive.ofMul (p ≫ rigidMorphism hu)) =
      Set.range (fun p : CurvePoints u => Additive.ofMul (p ≫ rigidMorphism hu) -
        Additive.ofMul (galoisPoint (X := paperModel ℚ u) σ (basepoint hu) ≫ rigidMorphism hu)) :=
  translated_image_of_matches hu _ _ (rigid_point_class hu) σ

end
end ZInQBlueprint.AbelGalois
#print axioms ZInQBlueprint.AbelGalois.rigid_point_class
#print axioms ZInQBlueprint.AbelGalois.rigid_translated_image

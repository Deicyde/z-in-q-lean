import GeometricPointDifferences
import SignedSixAbel

/-! Moving-base-point theorem for the actual rational six-contact Jacobian. -/
open CategoryTheory AlgebraicGeometry
open JacobianVarieties.Picard.Unpointed
open scoped CategoryTheory.MonObj CategoryTheory.Obj
namespace ZInQBlueprint.AbelGalois
open BinaryCover GeometricMarking SixAbelMap NormalDescent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)

include hu in
private theorem signed_dim : SmoothOfRelativeDimension 1 (paperModel ℚ u).hom := by
  let := smooth_paperModel hu
  let : AlgebraicGeometry.IsIntegral (paperModel ℚ u).left := paper_reglued_integral ℚ hu
  exact SixJacobian.relative_dimension_one _ (paper_dimension ℚ u)

def signedDifference (p q : CurvePoints u) : JacobianPoints hu := by
  let : IsProper (paperModel ℚ u).hom := paper_proper ℚ u
  let : GeometricallyIntegral (paperModel ℚ u).hom := geometricallyIntegral_paperModel hu
  let : SmoothOfRelativeDimension 1 (paperModel ℚ u).hom := signed_dim hu
  exact geometricDifference (paperModel ℚ u) p q

theorem signed_galois (σ : Qbar ≃ₐ[ℚ] Qbar) (p q : CurvePoints u) :
    geometricAction (SixJacobian.jacobian hu) σ (signedDifference hu p q) =
      signedDifference hu (galoisPoint (X := paperModel ℚ u) σ p)
        (galoisPoint (X := paperModel ℚ u) σ q) := by
  let : IsProper (paperModel ℚ u).hom := paper_proper ℚ u
  let : GeometricallyIntegral (paperModel ℚ u).hom := geometricallyIntegral_paperModel hu
  let : SmoothOfRelativeDimension 1 (paperModel ℚ u).hom := signed_dim hu
  exact geometric_galois (paperModel ℚ u) σ p q

theorem signed_chain (p q r : CurvePoints u) :
    signedDifference hu p q + signedDifference hu q r = signedDifference hu p r := by
  let : IsProper (paperModel ℚ u).hom := paper_proper ℚ u
  let : GeometricallyIntegral (paperModel ℚ u).hom := geometricallyIntegral_paperModel hu
  let : SmoothOfRelativeDimension 1 (paperModel ℚ u).hom := signed_dim hu
  exact geometric_chain (paperModel ℚ u) p q r

theorem signed_translated_image (σ : Qbar ≃ₐ[ℚ] Qbar) (b : CurvePoints u) :
    geometricAction (SixJacobian.jacobian hu) σ '' Set.range (fun p => signedDifference hu p b) =
      Set.range (fun p => signedDifference hu p b -
        signedDifference hu (galoisPoint (X := paperModel ℚ u) σ b) b) := by
  let : IsProper (paperModel ℚ u).hom := paper_proper ℚ u
  let : GeometricallyIntegral (paperModel ℚ u).hom := geometricallyIntegral_paperModel hu
  let : SmoothOfRelativeDimension 1 (paperModel ℚ u).hom := signed_dim hu
  exact translated_image (paperModel ℚ u) σ b

theorem translated_image_of_matches (m : paperCurve u ⟶ (geometricJacobian hu).X)
    (b : CurvePoints u)
    (classifies : ∀ p : CurvePoints u, Additive.ofMul (p ≫ m) = signedDifference hu p b)
    (σ : Qbar ≃ₐ[ℚ] Qbar) :
    geometricAction (SixJacobian.jacobian hu) σ '' Set.range (fun p : CurvePoints u => Additive.ofMul (p ≫ m)) =
      Set.range (fun p : CurvePoints u => Additive.ofMul (p ≫ m) -
        Additive.ofMul (galoisPoint (X := paperModel ℚ u) σ b ≫ m)) := by
  simpa only [classifies] using signed_translated_image hu σ b

end
end ZInQBlueprint.AbelGalois
#print axioms ZInQBlueprint.AbelGalois.signed_galois
#print axioms ZInQBlueprint.AbelGalois.signed_chain
#print axioms ZInQBlueprint.AbelGalois.signed_translated_image
#print axioms ZInQBlueprint.AbelGalois.translated_image_of_matches

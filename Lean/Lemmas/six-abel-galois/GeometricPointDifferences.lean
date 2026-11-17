import RepresentedPointDifferences
import CoefficientSections

/-! Moving the base point on the geometric points of the scalar extension of
the rational unpointed Jacobian. The arithmetic coefficient action is the one
compared with the scheme-theoretic deck map by `galoisPoint_deck`. -/
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RelPicard JacobianVarieties.Picard.Unpointed
open scoped CategoryTheory.MonObj CategoryTheory.Obj
namespace ZInQBlueprint.AbelGalois
noncomputable section
variable {K L : Type} [Field K] [Field L] [Algebra K L]
variable (X : Over (Spec (.of K)))
  [IsProper X.hom] [SmoothOfRelativeDimension 1 X.hom] [GeometricallyIntegral X.hom]
abbrev geometricSections (L : Type) [Field L] [Algebra K L] (Y : Over (Spec (.of K))) :=
  fieldPoint L ⟶ (Over.pullback (NormalDescent.specExtension K L)).obj Y

abbrev geometricGroup (L : Type) [Field L] [Algebra K L] (A : AbelianModel.GroupScheme K) :=
  Additive (fieldPoint L ⟶ ((AbelianModel.baseChange (algebraMap K L)).obj A).X)

def geometricDifference (p q : geometricSections L X) :
    geometricGroup L (groupScheme K X.hom) :=
  pointAddEquiv _ (pointDifference X.hom ((equivPoints X).symm p) ((equivPoints X).symm q))

theorem geometric_chain (p q r : geometricSections L X) :
    geometricDifference X p q + geometricDifference X q r = geometricDifference X p r := by
  unfold geometricDifference
  rw [←map_add,point_chain]

def geometricAction (A : AbelianModel.GroupScheme K) (σ : L ≃ₐ[K] L) :
    geometricGroup L A → geometricGroup L A :=
  fun v => Additive.ofMul (galoisPoint σ v.toMul)

theorem geometric_galois (σ : L ≃ₐ[K] L) (p q : geometricSections L X) :
    geometricAction (groupScheme K X.hom) σ (geometricDifference X p q) =
      geometricDifference X (galoisPoint σ p) (galoisPoint σ q) := by
  apply Additive.toMul.injective
  change (equivPoints _) (coefficient σ ≫ (equivPoints _).symm ((equivPoints _)
    (pointDifference X.hom ((equivPoints X).symm p) ((equivPoints X).symm q)).toMul)) =
    (equivPoints _) ((pointDifference X.hom ((equivPoints X).symm _) ((equivPoints X).symm _)).toMul)
  rw [Equiv.symm_apply_apply,point_pull]
  unfold galoisPoint
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]

theorem moving_basepoint (σ : L ≃ₐ[K] L) (p b : geometricSections L X) :
    geometricAction (groupScheme K X.hom) σ (geometricDifference X p b) =
      geometricDifference X (galoisPoint σ p) b - geometricDifference X (galoisPoint σ b) b := by
  rw [geometric_galois,eq_sub_iff_add_eq,geometric_chain]

theorem translated_image (σ : L ≃ₐ[K] L) (b : geometricSections L X) :
    geometricAction (groupScheme K X.hom) σ '' Set.range (fun p => geometricDifference X p b) =
      Set.range (fun p => geometricDifference X p b - geometricDifference X (galoisPoint σ b) b) := by
  ext v
  constructor
  · rintro ⟨_,⟨p,rfl⟩,rfl⟩
    exact ⟨galoisPoint σ p,(moving_basepoint X σ p b).symm⟩
  · rintro ⟨p,rfl⟩
    obtain ⟨q,hq⟩ := (galoisEquiv X σ).surjective p
    change galoisPoint σ q = p at hq
    exact ⟨_,⟨q,rfl⟩,(moving_basepoint X σ q b).trans (by rw [hq])⟩

end
end ZInQBlueprint.AbelGalois
#print axioms ZInQBlueprint.AbelGalois.geometric_galois
#print axioms ZInQBlueprint.AbelGalois.geometric_chain
#print axioms ZInQBlueprint.AbelGalois.moving_basepoint
#print axioms ZInQBlueprint.AbelGalois.translated_image

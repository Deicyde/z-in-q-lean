import NormalDescent
import AbelianModel
import Nyll.SchemeTheory.CategoryTheory.AdjunctionGroupPoints

/-! Coefficient action on geometric sections, with the direction of the deck projection explicit. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj
namespace ZInQBlueprint.AbelGalois
open NormalDescent
noncomputable section
variable {K L : Type} [Field K] [Field L] [Algebra K L]

abbrev fieldPoint (L : Type) [Field L] := Over.mk (𝟙 (Spec (.of L)))
abbrev fieldTest (K L : Type) [Field K] [Field L] [Algebra K L] :=
  (Over.map (specExtension K L)).obj (fieldPoint L)
abbrev equivPoints (X : Over (Spec (.of K))) :=
  (Over.mapPullbackAdj (specExtension K L)).homEquiv (fieldPoint L) X

def coefficient (σ : L ≃ₐ[K] L) : fieldTest K L ⟶ fieldTest K L :=
  Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
    change Spec.map _ ≫ 𝟙 _ ≫ specExtension K L = 𝟙 _ ≫ specExtension K L
    rw [Category.id_comp, ←Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext σ.toAlgHom.comp_algebraMap))

def galoisPoint {X : Over (Spec (.of K))} (σ : L ≃ₐ[K] L)
    (p : fieldPoint L ⟶ (Over.pullback (specExtension K L)).obj X) :
    fieldPoint L ⟶ (Over.pullback (specExtension K L)).obj X :=
  equivPoints X (coefficient σ ≫ (equivPoints X).symm p)

private theorem equiv_fst {X : Over (Spec (.of K))} (p : fieldTest K L ⟶ X) :
    (equivPoints X p).left ≫ pullback.fst X.hom (specExtension K L) = p.left := by
  exact congrArg Over.Hom.left ((equivPoints X).symm_apply_apply p)

private theorem symm_left {X : Over (Spec (.of K))}
    (p : fieldPoint L ⟶ (Over.pullback (specExtension K L)).obj X) :
    ((equivPoints X).symm p).left = p.left ≫ pullback.fst X.hom (specExtension K L) := rfl

theorem galoisPoint_deck {X : Over (Spec (.of K))} (σ : L ≃ₐ[K] L)
    (p : fieldPoint L ⟶ (Over.pullback (specExtension K L)).obj X) :
    (galoisPoint σ p).left ≫ deck X.hom σ =
      (Spec.map (CommRingCat.ofHom σ.toRingHom)) ≫ p.left := by
  apply pullback.hom_ext (f := X.hom) (g := specExtension K L)
  · rw [Category.assoc, deck_fst, galoisPoint, equiv_fst,Category.assoc]
    exact congrArg ((coefficient σ).left ≫ ·) (symm_left p)
  · have hw : p.left ≫ pullback.snd X.hom (specExtension K L) = 𝟙 _ := p.w
    have hw' : (galoisPoint σ p).left ≫ pullback.snd X.hom (specExtension K L) = 𝟙 _ :=
      (galoisPoint σ p).w
    rw [Category.assoc,deck_snd,←Category.assoc,hw',Category.id_comp,Category.assoc,hw]
    exact (Category.comp_id _).symm

private theorem coefficient_inv (σ : L ≃ₐ[K] L) :
    coefficient σ ≫ coefficient σ.symm = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp,← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x => σ.apply_symm_apply x))

def galoisEquiv (X : Over (Spec (.of K))) (σ : L ≃ₐ[K] L) :
    Equiv.Perm (fieldPoint L ⟶ (Over.pullback (specExtension K L)).obj X) where
  toFun := galoisPoint σ
  invFun := galoisPoint σ.symm
  left_inv p := by
    unfold galoisPoint
    rw [Equiv.symm_apply_apply,←Category.assoc]
    have e : coefficient σ.symm ≫ coefficient σ = 𝟙 _ := coefficient_inv σ.symm
    rw [e,Category.id_comp,Equiv.apply_symm_apply]
  right_inv p := by
    unfold galoisPoint
    simp only [Equiv.symm_apply_apply,←Category.assoc,coefficient_inv,Category.id_comp,
      Equiv.apply_symm_apply]

def pointAddEquiv (A : AbelianModel.GroupScheme K) :
    Additive (fieldTest K L ⟶ A.X) ≃+
      Additive (fieldPoint L ⟶ ((AbelianModel.baseChange (algebraMap K L)).obj A).X) :=
  ((Over.mapPullbackAdj (specExtension K L)).homMulEquiv (fieldPoint L) A.X).toAdditive

end
end ZInQBlueprint.AbelGalois
#print axioms ZInQBlueprint.AbelGalois.galoisPoint_deck
#print axioms ZInQBlueprint.AbelGalois.galoisEquiv
#print axioms ZInQBlueprint.AbelGalois.pointAddEquiv

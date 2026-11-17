import ScalarGraphComparison
import UnpointedScalarClasses

/-! The canonical base-change isomorphism sends the geometric rational class
of P-Q to its class on the scalar-extended curve, with exactly these sections. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.GeneralizedJacobian AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra Opposite GoodReductionJacobian JacobianVarieties.Picard.Unpointed
open scoped CategoryTheory.MonObj
attribute [local instance] filteredCommGrpHasColimitsOfShape
namespace ZInQBlueprint.AbelGalois
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K L : Type} [Field K] [Field L] [Algebra K L] (C : Over (Spec (.of K)))
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIntegral C.hom]
set_option quotPrecheck false
local notation "Cₗ" => (Over.pullback (specMap K L)).obj C
local notation "η₁" => toSheafify (Scheme.fppfTopology.over (Spec (.of K))) (Unrigidified.zeroCommGrpPresheaf C.hom)
local notation "η₂" => toSheafify (Scheme.fppfTopology.over (Spec (.of L))) (Unrigidified.zeroCommGrpPresheaf (Cₗ).hom)

theorem baseChange_difference (p q : geometricSections L C) :
    let _ : IsProper (Cₗ).hom := inferInstanceAs (IsProper (pullback.snd C.hom (specMap K L)))
    let _ : SmoothOfRelativeDimension 1 (Cₗ).hom := inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd C.hom (specMap K L)))
    let _ : GeometricallyIntegral (Cₗ).hom := inferInstanceAs (GeometricallyIntegral (pullback.snd C.hom (specMap K L)))
    (geometricDifference C p q).toMul ≫ (IntegralPicard.unpointed_baseChangeIso C Cₗ (Iso.refl _)).hom.hom.hom.hom =
      (pointDifference (Cₗ).hom p q).toMul := by
  intro _ _ _
  let t := op (fieldPoint L)
  let iso := (sheafToPresheaf (Scheme.fppfTopology.over (Spec (.of L))) CommGrpCat.{1}).mapIso (scalarClasses (L:=L) C)
  let l := (groupSheafRepresentation L (Cₗ).hom)
  let k := (groupSheafRepresentation K C.hom)
  let r := rawDifference (Cₗ).hom p q
  apply l.homEquiv.injective
  rw [carrier_scalar_class]
  change (iso.inv.app t).hom (k.homEquiv ((equivPoints _).symm ((equivPoints _)
    (k.homEquiv.symm ((η₁).app _ (rawDifference C.hom ((equivPoints C).symm p) ((equivPoints C).symm q))))))) =
    l.homEquiv (l.homEquiv.symm ((η₂).app t r))
  rw [Equiv.symm_apply_apply,Equiv.apply_symm_apply,Equiv.apply_symm_apply,←scalar_raw C p q,
    ←scalarClasses_unit]
  exact ConcreteCategory.congr_hom (iso.hom_inv_id_app t) ((η₂).app t r)

end
end ZInQBlueprint.AbelGalois
#print axioms ZInQBlueprint.AbelGalois.baseChange_difference

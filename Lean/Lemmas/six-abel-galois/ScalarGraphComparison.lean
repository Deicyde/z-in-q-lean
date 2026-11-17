import GeometricPointDifferences
import Nyll.AlgebraicCurves.Geometry.Schemes.BaseChange.HomPullbackKerPowInvModuleIso

/-! The comparison on actual graph line bundles under extension of the base field. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra Opposite
namespace ZInQBlueprint.AbelGalois
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K L : Type} [Field K] [Field L] [Algebra K L] (C : Over (Spec (.of K)))
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIntegral C.hom]
set_option quotPrecheck false
local notation "Cₗ" => (Over.pullback (specMap K L)).obj C

theorem scalar_raw (p q : geometricSections L C) :
    let _ : IsProper (Cₗ).hom := inferInstanceAs (IsProper (pullback.snd C.hom (specMap K L)))
    let _ : SmoothOfRelativeDimension 1 (Cₗ).hom := inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd C.hom (specMap K L)))
    let _ : GeometricallyIntegral (Cₗ).hom := inferInstanceAs (GeometricallyIntegral (pullback.snd C.hom (specMap K L)))
    (Unrigidified.zeroCommGrpBaseChangeIso C.hom L).hom.app (op (fieldPoint L))
      (rawDifference (Cₗ).hom p q) =
       rawDifference C.hom ((equivPoints C).symm p) ((equivPoints C).symm q) := by
  intro _ _ _
  let t := (fieldPoint L).hom
  let f := (BaseChange.κ C.hom L t).inv
  let I (s : geometricSections L C) := (RelEffCartierDiv.ofPoint (Cₗ).hom s.left s.w).I
  let D (s : geometricSections L C) := (RelEffCartierDiv.ofPoint C.hom
    ((equivPoints C).symm s).left ((equivPoints C).symm s).w).I
  have hI (s : geometricSections L C) : (I s).comap f = D s :=
    by
      let u := (equivPoints C).symm s
      have e : graphOver (Cₗ).hom s.left s.w ≫ (BaseChange.κ C.hom L t).hom =
          graphOver C.hom u.left u.w := by
        apply pullback.hom_ext
        · rw [Category.assoc,BaseChange.κ_hom_fst]
          exact (graphOver_fst_assoc (Cₗ).hom s.left s.w (pullback.fst C.hom (specMap K L))).trans
            (graphOver_fst C.hom u.left u.w).symm
        · rw [Category.assoc,BaseChange.κ_hom_snd]
          exact (graphOver_snd (Cₗ).hom s.left s.w).trans (graphOver_snd C.hom u.left u.w).symm
      apply AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso.AlgebraicGeometry.BCKerGlue.ker_comap_eq_ker f
      rw [←e,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  have h (s : geometricSections L C) : (I s).IsInvertible := RelEffCartierDiv.isInvertible_I _
  have h' (s : geometricSections L C) : ((I s).comap f).IsInvertible :=
    (hI s).symm ▸ RelEffCartierDiv.isInvertible_I _
  obtain ⟨pos⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso f (h p) (h' p)
  let := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison f (h q) (h' q)
  apply Subtype.ext
  apply Quot.sound
  apply Unrigidified.baseTwist_of_iso
  exact Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫
    ((pos ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule (hI p))) ⊗ᵢ
      (asIso ((I q).pullbackModuleComparison f) ≪≫ eqToIso (congrArg Scheme.IdealSheafData.module (hI q))))

end
end ZInQBlueprint.AbelGalois
#print axioms ZInQBlueprint.AbelGalois.scalar_raw

import ThetaDivisorMarking

/-! Translations by geometric points are isomorphisms of the underlying scheme over its field. -/
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.SixThetaRestriction
open GeometricMarking NormalDescent QuaternionMarking
noncomputable section
variable {A : AbelianModel.GroupScheme Qbar}

abbrev toBase (T : Over (Spec (.of Qbar))) : T ⟶ basePoint :=
  Over.homMk T.hom (Category.comp_id _)

theorem comp_toBase {S T : Over (Spec (.of Qbar))} (f : S ⟶ T) :
    f ≫ toBase T = toBase S := by
  apply Over.OverMorphism.ext
  exact f.w

def translateHom (t : sections A) : A.X ⟶ A.X := (𝟙 A.X) * (toBase A.X ≫ t.toMul)

theorem comp_translate {T : Over (Spec (.of Qbar))} (p : T ⟶ A.X) (t : sections A) :
    p ≫ translateHom t = p * (toBase T ≫ t.toMul) := by
  rw [translateHom,MonObj.comp_mul,Category.comp_id,←Category.assoc,comp_toBase]

theorem translate_point (p t : sections A) :
    Additive.ofMul (p.toMul ≫ translateHom t) = p+t := by
  rw [comp_translate]
  have id' : toBase basePoint = 𝟙 basePoint := by
    apply Over.OverMorphism.ext
    rfl
  rw [id',Category.id_comp]
  rfl

def translation (t : sections A) : A.X ≅ A.X where
  hom := translateHom t
  inv := translateHom (-t)
  hom_inv_id := by
    rw [comp_translate]
    change ((𝟙 A.X) * (toBase A.X ≫ t.toMul)) * (toBase A.X ≫ t.toMul⁻¹) = 𝟙 A.X
    rw [GrpObj.comp_inv,mul_inv_cancel_right]
  inv_hom_id := by
    rw [comp_translate]
    change ((𝟙 A.X) * (toBase A.X ≫ t.toMul⁻¹)) * (toBase A.X ≫ t.toMul) = 𝟙 A.X
    rw [GrpObj.comp_inv,inv_mul_cancel_right]

/-- Extract the single translate which is the image of the original Abel curve. -/
theorem exists_translate {u : ℚ} {hu : u∉ZInQ.contactSet} (D : DivisorData hu)
    (a : geometricJacobian hu ≅ geometricJacobian hu) (h : preservesTheta D a) :
    ∃ t : JacobianPoints hu,
      (groupAction a) '' Set.range D.abel = Set.range (fun p => D.abel p+t) := by
  have ha : Set.range D.abel ∈ thetaFamily D := by
    refine ⟨0,?_⟩
    simp only [add_zero]
  have hb : onSections a.hom '' Set.range D.abel ∈ imageFamily a.hom (thetaFamily D) :=
    ⟨_,ha,rfl⟩
  rw [show imageFamily a.hom (thetaFamily D) = thetaFamily D from h] at hb
  obtain ⟨t,ht⟩ := hb
  exact ⟨t,ht.symm⟩

end
end ZInQBlueprint.SixThetaRestriction
#print axioms ZInQBlueprint.SixThetaRestriction.translation
#print axioms ZInQBlueprint.SixThetaRestriction.translate_point
#print axioms ZInQBlueprint.SixThetaRestriction.exists_translate

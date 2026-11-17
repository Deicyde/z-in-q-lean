import PolarizationClass

/-! The marked comparison of Baba and Granath is compared with the rational
descent isomorphism on the same polarized Jacobian. The target line bundle
is obtained by transport, so the rational isomorphism preserves its class. -/
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ThetaClass
open QuaternionMarking GeometricMarking AbelianModel NormalDescent
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {u : ℚ} {hu : u ∉ ZInQ.contactSet} {P : GroupScheme Qbar}
local notation "J" => geometricJacobian hu

/-- The equality of inverse images, with translation by t on the right,
implies equality of the complete translate families under the forward map. -/
theorem preserves_of_preimages {A : GroupScheme Qbar} (D : Set (sections A))
    (a : A ≅ A) (t : sections A) (h : ∀ p, onSections a.hom p ∈ D ↔ p+t ∈ D) :
    imageFamily a.hom (translates D) = translates D := by
  let e := SixAbelMap.pointsIso a
  have invImage : e.symm '' D = translate (-t) D := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      have m := (h (e.symm y)).mp (show e (e.symm y) ∈ D by simpa using hy)
      exact ⟨_,m,by simp⟩
    · rintro ⟨y,hy,rfl⟩
      refine ⟨e (y + -t), (h _).mpr ?_,e.symm_apply_apply _⟩
      simpa using hy
  have invFamily : imageFamily a.inv (translates D) = translates D :=
    (imageFamily_translates a.symm D).trans
      ((congrArg translates invImage).trans (translates_translate (-t) D))
  apply image_iso_injective a.symm
  change imageFamily a.inv (imageFamily a.hom (translates D)) = imageFamily a.inv (translates D)
  rw [←image_comp,a.hom_inv_id,image_id,invFamily]

/-- The theta class on the conjugate printed model expressed using rational descent. -/
abbrev conjugateBundle (e : J ≅ P) (σ : Qbar ≃ₐ[ℚ] Qbar) (L : (geometricJacobian hu).X.left.Modules) :=
  pullModule (underlying (e ≪≫ rationalOnPrinted e σ)).inv L

/-- The field-of-moduli comparison respects the labelled real generator and
the transported Néron–Severi class of the specified line bundle. -/
def PrintedClassMarking (e : J ≅ P) (L : (geometricJacobian hu).X.left.Modules) : Prop :=
  ∃ act : LevelThree.O →+* End P, Function.Injective act ∧
    (IsSquare (-(27*SixContact.J u+16)/SixContact.J u) →
    ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∃ φ : P ≅ (conjugation σ.toRingEquiv).mapCommGrp.obj P,
      (act sqrtThree).asHom ≫ φ.hom = φ.hom ≫ (conjugation σ.toRingEquiv).mapCommGrp.map
        (act sqrtThree).asHom ∧
      SameClass (geometricJacobian hu).X.hom L (pullModule (underlying (e ≪≫ φ)).hom (conjugateBundle e σ L)))

theorem correction_sameClass (e : J ≅ P) (σ : Qbar ≃ₐ[ℚ] Qbar)
    (φ : P ≅ (conjugation σ.toRingEquiv).mapCommGrp.obj P) (L : (geometricJacobian hu).X.left.Modules)
    (h : SameClass (geometricJacobian hu).X.hom L (pullModule (underlying (e ≪≫ φ)).hom (conjugateBundle e σ L))) :
    SameClass (geometricJacobian hu).X.hom L (pullModule (underlying (correctionIso e σ φ)).hom L) := by
  let f := underlying (e ≪≫ φ)
  let g := underlying (e ≪≫ rationalOnPrinted e σ)
  have c := sameClass_pull_comparison f g L (conjugateBundle e σ L) h (sameClass_transport g L)
  have eq : ((f ≪≫ g.symm).hom).left = (underlying (correctionIso e σ φ)).hom.left := by
    simp [f,g,underlying,correctionIso]
  exact c.congr (Iso.refl _) ((Scheme.Modules.pullbackCongr eq).app L)

theorem comparison_of_corrected (D : DivisorData hu) (e : J ≅ P) (σ : Qbar ≃ₐ[ℚ] Qbar)
    (φ : P ≅ (conjugation σ.toRingEquiv).mapCommGrp.obj P)
    (hp : preservesTheta D (correctionIso e σ φ)) :
    imageFamily φ.hom (imageFamily e.hom (thetaFamily D)) =
      imageFamily (rationalOnPrinted e σ).hom (imageFamily e.hom (thetaFamily D)) := by
  let a := correctionIso e σ φ
  let g := rationalOnPrinted e σ
  have eq : e.hom ≫ φ.hom = a.hom ≫ e.hom ≫ g.hom := by simp [a,g,correctionIso,Category.assoc]
  rw [←image_comp,eq,image_comp,image_comp]
  exact congrArg (fun T => imageFamily g.hom (imageFamily e.hom T)) hp

end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.preserves_of_preimages
#print axioms ZInQBlueprint.ThetaClass.correction_sameClass
#print axioms ZInQBlueprint.ThetaClass.comparison_of_corrected

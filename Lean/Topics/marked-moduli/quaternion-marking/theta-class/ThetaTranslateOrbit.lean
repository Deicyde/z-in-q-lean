import ThetaTranslation
import SignedPoincare

/-! An isomorphism carries all translates of an Abel curve to all translates
of its image. It suffices to compare one divisor from each family. -/
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ThetaClass
open QuaternionMarking GeometricMarking AbelianModel NormalDescent
noncomputable section

def translate {G : Type*} [AddCommGroup G] (t : G) (D : Set G) : Set G :=
  (fun x => x + t) '' D

def translates {G : Type*} [AddCommGroup G] (D : Set G) : Set (Set G) :=
  Set.range (fun t => translate t D)

theorem translate_translate {G : Type*} [AddCommGroup G] (s t : G) (D : Set G) :
    translate t (translate s D) = translate (s+t) D := by
  simp only [translate,Set.image_image,add_assoc]

theorem translates_translate {G : Type*} [AddCommGroup G] (s : G) (D : Set G) :
    translates (translate s D) = translates D := by
  ext E
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨s+t,(translate_translate s t D).symm⟩
  · rintro ⟨t,rfl⟩
    refine ⟨t-s,?_⟩
    change translate (t-s) (translate s D) = translate t D
    rw [translate_translate,show s + (t-s) = t by abel]

theorem translates_eq_iff {G : Type*} [AddCommGroup G] (D E : Set G) :
    translates D = translates E ↔ ∃ t, D = translate t E := by
  constructor
  · intro h
    have m : D ∈ translates D := ⟨0,by simp [translate]⟩
    rw [h] at m
    obtain ⟨t,ht⟩ := m
    exact ⟨t,ht.symm⟩
  · rintro ⟨t,rfl⟩
    exact translates_translate t E

theorem image_translate {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (t : G) (D : Set G) :
    e '' translate t D = translate (e t) (e '' D) := by
  simp only [translate,Set.image_image,map_add]

theorem image_translates {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (D : Set G) :
    Set.image (Set.image e) (translates D) = translates (e '' D) := by
  ext E
  constructor
  · rintro ⟨_,⟨t,rfl⟩,rfl⟩
    exact ⟨e t,(image_translate e t D).symm⟩
  · rintro ⟨t,rfl⟩
    exact ⟨_,⟨e.symm t,rfl⟩,by rw [image_translate,e.apply_symm_apply]⟩

theorem imageFamily_translates {A B : GroupScheme Qbar} (e : A ≅ B) (D : Set (sections A)) :
    imageFamily e.hom (translates D) = translates ((onSections e.hom) '' D) :=
  image_translates (SixAbelMap.pointsIso e) D

variable {u : ℚ} {hu : u ∉ ZInQ.contactSet}
local notation "J" => geometricJacobian hu

theorem abel_translates (D : DivisorData hu) :
    thetaFamily D = translates (Set.range D.abel) := by
  unfold thetaFamily translates translate
  congr 1
  funext t
  ext x
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨_,⟨p,rfl⟩,rfl⟩
  · rintro ⟨_,⟨p,rfl⟩,rfl⟩
    exact ⟨p,rfl⟩

/-- This iff compares the two actual morphisms whose quotient acts on the rational model. -/
theorem printed_comparison_iff {P T : GroupScheme Qbar} (e : J ≅ P) (f g : P ≅ T)
    (D : DivisorData hu) :
    imageFamily f.hom (imageFamily e.hom (thetaFamily D)) =
      imageFamily g.hom (imageFamily e.hom (thetaFamily D)) ↔
    ∃ t, onSections (e ≪≫ f).hom '' Set.range D.abel =
      translate t (onSections (e ≪≫ g).hom '' Set.range D.abel) := by
  rw [← image_comp,← image_comp,abel_translates]
  change imageFamily (e ≪≫ f).hom _ = imageFamily (e ≪≫ g).hom _ ↔ _
  rw [imageFamily_translates,imageFamily_translates,translates_eq_iff]

end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.translates_eq_iff
#print axioms ZInQBlueprint.ThetaClass.image_translates
#print axioms ZInQBlueprint.ThetaClass.abel_translates
#print axioms ZInQBlueprint.ThetaClass.printed_comparison_iff

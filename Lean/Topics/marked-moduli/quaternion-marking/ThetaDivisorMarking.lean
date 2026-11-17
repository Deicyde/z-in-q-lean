import PolarizedOrder

/-! In genus two the translates of the Abel image represent the canonical
theta divisor class. With this point description, comparing two polarized
isomorphisms and cancelling their common target is a calculation with sets. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.QuaternionMarking
open AbelianModel NormalDescent GeometricMarking
open scoped NormalDescent CategoryTheory.MonObj
noncomputable section

abbrev sections (A : GroupScheme Qbar) := Additive (basePoint ⟶ A.X)

def onSections {A B : GroupScheme Qbar} (f : A ⟶ B) (p : sections A) : sections B :=
  Additive.ofMul (p.toMul ≫ f.hom.hom.hom)

def imageFamily {A B : GroupScheme Qbar} (f : A ⟶ B) (T : Set (Set (sections A))) :
    Set (Set (sections B)) := Set.image (Set.image (onSections f)) T

theorem image_id (A : GroupScheme Qbar) (T : Set (Set (sections A))) : imageFamily (𝟙 A) T = T := by
  have id (p : sections A) : onSections (𝟙 A) p = p := by
    change Additive.ofMul (p.toMul ≫ 𝟙 _) = p
    rw [Category.comp_id]
    rfl
  simp [imageFamily,funext id]

theorem image_comp {A B C : GroupScheme Qbar} (f : A ⟶ B) (g : B ⟶ C) (T : Set (Set (sections A))) :
    imageFamily (f ≫ g) T = imageFamily g (imageFamily f T) := by
  have comp (p : sections A) : onSections (f ≫ g) p = onSections g (onSections f p) := by
    change Additive.ofMul (p.toMul ≫ f.hom.hom.hom ≫ g.hom.hom.hom) = Additive.ofMul ((p.toMul ≫ f.hom.hom.hom) ≫ g.hom.hom.hom)
    rw [Category.assoc]
  apply Set.ext
  intro t
  simp only [imageFamily, Set.mem_image]
  constructor
  · rintro ⟨s,hs,rfl⟩
    exact ⟨_,⟨s,hs,rfl⟩,by rw [Set.image_image]; congr 1⟩
  · rintro ⟨_,⟨s,hs,rfl⟩,rfl⟩
    exact ⟨s,hs,by rw [Set.image_image]; congr 1⟩

theorem image_iso_injective {A B : GroupScheme Qbar} (g : A ≅ B) :
    Function.Injective (imageFamily g.hom) := by
  intro T U h
  have H := congrArg (imageFamily g.inv) h
  simpa only [← image_comp,g.hom_inv_id,image_id] using H

variable {u : ℚ} {hu : u ∉ ZInQ.contactSet}
local notation "J" => geometricJacobian hu
local notation "A" => SixJacobian.jacobian hu

/-- The complete family of translates of a single Abel curve. The family
is independent of the choice of Abel base point. -/
def thetaFamily (D : DivisorData hu) : Set (Set (sections J)) :=
  Set.range (fun t : sections J => Set.range (fun p => D.abel p + t))

def preservesTheta (D : DivisorData hu) (a : J ≅ J) : Prop :=
  imageFamily a.hom (thetaFamily D) = thetaFamily D

variable {P : GroupScheme Qbar}

theorem corrected_preserves (D : DivisorData hu) (e : J ≅ P) (σ : Qbar ≃ₐ[ℚ] Qbar)
    (φ : P ≅ (conjugation σ.toRingEquiv).mapCommGrp.obj P)
    (polarized : let T := imageFamily e.hom (thetaFamily D)
      imageFamily φ.hom T = imageFamily (rationalOnPrinted e σ).hom T) :
    preservesTheta D (correctionIso e σ φ) := by
  apply image_iso_injective e
  change imageFamily e.hom (imageFamily (correctionIso e σ φ).hom (thetaFamily D)) = _
  rw [← image_comp]
  apply image_iso_injective (rationalOnPrinted e σ)
  simp only [← image_comp] at polarized ⊢
  simpa [correctionIso, Category.assoc] using polarized

/-- The two facts supplied by the marked Shimura-curve theorem are a faithful
quaternion action and a polarized isomorphism to each conjugate which
commutes with the indicated generator. The target theta class is specified
using the rational polarization. -/
def PrintedMarking (D : DivisorData hu) (e : J ≅ P) : Prop :=
  ∃ act : LevelThree.O →+* End P, Function.Injective act ∧
    (IsSquare (-(27*SixContact.J u+16)/SixContact.J u) →
    ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∃ φ : P ≅ (conjugation σ.toRingEquiv).mapCommGrp.obj P,
      (act sqrtThree).asHom ≫ φ.hom = φ.hom ≫ (conjugation σ.toRingEquiv).mapCommGrp.map (act sqrtThree).asHom ∧
      imageFamily φ.hom (imageFamily e.hom (thetaFamily D)) =
        imageFamily (rationalOnPrinted e σ).hom (imageFamily e.hom (thetaFamily D)))

theorem marked_of_theta (D : DivisorData hu) (e : J ≅ P)
    (T : PolarizedTorelli D (preservesTheta D)) (M : PrintedMarking D e) :
    Nonempty (JacobianHeight.MarkedAction u A) := by
  obtain ⟨act,hact,m⟩ := M
  refine ⟨marked_of_printed D _ T e act hact ?_⟩
  intro square σ
  obtain ⟨φ,hφ,hT⟩ := m square σ
  exact ⟨φ,hφ,corrected_preserves D e σ φ hT⟩

end
end ZInQBlueprint.QuaternionMarking
#print axioms ZInQBlueprint.QuaternionMarking.image_comp
#print axioms ZInQBlueprint.QuaternionMarking.corrected_preserves
#print axioms ZInQBlueprint.QuaternionMarking.marked_of_theta

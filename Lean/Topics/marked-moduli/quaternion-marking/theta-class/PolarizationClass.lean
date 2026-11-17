import ThetaTranslateOrbit

/-! Algebraic equivalence of invertible sheaves on the geometric Jacobian.
The relation is expressed using an invertible family over a connected parameter
scheme via NYLL's Picard functor. Isomorphisms pull it back contravariantly. -/
open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
namespace ZInQBlueprint.ThetaClass
open QuaternionMarking GeometricMarking AbelianModel NormalDescent SixThetaRestriction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The two invertible sheaves represent the same Néron–Severi class. The
algebraically trivial factor is an actual sheaf on the same scheme. -/
def SameClass {k : Type} [Field k] {X : Scheme} (c : X ⟶ Spec (.of k))
    (L M : X.Modules) : Prop :=
  ∃ N : X.Modules, N.IsInvertible ∧ RelPicard.IsAlgEquivZero c N ∧ Nonempty (L ⊗ N ≅ M)

namespace SameClass

theorem refl {k : Type} [Field k] {X : Scheme} (c : X ⟶ Spec (.of k)) (L : X.Modules) :
    SameClass c L L := by
  let S := Spec (.of k)
  have hu : RelPicard.IsAlgEquivZero c (𝟙_ X.Modules) := by
    refine ⟨S,𝟙 _,inferInstance,RelPicard.geometricallyIntegral_id_Spec k,
      𝟙_ (Limits.pullback c (𝟙 S)).Modules,Scheme.Modules.isInvertible_unit _,
      ⟨𝟙 _,Category.comp_id _⟩,⟨𝟙 _,Category.comp_id _⟩,⟨Scheme.Modules.pullbackUnitIso _⟩,⟨?_⟩⟩
    exact Scheme.Modules.pullbackUnitIso _ ≪≫ (Scheme.Modules.pullbackUnitIso _).symm
  exact ⟨_,Scheme.Modules.isInvertible_unit _,hu,⟨ρ_ L⟩⟩

theorem congr {k : Type} [Field k] {X : Scheme} {c : X ⟶ Spec (.of k)} {L L' M M' : X.Modules}
    (h : SameClass c L M) (l : L ≅ L') (m : M ≅ M') : SameClass c L' M' := by
  obtain ⟨N,hN,h0,⟨e⟩⟩ := h
  exact ⟨N,hN,h0,⟨whiskerRightIso l.symm N ≪≫ e ≪≫ m⟩⟩

theorem symm {k : Type} [Field k] {X : Scheme} {c : X ⟶ Spec (.of k)} {L M : X.Modules}
    (h : SameClass c L M) : SameClass c M L := by
  obtain ⟨N,hN,h0,⟨e⟩⟩ := h
  obtain ⟨V,hV,⟨v⟩⟩ := hN.exists_tensor_inverse
  exact ⟨V,hV,h0.of_tensor_iso_unit v,
    ⟨whiskerRightIso e.symm V ≪≫ (α_ L N V) ≪≫ whiskerLeftIso L v ≪≫ (ρ_ L)⟩⟩

theorem trans {k : Type} [Field k] {X : Scheme} {c : X ⟶ Spec (.of k)} {L M P : X.Modules}
    (h : SameClass c L M) (g : SameClass c M P) : SameClass c L P := by
  obtain ⟨N,hN,h0,⟨e⟩⟩ := h
  obtain ⟨V,hV,v0,⟨v⟩⟩ := g
  exact ⟨N ⊗ V,hN.tensor hV,h0.tensor v0,
    ⟨(α_ L N V).symm ≪≫ whiskerRightIso e V ≪≫ v⟩⟩

theorem pull {k : Type} [Field k] {X Y : Scheme} {c : X ⟶ Spec (.of k)}
    {d : Y ⟶ Spec (.of k)} {L M : X.Modules} (h : SameClass c L M) (f : Y ⟶ X)
    (hf : f ≫ c = d) : SameClass d ((Scheme.Modules.pullback f).obj L)
      ((Scheme.Modules.pullback f).obj M) := by
  obtain ⟨N,hN,h0,⟨e⟩⟩ := h
  exact ⟨_,hN.pullback f,h0.pullback f hf,
    ⟨(Scheme.Modules.pullbackTensorObjIso f L N).symm ≪≫ (Scheme.Modules.pullback f).mapIso e⟩⟩

end SameClass

abbrev curveBase := Spec (.of Qbar)
abbrev underlying {A B : GroupScheme Qbar} (f : A ≅ B) := (CommGrp.forget _).mapIso f
abbrev schemeIso {X Y : Over curveBase} (f : X ≅ Y) := (Over.forget _).mapIso f
abbrev pullModule {X Y : Over curveBase} (f : X ⟶ Y) (L : Y.left.Modules) :=
  (Scheme.Modules.pullback f.left).obj L

private def pullComp {X Y Z : Over curveBase} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.left.Modules) :
    pullModule f (pullModule g L) ≅ pullModule (f ≫ g) L :=
  (Scheme.Modules.pullbackComp f.left g.left).app L

private def pullCongr {X Y : Over curveBase} {f g : X ⟶ Y} (h : f = g) (L : Y.left.Modules) :
    pullModule f L ≅ pullModule g L :=
  (Scheme.Modules.pullbackCongr (congrArg (fun m : X ⟶ Y => m.left) h)).app L

/-- Transport of a line bundle back along the same isomorphism gives its original class. -/
theorem sameClass_transport {X Y : Over curveBase} (g : X ≅ Y) (L : X.left.Modules) :
    SameClass X.hom L (pullModule g.hom (pullModule g.inv L)) := by
  let back := pullComp g.hom g.inv L ≪≫ pullCongr g.hom_inv_id L ≪≫
    (Scheme.Modules.pullbackId X.left).app L
  exact (SameClass.refl X.hom L).congr (Iso.refl _) back.symm

theorem sameClass_pull_comparison {X Y : Over curveBase} (f g : X ≅ Y)
    (L : X.left.Modules) (M : Y.left.Modules)
    (hf : SameClass X.hom L (pullModule f.hom M)) (hg : SameClass X.hom L (pullModule g.hom M)) :
    SameClass X.hom L (pullModule (f ≪≫ g.symm).hom L) := by
  let a := f ≪≫ g.symm
  have h := hg.symm.pull a.hom.left a.hom.w
  let back : pullModule a.hom (pullModule g.hom M) ≅ pullModule f.hom M :=
    pullComp a.hom g.hom M ≪≫ pullCongr (show a.hom ≫ g.hom = f.hom by simp [a]) M
  exact hf.trans (h.congr back (Iso.refl _))

/-- The surjectivity part of principal autoduality: all algebraically
trivial twists of this line bundle come from translation. -/
def PrincipalTranslations {A : GroupScheme Qbar} (L : A.X.left.Modules) : Prop :=
  ∀ N : A.X.left.Modules, N.IsInvertible → RelPicard.IsAlgEquivZero A.X.hom N →
    ∃ t : sections A, Nonempty (L ⊗ N ≅ pullModule (translation t).hom L)

theorem translate_of_sameClass {A : GroupScheme Qbar} {L M : A.X.left.Modules}
    (h : PrincipalTranslations (A:=A) L) (c : SameClass A.X.hom L M) :
    ∃ t : sections A, Nonempty (M ≅ pullModule (translation t).hom L) := by
  obtain ⟨N,hN,h0,⟨e⟩⟩ := c
  obtain ⟨t,⟨v⟩⟩ := h N hN h0
  exact ⟨t,⟨e.symm ≪≫ v⟩⟩

end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.SameClass.refl
#print axioms ZInQBlueprint.ThetaClass.SameClass.symm
#print axioms ZInQBlueprint.ThetaClass.SameClass.trans
#print axioms ZInQBlueprint.ThetaClass.SameClass.pull
#print axioms ZInQBlueprint.ThetaClass.sameClass_transport
#print axioms ZInQBlueprint.ThetaClass.sameClass_pull_comparison
#print axioms ZInQBlueprint.ThetaClass.translate_of_sameClass

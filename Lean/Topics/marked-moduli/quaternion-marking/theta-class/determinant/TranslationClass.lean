import PolarizationClass

/-! Two fibres of an invertible sheaf over a geometrically integral parameter
are algebraically equivalent. Applying this family criterion to addition gives
algebraic equivalence of translations along an Abel curve. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RelPicard NeronModelInfra
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ThetaClass
open GeometricMarking AbelianModel NormalDescent SixThetaRestriction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Divide the family by its first fibre. The resulting family connects the
unit to the quotient of the two line bundles. -/
theorem SameClass.of_family {k : Type} [Field k] {X T : Scheme}
    (c : X ⟶ Spec (.of k)) (d : T ⟶ Spec (.of k)) [LocallyOfFiniteType d] [GeometricallyIntegral d]
    {L M : X.Modules} (hL : L.IsInvertible) (hM : M.IsInvertible)
    (F : (pullback c d).Modules) (hF : F.IsInvertible)
    (p q : SchemeHomOver (𝟙 (Spec (.of k))) d)
    (first : (Scheme.Modules.pullback (baseChangeSnd c p)).obj F ≅
      (Scheme.Modules.pullback (pullback.fst c (𝟙 _))).obj L)
    (last : (Scheme.Modules.pullback (baseChangeSnd c q)).obj F ≅
      (Scheme.Modules.pullback (pullback.fst c (𝟙 _))).obj M) : SameClass c L M := by
  obtain ⟨V,hV,⟨inv⟩⟩ := hL.exists_tensor_inverse
  let π := pullback.fst c (𝟙 (Spec (.of k)))
  let pr := pullback.fst c d
  let G := (Scheme.Modules.pullback pr).obj V
  let constant (s : SchemeHomOver (𝟙 (Spec (.of k))) d) :
      (Scheme.Modules.pullback (baseChangeSnd c s)).obj G ≅ (Scheme.Modules.pullback π).obj V :=
    (Scheme.Modules.pullbackComp _ pr).app V ≪≫
      (Scheme.Modules.pullbackCongr (show baseChangeSnd c s ≫ pr = π by
        simp [baseChangeSnd,pr,π])).app V
  refine ⟨V ⊗ M,hV.tensor hM,?_,⟨(α_ L V M).symm ≪≫ whiskerRightIso inv M ≪≫ λ_ M⟩⟩
  refine ⟨T,d,inferInstance,inferInstance,G ⊗ F,(hV.pullback pr).tensor hF,p,q,⟨?_⟩,⟨?_⟩⟩
  · exact Scheme.Modules.pullbackTensorObjIso _ G F ≪≫ (constant p ⊗ᵢ first) ≪≫
      (Scheme.Modules.pullbackTensorObjIso π V L).symm ≪≫
      (Scheme.Modules.pullback π).mapIso ((β_ V L) ≪≫ inv) ≪≫ Scheme.Modules.pullbackUnitIso π
  · exact Scheme.Modules.pullbackTensorObjIso _ G F ≪≫ (constant q ⊗ᵢ last) ≪≫
      (Scheme.Modules.pullbackTensorObjIso π V M).symm

variable {A : GroupScheme Qbar}

/-- Points on the same integral parameter scheme give algebraically equivalent
translates, for every morphism of that scheme to the group. -/
theorem sameClass_translations_in_family {T : Over curveBase}
    [LocallyOfFiniteType T.hom] [GeometricallyIntegral T.hom] (f : T ⟶ A.X)
    (p q : basePoint ⟶ T) (L : A.X.left.Modules) (hL : L.IsInvertible) :
    SameClass A.X.hom (pullModule (translateHom (Additive.ofMul (p ≫ f))) L)
      (pullModule (translateHom (Additive.ofMul (q ≫ f))) L) := by
  let c := A.X.hom
  let d := T.hom
  let B : Over curveBase := Over.mk (pullback.fst c d ≫ c)
  let fst : B ⟶ A.X := Over.homMk (pullback.fst c d) rfl
  let snd : B ⟶ T := Over.homMk (pullback.snd c d) pullback.condition.symm
  let add : B ⟶ A.X := fst * (snd ≫ f)
  let U : Over curveBase := Over.mk (pullback.fst c (𝟙 curveBase) ≫ c)
  let π : U ⟶ A.X := Over.homMk (pullback.fst c (𝟙 curveBase)) rfl
  let point (s : basePoint ⟶ T) : SchemeHomOver (𝟙 curveBase) d := ⟨s.left,s.w⟩
  let graph (s : basePoint ⟶ T) : U ⟶ B := Over.homMk (baseChangeSnd c (point s))
    (by change _ ≫ pullback.fst c d ≫ c = pullback.fst c (𝟙 _) ≫ c
        simp [baseChangeSnd])
  have fibre (s : basePoint ⟶ T) :
      graph s ≫ add = π ≫ translateHom (Additive.ofMul (s ≫ f)) := by
    rw [comp_translate]
    change graph s ≫ (fst * (snd ≫ f)) = π * (toBase U ≫ s ≫ f)
    rw [MonObj.comp_mul,←Category.assoc (graph s) snd f,←Category.assoc (toBase U) s f]
    have e₁ : graph s ≫ fst = π := by
      apply Over.OverMorphism.ext
      change baseChangeSnd c (point s) ≫ pullback.fst c d = _
      simp [baseChangeSnd,π]
    have e₂ : graph s ≫ snd = toBase U ≫ s := by
      apply Over.OverMorphism.ext
      change baseChangeSnd c (point s) ≫ pullback.snd c d = (pullback.fst c (𝟙 _) ≫ c) ≫ s.left
      simp only [baseChangeSnd,pullback.lift_snd,point]
      rw [pullback.condition,Category.comp_id]
    rw [e₁,e₂]
  let F := (Scheme.Modules.pullback add.left).obj L
  let restrict (s : basePoint ⟶ T) :
      (Scheme.Modules.pullback (baseChangeSnd c (point s))).obj F ≅
      (Scheme.Modules.pullback π.left).obj (pullModule (translateHom (Additive.ofMul (s ≫ f))) L) :=
    (Scheme.Modules.pullbackComp (graph s).left add.left).app L ≪≫
    (Scheme.Modules.pullbackCongr (congrArg (fun g : U ⟶ A.X => g.left) (fibre s))).app L ≪≫
    ((Scheme.Modules.pullbackComp π.left _).app L).symm
  exact SameClass.of_family c d (hL.pullback _) (hL.pullback _) F (hL.pullback add.left)
    (point p) (point q) (restrict p) (restrict q)

end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.SameClass.of_family
#print axioms ZInQBlueprint.ThetaClass.sameClass_translations_in_family

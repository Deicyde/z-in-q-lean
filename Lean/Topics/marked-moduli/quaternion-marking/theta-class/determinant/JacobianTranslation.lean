import TranslationClass
import SignedThetaEndpoint

/-! On a smooth geometrically connected group over a field every translation
preserves the algebraic-equivalence class of every invertible sheaf. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ThetaClass
open QuaternionMarking GeometricMarking AbelianModel NormalDescent SixThetaRestriction CanonicalTheta
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- After each field extension the smooth fibre is locally noetherian with
regular local rings. Connectedness then makes the fibre integral. -/
theorem geometricallyIntegral_of_smooth_connected {k : Type} [Field k] {X : Scheme}
    (c : X ⟶ Spec (.of k)) [Smooth c] [GeometricallyConnected c] : GeometricallyIntegral c := by
  constructor
  intro K hK y Z fst snd square
  let : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) square inferInstance
  let : GeometricallyConnected snd :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) square inferInstance
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian snd
  let : ConnectedSpace Z := GeometricallyConnected.connectedSpace_of_subsingleton snd
  exact isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk Z fun x => by
    let := Smooth.isRegularLocalRing_stalk (f := snd) x
    exact IsRegularLocalRing.isDomain _

private theorem translate_zero {A : GroupScheme Qbar} : translateHom (0 : sections A) = 𝟙 A.X := by
  change (𝟙 A.X) * (toBase A.X ≫ (1 : basePoint ⟶ A.X)) = _
  rw [MonObj.comp_one,mul_one]

/-- The universal addition family interpolates the original sheaf and its pullback
along translation by any geometric point. -/
theorem sameClass_translation {A : GroupScheme Qbar} (ab : IsAbelianScheme A)
    (L : A.X.left.Modules) (hL : L.IsInvertible) (t : sections A) :
    SameClass A.X.hom L (pullModule (translation t).hom L) := by
  let := ab.smooth
  let := ab.geometricallyConnected
  let := geometricallyIntegral_of_smooth_connected A.X.hom
  have h := sameClass_translations_in_family (𝟙 A.X) (0 : sections A).toMul t.toMul L hL
  simp only [Category.comp_id] at h
  let e : pullModule (translateHom (0 : sections A)) L ≅ L :=
    (Scheme.Modules.pullbackCongr (congrArg (fun f : A.X ⟶ A.X => f.left) translate_zero)).app L ≪≫
      (Scheme.Modules.pullbackId A.X.left).app L
  exact h.congr e (Iso.refl _)

theorem signedTheta_translate {u : ℚ} (hu : u ∉ ZInQ.contactSet) (t : JacobianPoints hu) :
    SameClass (geometricJacobian hu).X.hom (signedThetaLine hu)
      (pullModule (translation t).hom (signedThetaLine hu)) :=
  sameClass_translation (isAbelianScheme_baseChange (algebraMap ℚ Qbar) (SixJacobian.isAbelian hu))
    _ (signedThetaLine_invertible hu) t

/-- Galois invariance of the class follows from a translate comparison of
the actual determinant under each semilinear deck map. -/
theorem rational_of_deck_translations {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (h : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∃ t : JacobianPoints hu,
      Nonempty (pullModule (translation t).hom (signedThetaLine hu) ≅
        (Scheme.Modules.pullback (deck (SixJacobian.jacobian hu).X.hom σ)).obj (signedThetaLine hu))) :
    RationalThetaClass (hu := hu) (signedThetaLine hu) := by
  intro σ
  obtain ⟨t,⟨e⟩⟩ := h σ
  exact (signedTheta_translate hu t).congr (Iso.refl _) e

end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.geometricallyIntegral_of_smooth_connected
#print axioms ZInQBlueprint.ThetaClass.sameClass_translation
#print axioms ZInQBlueprint.ThetaClass.signedTheta_translate
#print axioms ZInQBlueprint.ThetaClass.rational_of_deck_translations

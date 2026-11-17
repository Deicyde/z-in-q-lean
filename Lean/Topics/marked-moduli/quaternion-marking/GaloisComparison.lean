import MarkedTransport

/-! The rational descent isomorphism to the Galois-conjugate group scheme.
Its first projection is exactly the semilinear deck map used by descent. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace ZInQBlueprint.QuaternionMarking
open AbelianModel NormalDescent
open scoped NormalDescent
noncomputable section
variable {K L : Type} [Field K] [Field L] [Algebra K L]
private abbrev S (σ : L ≃ₐ[K] L) := Spec.map (CommRingCat.ofHom σ.toRingHom)
local notation "F" => Over.pullback (specExtension K L)
private abbrev G (σ : L ≃ₐ[K] L) := Over.pullback (S σ)

private theorem deck_inverse (X : Over (Spec (.of K))) (σ : L ≃ₐ[K] L) :
    deck X.hom σ ≫ deck X.hom σ.symm = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc,deck_snd,deck_snd_assoc,Category.id_comp,← Spec.map_comp]
    have id : CommRingCat.ofHom σ.symm.toRingHom ≫ CommRingCat.ofHom σ.toRingHom = 𝟙 _ := by
      ext x
      exact σ.apply_symm_apply x
    rw [id, Spec.map_id, Category.comp_id]

private def component (X : Over (Spec (.of K))) (σ : L ≃ₐ[K] L) :
    (F).obj X ≅ (G σ).obj ((F).obj X) := by
  let A := (F).obj X
  let f : A.left ⟶ pullback A.hom (S σ) := pullback.lift (deck X.hom σ) A.hom (deck_snd X.hom σ)
  let : IsIso (deck X.hom σ) := ⟨deck X.hom σ.symm, deck_inverse X σ, deck_inverse X σ.symm⟩
  let : IsIso (S σ) := inferInstanceAs (IsIso ((Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op).hom))
  let : IsIso f := IsIso.of_isIso_fac_right (show f ≫ pullback.fst A.hom (S σ) = deck X.hom σ from pullback.lift_fst ..)
  exact Over.isoMk (asIso f) (pullback.lift_snd ..)

private theorem component_fst (X : Over (Spec (.of K))) (σ : L ≃ₐ[K] L) :
    (component X σ).hom.left ≫ pullback.fst _ _ = deck X.hom σ := pullback.lift_fst ..

private theorem component_snd (X : Over (Spec (.of K))) (σ : L ≃ₐ[K] L) :
    (component X σ).hom.left ≫ pullback.snd _ _ = ((F).obj X).hom := pullback.lift_snd ..

private theorem deck_naturality {X Y : Over (Spec (.of K))} (f : X ⟶ Y) (σ : L ≃ₐ[K] L) :
    ((F).map f).left ≫ deck Y.hom σ = deck X.hom σ ≫ ((F).map f).left := by
  apply pullback.hom_ext
  · simp [Over.pullback_map_left]
  · simp [Over.pullback_map_left]

private def rationalComparison (σ : L ≃ₐ[K] L) : F ≅ F ⋙ G σ :=
  NatIso.ofComponents (fun X => component X σ) fun {X Y} f => by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (((F).map f).left ≫ (component Y σ).hom.left) ≫ _ = ((component X σ).hom.left ≫ ((G σ).map ((F).map f)).left) ≫ _
      simp only [Category.assoc, component_fst, G, Over.pullback_map_left, pullback.lift_fst, ← Category.assoc (component X σ).hom.left, component_fst]
      exact deck_naturality f σ
    · change (((F).map f).left ≫ (component Y σ).hom.left) ≫ _ = ((component X σ).hom.left ≫ ((G σ).map ((F).map f)).left) ≫ _
      simp only [Category.assoc,component_snd, G, Over.pullback_map_left, pullback.lift_snd]
      exact ((F).map f).w

def rationalGroupComparison (A : GroupScheme K) (σ : L ≃ₐ[K] L) :
    (F).mapCommGrp.obj A ≅ (G σ).mapCommGrp.obj ((F).mapCommGrp.obj A) :=
  (Functor.mapCommGrpNatIso (rationalComparison σ)).app A ≪≫ Functor.mapCommGrpCompIso.app A

theorem comparison_fst (A : GroupScheme K) (σ : L ≃ₐ[K] L) :
    (rationalGroupComparison A σ).hom.hom.hom.hom.left ≫ pullback.fst _ _ = deck A.X.hom σ := by
  change ((component A.X σ).hom.left ≫ 𝟙 _) ≫ _ = _
  rw [Category.comp_id]
  exact pullback.lift_fst ..

end
end ZInQBlueprint.QuaternionMarking
#print axioms ZInQBlueprint.QuaternionMarking.rationalGroupComparison
#print axioms ZInQBlueprint.QuaternionMarking.comparison_fst

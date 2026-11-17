import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.FieldTheory.Normal.Basic

/-! Descent of an invariant morphism along a normal extension of fields. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQBlueprint.NormalDescent

universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The structural projection on spectra for the given field extension. -/
noncomputable abbrev specExtension (K L : Type u) [Field K] [Field L] [Algebra K L] :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

/-- The two embeddings of a normal extension into a common point's residue field
over the same base embedding differ by an automorphism of the extension. -/
theorem conjugate_field_maps [Normal K L] {M : Type u} [Field M] (a b : L →+* M)
    (hab : a.comp (algebraMap K L) = b.comp (algebraMap K L)) :
    ∃ σ : L ≃ₐ[K] L, a.comp σ.toRingHom = b := by
  let : Algebra L M := a.toAlgebra
  let : Algebra K M := (a.comp (algebraMap K L)).toAlgebra
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let b' : L →ₐ[K] M := ⟨b, fun k => (DFunLike.congr_fun hab k).symm⟩
  let e := Normal.algHomEquivAut K M L
  refine ⟨e b', ?_⟩
  exact congrArg AlgHom.toRingHom (e.symm_apply_apply b')

/-- Geometric-point version of normality in the category of schemes. -/
theorem conjugate_spec_maps [Normal K L] {M : Type u} [Field M]
    (a b : Spec (.of M) ⟶ Spec (.of L))
    (hab : a ≫ specExtension K L = b ≫ specExtension K L) :
    ∃ σ : L ≃ₐ[K] L, a ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) = b := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  simp only [specExtension, ← Spec.map_comp, Spec.map_inj] at hab
  obtain ⟨σ, hσ⟩ := conjugate_field_maps (K := K) (L := L) (M := M) a.hom b.hom (congrArg CommRingCat.Hom.hom hab)
  refine ⟨σ, ?_⟩
  rw [← Spec.map_comp, Spec.map_inj]
  exact CommRingCat.hom_ext hσ

variable {X Y : Scheme.{u}} (s : X ⟶ Spec (.of K))

/-- The semilinear map on the scalar extension of a rational scheme. -/
noncomputable def deck (σ : L ≃ₐ[K] L) :
    pullback s (specExtension K L) ⟶ pullback s (specExtension K L) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
      rw [Category.assoc, ← Spec.map_comp]
      have h : (CommRingCat.ofHom (algebraMap K L)) ≫ CommRingCat.ofHom σ.toRingHom =
          CommRingCat.ofHom (algebraMap K L) := CommRingCat.hom_ext σ.toAlgHom.comp_algebraMap
      rw [h]
      exact pullback.condition)

@[reassoc (attr := simp)] theorem deck_fst (σ : L ≃ₐ[K] L) :
    deck s σ ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst ..

@[reassoc (attr := simp)] theorem deck_snd (σ : L ≃ₐ[K] L) :
    deck s σ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := pullback.lift_snd ..

theorem conjugate_points [Normal K L] {M : Type u} [Field M]
    (a b : Spec (.of M) ⟶ pullback s (specExtension K L))
    (hab : a ≫ pullback.fst _ _ = b ≫ pullback.fst _ _) :
    ∃ σ : L ≃ₐ[K] L, a ≫ deck s σ = b := by
  obtain ⟨σ, hσ⟩ := conjugate_spec_maps (K := K)
    (a ≫ pullback.snd _ _) (b ≫ pullback.snd _ _) (by
      simpa only [Category.assoc, ← pullback.condition] using congrArg (· ≫ s) hab)
  refine ⟨σ, pullback.hom_ext ?_ ?_⟩
  · simpa using hab
  · simpa only [Category.assoc, deck_snd] using hσ

/-- A field extension induces an effective epimorphism after every base change. -/
theorem effective_projection : EffectiveEpi (pullback.fst s (specExtension K L)) := by
  have h := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap K L))).2
    (RingHom.faithfullyFlat_algebraMap_iff.mpr (by infer_instance))
  let : Flat (specExtension K L) := h.1
  let : Surjective (specExtension K L) := h.2
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- A morphism from the scalar extension to a rational target descends
uniquely if it is invariant under every deck transformation. The overlap
is taken in schemes; reducedness makes its residue-field points detect equality. -/
theorem existsUnique_of_invariant [Normal K L] (t : Y ⟶ Spec (.of K)) [IsSeparated t]
    (f : pullback s (specExtension K L) ⟶ Y)
    (hf : f ≫ t = pullback.fst _ _ ≫ s)
    (invariant : ∀ σ : L ≃ₐ[K] L, deck s σ ≫ f = f)
    [IsReduced (pullback (pullback.fst s (specExtension K L))
                         (pullback.fst s (specExtension K L)))] :
    ∃! g : X ⟶ Y, g ≫ t = s ∧ pullback.fst s (specExtension K L) ≫ g = f := by
  let π := pullback.fst s (specExtension K L)
  let D := pullback π π
  let p : D ⟶ _ := pullback.fst π π
  let q : D ⟶ _ := pullback.snd π π
  have hpq : p ≫ π = q ≫ π := pullback.condition
  have heq : p ≫ f = q ≫ f := by
    apply ext_of_fromSpecResidueField_eq _ _ t Set.univ dense_univ
    · intro x _
      let z : Spec (.of (D.residueField x)) ⟶ D := D.fromSpecResidueField x
      have hpz : (z ≫ p) ≫ π = (z ≫ q) ≫ π := by simp only [Category.assoc, hpq]
      obtain ⟨σ, hσ⟩ := conjugate_points (M := D.residueField x) s (z ≫ p) (z ≫ q) hpz
      change z ≫ p ≫ f = z ≫ q ≫ f
      calc
        _ = (z ≫ p ≫ deck s σ) ≫ f := by simp only [Category.assoc, invariant]
        _ = _ := by rw [← Category.assoc z p, hσ, Category.assoc]
    · simpa only [Category.assoc, hf] using congrArg (· ≫ s) hpq
  let : EffectiveEpi π := effective_projection s
  have rel {T : Scheme} (a b : T ⟶ _) (h : a ≫ π = b ≫ π) : a ≫ f = b ≫ f := by
    have hh := congrArg (pullback.lift a b h ≫ ·) heq
    simpa only [p, q, pullback.lift_fst_assoc, pullback.lift_snd_assoc] using hh
  refine ⟨EffectiveEpi.desc π f rel, ⟨?_, EffectiveEpi.fac π f rel⟩, ?_⟩
  · exact (cancel_epi π).mp (by rw [← Category.assoc, EffectiveEpi.fac, hf])
  · exact fun g hg => EffectiveEpi.uniq π f rel g hg.2

end ZInQBlueprint.NormalDescent

#print axioms ZInQBlueprint.NormalDescent.conjugate_field_maps
#print axioms ZInQBlueprint.NormalDescent.conjugate_spec_maps
#print axioms ZInQBlueprint.NormalDescent.deck
#print axioms ZInQBlueprint.NormalDescent.deck_fst
#print axioms ZInQBlueprint.NormalDescent.deck_snd
#print axioms ZInQBlueprint.NormalDescent.conjugate_points
#print axioms ZInQBlueprint.NormalDescent.effective_projection
#print axioms ZInQBlueprint.NormalDescent.existsUnique_of_invariant

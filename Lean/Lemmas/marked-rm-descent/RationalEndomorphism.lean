import NormalDescent
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.RingTheory.Unramified.Field
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Descent over a characteristic-zero field for reduced schemes locally of finite type. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace ZInQBlueprint.NormalDescent

universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The tensor product of an arbitrary field extension with an algebraic field
extension in characteristic zero is reduced, including for infinite extensions. -/
theorem tensor_reduced [CharZero K] [Algebra.IsAlgebraic K L]
    (M : Type u) [Field M] [Algebra K M] : _root_.IsReduced (M ⊗[K] L) := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  let : Field B := inferInstanceAs (Field (subalgebraEquivIntermediateField B))
  let : Algebra.FiniteType K B := B.fg_iff_finiteType.mp hB
  let : Algebra.FormallyUnramified K B := Algebra.FormallyUnramified.of_isSeparable K B
  exact Algebra.FormallyUnramified.isReduced_of_field M (M ⊗[K] B)

set_option backward.isDefEq.respectTransparency.types false in
theorem geometricallyReduced_extension [CharZero K] [Algebra.IsAlgebraic K L] :
    GeometricallyReduced (specExtension K L) := by
  rw [geometricallyReduced_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro M _ y
  let : Algebra K M := (Spec.preimage y).hom.toAlgebra
  have hy : y = specExtension K M := (Spec.map_preimage y).symm
  rw [hy]
  have : _root_.IsReduced (M ⊗[K] L) := tensor_reduced (L := L) M
  let : _root_.IsReduced (L ⊗[K] M) :=
    isReduced_of_injective (Algebra.TensorProduct.comm K L M)
      (Algebra.TensorProduct.comm K L M).injective (S := M ⊗[K] L)
  exact isReduced_of_isOpenImmersion (pullbackSpecIso K L M).hom

/-- Descent for a reduced locally finite type scheme with a separated target. -/
theorem existsUnique_of_galois [CharZero K] [Normal K L] {X Y : Scheme.{u}}
    (s : X ⟶ Spec (.of K)) [LocallyOfFiniteType s] [IsReduced X]
    (t : Y ⟶ Spec (.of K)) [IsSeparated t]
    (f : pullback s (specExtension K L) ⟶ Y)
    (hf : f ≫ t = pullback.fst _ _ ≫ s)
    (invariant : ∀ σ : L ≃ₐ[K] L, deck s σ ≫ f = f) :
    ∃! g : X ⟶ Y, g ≫ t = s ∧ pullback.fst s (specExtension K L) ≫ g = f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : Flat (specExtension K L) :=
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap K L))).2
      (RingHom.faithfullyFlat_algebraMap_iff.mpr (by infer_instance))).1
  have : GeometricallyReduced (specExtension K L) := geometricallyReduced_extension
  exact existsUnique_of_invariant s t f hf invariant

/-- Scalar extension of a rational endomorphism. -/
noncomputable def baseChangeEnd {X : Scheme.{u}} (s : X ⟶ Spec (.of K))
    (h : X ⟶ X) (hh : h ≫ s = s) :
    pullback s (specExtension K L) ⟶ pullback s (specExtension K L) :=
  pullback.lift (pullback.fst _ _ ≫ h) (pullback.snd _ _) (by
    simpa only [Category.assoc, hh] using (pullback.condition (f := s) (g := specExtension K L)))

@[reassoc (attr := simp)] theorem baseChangeEnd_fst {X : Scheme.{u}}
    (s : X ⟶ Spec (.of K)) (h : X ⟶ X) (hh : h ≫ s = s) :
    baseChangeEnd (L := L) s h hh ≫ pullback.fst _ _ = pullback.fst _ _ ≫ h :=
  pullback.lift_fst ..

@[reassoc (attr := simp)] theorem baseChangeEnd_snd {X : Scheme.{u}}
    (s : X ⟶ Spec (.of K)) (h : X ⟶ X) (hh : h ≫ s = s) :
    baseChangeEnd (L := L) s h hh ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd ..

theorem baseChangeEnd_commutes {X : Scheme.{u}} (s : X ⟶ Spec (.of K))
    (h : X ⟶ X) (hh : h ≫ s = s) (σ : L ≃ₐ[K] L) :
    deck s σ ≫ baseChangeEnd s h hh = baseChangeEnd s h hh ≫ deck s σ := by
  apply pullback.hom_ext <;> simp

/-- A genuine endomorphism of the base-changed scheme comes from one and only
one rational endomorphism as soon as it commutes with Galois. -/
theorem endomorphism_descent [CharZero K] [Normal K L] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of K)) [LocallyOfFiniteType s] [IsReduced X] [IsSeparated s]
    (e : pullback s (specExtension K L) ⟶ pullback s (specExtension K L))
    (he : e ≫ pullback.snd _ _ = pullback.snd _ _)
    (invariant : ∀ σ : L ≃ₐ[K] L, deck s σ ≫ e = e ≫ deck s σ) :
    ∃! h : {h : X ⟶ X // h ≫ s = s}, baseChangeEnd s h.1 h.2 = e := by
  let π := pullback.fst s (specExtension K L)
  have hf : (e ≫ π) ≫ s = π ≫ s := by
    change (e ≫ pullback.fst s _) ≫ s = pullback.fst s _ ≫ s
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  have commute (σ : L ≃ₐ[K] L) : deck s σ ≫ e ≫ π = e ≫ π := by
    rw [← Category.assoc, invariant, Category.assoc, deck_fst]
  obtain ⟨h, ⟨hs, hb⟩, uniq⟩ := existsUnique_of_galois s s (e ≫ π) hf commute
  refine ⟨⟨h, hs⟩, pullback.hom_ext ?_ ?_, ?_⟩
  · simpa using hb
  · simpa using he.symm
  · intro k hk
    apply Subtype.ext
    exact uniq _ ⟨k.2, by simpa only [π, baseChangeEnd_fst] using congrArg (· ≫ π) hk⟩

end ZInQBlueprint.NormalDescent

#print axioms ZInQBlueprint.NormalDescent.tensor_reduced
#print axioms ZInQBlueprint.NormalDescent.geometricallyReduced_extension
#print axioms ZInQBlueprint.NormalDescent.existsUnique_of_galois
#print axioms ZInQBlueprint.NormalDescent.baseChangeEnd
#print axioms ZInQBlueprint.NormalDescent.baseChangeEnd_fst
#print axioms ZInQBlueprint.NormalDescent.baseChangeEnd_snd
#print axioms ZInQBlueprint.NormalDescent.baseChangeEnd_commutes
#print axioms ZInQBlueprint.NormalDescent.endomorphism_descent

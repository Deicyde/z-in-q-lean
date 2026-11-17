import RationalEndomorphism
import Mathlib.CategoryTheory.Monoidal.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! Galois descent in the category of group schemes. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Functor MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ZInQBlueprint.NormalDescent

section Reflection
variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]

/-- A faithful strong monoidal functor detects preservation of unit and multiplication. -/
theorem isMonHom_of_map (F : C ⥤ D) [F.Monoidal] [F.Faithful]
    {A B : C} [MonObj A] [MonObj B] (f : A ⟶ B) (h : IsMonHom (F.map f)) :
    IsMonHom f where
  one_hom := F.map_injective <| by
    simp [← obj.η_def_assoc, ← obj.η_def, ← cancel_epi (LaxMonoidal.ε F)]
  mul_hom := F.map_injective <| by
    simp [← obj.μ_def_assoc, ← obj.μ_def, ← LaxMonoidal.μ_natural_assoc,
      ← cancel_epi (LaxMonoidal.μ F ..)]

end Reflection

universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- Every scalar extension of fields yields a faithful functor on schemes over the base. -/
theorem faithful_scalar_extension : (Over.pullback (specExtension K L)).Faithful := by
  let h (X : Scheme.{u}) (s : X ⟶ Spec (.of K)) : Epi (pullback.fst s (specExtension K L)) := by
    have := effective_projection (L := L) s
    infer_instance
  infer_instance

/-- Descent for genuine group-scheme endomorphisms. No linear representation of the
group of geometric points is used. -/
theorem groupEndomorphism_descent [CharZero K] [Normal K L]
    (G : Grp (Over (Spec (.of K)))) [LocallyOfFiniteType G.X.hom]
    [IsReduced G.X.left] [IsSeparated G.X.hom]
    (e : (Over.pullback (specExtension K L)).mapGrp.obj G ⟶
      (Over.pullback (specExtension K L)).mapGrp.obj G)
    (invariant : ∀ σ : L ≃ₐ[K] L,
      deck G.X.hom σ ≫ e.hom.hom.left = e.hom.hom.left ≫ deck G.X.hom σ) :
    ∃! f : G ⟶ G, (Over.pullback (specExtension K L)).mapGrp.map f = e := by
  let F := Over.pullback (specExtension K L)
  have : F.Faithful := faithful_scalar_extension
  obtain ⟨h, hb, _⟩ := endomorphism_descent G.X.hom e.hom.hom.left (Over.w e.hom.hom) invariant
  let a : G.X ⟶ G.X := Over.homMk h.1 h.2
  have ha : F.map a = e.hom.hom := Over.OverMorphism.ext hb
  have hm : IsMonHom (F.map a) := by rw [ha]; exact e.hom.isMonHom_hom
  have : IsMonHom a := isMonHom_of_map F a hm
  refine ⟨Grp.homMk a, Grp.hom_ext _ _ ha, ?_⟩
  intro f hf
  exact F.mapGrp.map_injective (hf.trans (Grp.hom_ext _ _ ha).symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- If a polarized descent isomorphism differs from the canonical Galois
comparison by the identity or inversion, then it fixes the specified
endomorphism. Both signs define isomorphisms of the underlying scheme. -/
theorem groupEndomorphism_of_signed_intertwiners [CharZero K] [Normal K L]
    (G : Grp (Over (Spec (.of K)))) [LocallyOfFiniteType G.X.hom]
    [IsReduced G.X.left] [IsSeparated G.X.hom]
    (e : (Over.pullback (specExtension K L)).mapGrp.obj G ⟶
      (Over.pullback (specExtension K L)).mapGrp.obj G)
    (intertwines : ∀ σ : L ≃ₐ[K] L, ∃ a : _ ⟶ _,
      (a = 𝟙 _ ∨ a = (ι[((Over.pullback (specExtension K L)).mapGrp.obj G).X]).left) ∧
      (deck G.X.hom σ ≫ a) ≫ e.hom.hom.left = e.hom.hom.left ≫ deck G.X.hom σ ≫ a) :
    ∃! f : G ⟶ G, (Over.pullback (specExtension K L)).mapGrp.map f = e := by
  apply groupEndomorphism_descent
  intro σ
  obtain ⟨a, ha, hint⟩ := intertwines σ
  rcases ha with rfl | rfl
  · let X := ((Over.pullback (specExtension K L)).mapGrp.obj G).X.left
    let d : X ⟶ X := deck G.X.hom σ
    let E : X ⟶ X := e.hom.hom.left
    change (d ≫ 𝟙 X) ≫ E = E ≫ d ≫ 𝟙 X at hint
    change d ≫ E = E ≫ d
    simpa only [Category.comp_id] using hint
  · let H := (Over.pullback (specExtension K L)).mapGrp.obj G
    let d : H.X.left ⟶ H.X.left := deck G.X.hom σ
    let E : H.X.left ⟶ H.X.left := e.hom.hom.left
    let n : H.X.left ⟶ H.X.left := (ι[H.X]).left
    have hcomm : n ≫ E = E ≫ n :=
      congrArg (fun f => f.left) (GrpObj.inv_hom e.hom.hom)
    change (d ≫ n) ≫ E = E ≫ d ≫ n at hint
    change d ≫ E = E ≫ d
    apply (cancel_mono n).mp
    simpa only [Category.assoc, hcomm] using hint

end ZInQBlueprint.NormalDescent

#print axioms ZInQBlueprint.NormalDescent.isMonHom_of_map
#print axioms ZInQBlueprint.NormalDescent.faithful_scalar_extension
#print axioms ZInQBlueprint.NormalDescent.groupEndomorphism_descent
#print axioms ZInQBlueprint.NormalDescent.groupEndomorphism_of_signed_intertwiners

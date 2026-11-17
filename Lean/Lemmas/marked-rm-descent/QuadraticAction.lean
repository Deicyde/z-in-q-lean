import GroupEndomorphism
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-! The integral real multiplication action on a commutative group scheme
descends from the signed intertwining of the single generator √3. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace ZInQBlueprint.NormalDescent

section Pointwise
variable {C D : Type*} [Category* C] [Category* D]
  [CartesianMonoidalCategory C] [BraidedCategory C]
  [CartesianMonoidalCategory D] [BraidedCategory D]

/-- Pointwise addition endows the category of commutative group objects with
its preadditive structure. -/
@[implicit_reducible]
def pointwisePreadditive (C : Type*) [Category* C]
    [CartesianMonoidalCategory C] [BraidedCategory C] : Preadditive (CommGrp C) where
  homGroup P Q :=
    ((InducedCategory.homEquiv : (P ⟶ Q) ≃ (P.toGrp ⟶ Q.toGrp)).trans Additive.ofMul).addCommGroup
  add_comp _ _ _ f g h := InducedCategory.hom_ext (MonObj.mul_comp f.hom g.hom h.hom)
  comp_add _ _ _ f g h := InducedCategory.hom_ext (MonObj.comp_mul f.hom g.hom h.hom)

scoped instance : Preadditive (CommGrp C) := pointwisePreadditive C

theorem additive_mapCommGrp (F : C ⥤ D) [F.Braided] : F.mapCommGrp.Additive where
  map_add {A B} f g := by
    apply CommGrp.hom_ext
    exact F.map_mul f.hom.hom.hom g.hom.hom.hom

/-- Base change as a ring homomorphism on the endomorphism rings. -/
def changeEndRing (F : C ⥤ D) [F.Braided] (A : CommGrp C) :
    End A →+* End (F.mapCommGrp.obj A) where
  toFun f := End.of (F.mapCommGrp.map f.asHom)
  map_one' := (F.mapCommGrp.mapEnd A).map_one
  map_mul' := (F.mapCommGrp.mapEnd A).map_mul
  map_zero' := by
    have : F.mapCommGrp.Additive := additive_mapCommGrp F
    exact congrArg End.of (F.mapCommGrp.map_zero A A)
  map_add' f g := by
    have : F.mapCommGrp.Additive := additive_mapCommGrp F
    exact congrArg End.of (F.mapCommGrp.map_add (f := f.asHom) (g := g.asHom))

theorem changeEndRing_injective (F : C ⥤ D) [F.Braided] [F.Faithful] (A : CommGrp C) :
    Function.Injective (changeEndRing F A) := fun _ _ h =>
  End.homEquiv.injective (F.mapCommGrp.map_injective (congrArg End.asHom h))

end Pointwise

/-- The order Z[√3] with its distinguished generator. -/
abbrev realOrder := QuadraticAlgebra ℤ 3 0

section Ring
variable {R T : Type*} [Ring R] [Ring T]

/-- Lifting the single generator lifts the whole specified order action. -/
theorem lift_realOrder (b : R →+* T) (hb : Function.Injective b)
    (i : realOrder →+* T) (hi : Function.Injective i)
    (hω : ∃ x, b x = i QuadraticAlgebra.omega) :
    ∃! j : realOrder →+* R, Function.Injective j ∧ b.comp j = i := by
  obtain ⟨x, hx⟩ := hω
  have mem (r : realOrder) : i r ∈ b.range := by
    rcases r with ⟨a,c⟩
    rw [QuadraticAlgebra.mk_eq_add_smul_omega, map_add, map_zsmul]
    exact b.range.add_mem (by simp)
      (b.range.zsmul_mem ⟨x,hx⟩ c)
  let e : R ≃+* b.range := RingEquiv.ofBijective b.rangeRestrict
    ⟨fun _ _ h => hb (congrArg Subtype.val h), b.rangeRestrict_surjective⟩
  let j := e.symm.toRingHom.comp (i.codRestrict _ mem)
  have hj (r) : b (j r) = i r := congrArg Subtype.val (e.apply_symm_apply (i.codRestrict _ mem r))
  refine ⟨j, ⟨fun a c h => hi ((hj a).symm.trans ((congrArg b h).trans (hj c))),
    RingHom.ext hj⟩, ?_⟩
  intro j' hj'
  exact RingHom.ext fun r => hb ((DFunLike.congr_fun hj'.2 r).trans (hj r).symm)

end Ring

universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [CharZero K] [Normal K L]

/-- On a rational model the descent of the specified embedding of Z[√3]
reduces to one signed intertwiner per Galois automorphism for its generator. -/
theorem real_multiplication_of_signed_generator
    (G : CommGrp (Over (Spec (.of K)))) [LocallyOfFiniteType G.X.hom]
    [IsReduced G.X.left] [IsSeparated G.X.hom]
    (i : realOrder →+* End ((Over.pullback (specExtension K L)).mapCommGrp.obj G))
    (hi : Function.Injective i)
    (intertwines : let E := (i QuadraticAlgebra.omega).asHom.hom.hom.hom.left
      ∀ σ : L ≃ₐ[K] L, ∃ a : _ ⟶ _,
        (a = 𝟙 _ ∨ a = (GrpObj.inv (X := ((Over.pullback (specExtension K L)).mapCommGrp.obj G).X)).left) ∧
        (deck G.X.hom σ ≫ a) ≫ E = E ≫ deck G.X.hom σ ≫ a) :
    ∃! j : realOrder →+* End G, Function.Injective j ∧
      (changeEndRing (Over.pullback (specExtension K L)) G).comp j = i := by
  let F := Over.pullback (specExtension K L)
  have : F.Faithful := faithful_scalar_extension
  apply lift_realOrder (changeEndRing F G) (changeEndRing_injective F G) i hi
  obtain ⟨h, hh, _⟩ := groupEndomorphism_of_signed_intertwiners G.toGrp
    (i QuadraticAlgebra.omega).asHom.hom intertwines
  exact ⟨End.of (InducedCategory.homMk h), End.homEquiv.injective (InducedCategory.hom_ext hh)⟩

end ZInQBlueprint.NormalDescent

#print axioms ZInQBlueprint.NormalDescent.pointwisePreadditive
#print axioms ZInQBlueprint.NormalDescent.additive_mapCommGrp
#print axioms ZInQBlueprint.NormalDescent.changeEndRing
#print axioms ZInQBlueprint.NormalDescent.changeEndRing_injective
#print axioms ZInQBlueprint.NormalDescent.lift_realOrder
#print axioms ZInQBlueprint.NormalDescent.real_multiplication_of_signed_generator

import QuadraticAction
import RealMultiplication

/-! Application to the coordinate of an unmarked six-contact fibre. -/

open CategoryTheory AlgebraicGeometry
open ZInQBlueprint.SixContact ZInQBlueprint.CoarseConic
open scoped CategoryTheory.Obj

namespace ZInQBlueprint.NormalDescent

abbrev Qbar := AlgebraicClosure ℚ

/-- The labelled-moduli comparison must supply a polarized correction to
the canonical Galois comparison of the generator. Torelli and the absence
of extra curve automorphisms must classify those corrections. -/
theorem six_contact_real_multiplication {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (A : CommGrp (Over (Spec (.of ℚ)))) [LocallyOfFiniteType A.X.hom]
    [IsReduced A.X.left] [IsSeparated A.X.hom]
    (i : realOrder →+* End ((Over.pullback (specExtension ℚ Qbar)).mapCommGrp.obj A))
    (hi : Function.Injective i)
    (polarized : (((Over.pullback (specExtension ℚ Qbar)).mapCommGrp.obj A).X.left ⟶
      ((Over.pullback (specExtension ℚ Qbar)).mapCommGrp.obj A).X.left) → Prop)
    (labelled : IsSquare (-(27 * J u + 16) / J u) →
      let E := (i QuadraticAlgebra.omega).asHom.hom.hom.hom.left
      ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∃ a, polarized a ∧
        (deck A.X.hom σ ≫ a) ≫ E = E ≫ deck A.X.hom σ ≫ a)
    (signs : J u * (64 * J u - 81) * (27 * J u + 16) ≠ 0 →
      ∀ a, polarized a → a = 𝟙 _ ∨
        a = (GrpObj.inv (X := ((Over.pullback (specExtension ℚ Qbar)).mapCommGrp.obj A).X)).left) :
    ∃! j : realOrder →+* End A, Function.Injective j ∧
      (changeEndRing (Over.pullback (specExtension ℚ Qbar)) A).comp j = i := by
  apply real_multiplication_of_signed_generator A i hi
  have hsquare : IsSquare (-(27 * J u + 16) / J u) := by
    rw [RealMultiplication.real_coordinate, pow_two]
    exact ⟨_, rfl⟩
  dsimp only
  intro σ
  obtain ⟨a, ha, intertwines⟩ := labelled hsquare σ
  exact ⟨a, signs (mestre_factors hu) a ha, intertwines⟩

end ZInQBlueprint.NormalDescent

#print axioms ZInQBlueprint.NormalDescent.six_contact_real_multiplication

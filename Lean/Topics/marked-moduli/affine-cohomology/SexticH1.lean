import AffineVanishingInput
import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-! Affine vanishing for Mathlib's cohomology presheaf and the dimension of the sextic's H¹. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace Opposite
namespace ZInQBlueprint.BinaryCover.Cech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 8000
open ModuleSheafCohomology

/-- Deriving sections over an affine open in modules gives the same vanishing as evaluating
Mathlib's Ext-defined cohomology presheaf on its underlying additive sheaf. -/
theorem affineVanishing : AffineVanishingInDegreeOne := by
  intro X M hM U hU
  let J := Opens.grothendieckTopology X
  let R := X.ringCatSheaf
  let G := (sheafSections J AddCommGrpCat.{0}).obj (op U)
  let _ : G.Additive := inferInstanceAs ((sheafToPresheaf J AddCommGrpCat.{0} ⋙
      (evaluation _ _).obj (op U)).Additive)
  let _ : PreservesFiniteLimits G := inferInstanceAs (PreservesFiniteLimits
    (sheafToPresheaf J AddCommGrpCat.{0} ⋙ (evaluation _ _).obj (op U)))
  let T := SheafOfModules.toSheaf.{0} R
  let A := ((presheafToSheaf J AddCommGrpCat).obj (yoneda.obj U ⋙ AddCommGrpCat.free))
  let α : G ≅ preadditiveCoyoneda.obj (op A) := evaluationRepresentation J U
  obtain ⟨_,_,e⟩ := moduleSheafCohomologyIsoUnderlying J R
  obtain ⟨β,_⟩ := e U
  obtain ⟨γ⟩ := nonempty_extFunctorObj_iso_rightDerived G A α 1
  have hz := Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X M U hU 1 (by decide)
  let equiv : ((T ⋙ G).rightDerived 1).obj M ≅ (Abelian.extFunctorObj A 1).obj (T.obj M) :=
    (β 1).app M ≪≫ (γ.app (T.obj M)).symm
  exact AddCommGrpCat.subsingleton_of_isZero (IsZero.of_iso hz equiv.symm)

/-- The two odd Laurent classes span the actual first structure-sheaf cohomology of every
rational member, including singular members. -/
theorem paper_h1_dimension (u : ℚ) :
    letI := h1Module (paperModel ℚ u).hom
    Module.finrank ℚ (H1 (paperModel ℚ u).left) = 2 :=
  paper_dimension_of_standard affineVanishing u

theorem paper_sheaf_comparison (u : ℚ) : SheafComparison (k := ℚ) u :=
  paper_comparison_of_affine u (paper_affine_of_standard affineVanishing u)

end
end ZInQBlueprint.BinaryCover.Cech
#print axioms ZInQBlueprint.BinaryCover.Cech.affineVanishing
#print axioms ZInQBlueprint.BinaryCover.Cech.paper_h1_dimension
#print axioms ZInQBlueprint.BinaryCover.Cech.paper_sheaf_comparison

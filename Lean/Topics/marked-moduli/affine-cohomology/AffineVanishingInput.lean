import PaperCohomology
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! The remaining affine theorem stated for a quasi-coherent module in the standard API. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
namespace ZInQBlueprint.BinaryCover.Cech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 6000
variable (X : Scheme.{0})

/-- Forgetting the module structure on the rank-one free module gives the actual additive
structure sheaf used above. -/
theorem unit_underlying :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf) =
      additiveStructure X := rfl

/-- The structure module has one generator and the empty set of relations. -/
theorem unit_quasicoherent : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent := by
  let R := X.ringCatSheaf
  let a : SheafOfModules.free PEmpty (R := R) ⟶ SheafOfModules.free PUnit := 0
  let M := SheafOfModules.free PUnit (R := R)
  let P : SheafOfModules.Presentation M := SheafOfModules.presentationOfIsCokernelFree a
    (𝟙 M) (by simp [a]) (CokernelCofork.IsColimit.ofId a rfl)
  let e : M ≅ SheafOfModules.unit R := coproductUniqueIso (fun _ : PUnit => SheafOfModules.unit R)
  exact (P.ofIsIso e.hom).isQuasicoherent

/-- Affine acyclicity in degree one in the precise objectwise cohomology used by Mathlib. -/
def AffineVanishingInDegreeOne : Prop :=
    ∀ (X : Scheme.{0}) (M : X.Modules) [M.IsQuasicoherent] (U : X.Opens), IsAffineOpen U →
      Subsingleton (Sheaf.H'.{0} ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) 1 U)

theorem paper_affine_of_standard (vanish : AffineVanishingInDegreeOne) (u : ℚ) : PaperAffineH1 u := by
  let X := (paperModel ℚ u).left
  let M := SheafOfModules.unit X.ringCatSheaf
  let _ : M.IsQuasicoherent := unit_quasicoherent X
  intro i
  let U := atlasOpen ℚ _ _ (paper_overlap ℚ u) (some i)
  let _ : IsAffine ((diagram ℚ _ _ (paper_overlap ℚ u)).obj (some i)) :=
    inferInstanceAs (IsAffine (Spec (.of (Cover (if i then paper ℚ u true else paper ℚ u false)))))
  have hU : IsAffineOpen U := isAffineOpen_opensRange (atlasMap ℚ _ _ (paper_overlap ℚ u) (some i))
  exact vanish X M U hU

theorem paper_dimension_of_standard (vanish : AffineVanishingInDegreeOne) (u : ℚ) :
    letI := h1Module (paperModel ℚ u).hom
    Module.finrank ℚ (H1 (paperModel ℚ u).left) = 2 :=
  paper_dimension_of_affine u (paper_affine_of_standard vanish u)

end
end ZInQBlueprint.BinaryCover.Cech
#print axioms ZInQBlueprint.BinaryCover.Cech.unit_underlying
#print axioms ZInQBlueprint.BinaryCover.Cech.unit_quasicoherent
#print axioms ZInQBlueprint.BinaryCover.Cech.paper_affine_of_standard
#print axioms ZInQBlueprint.BinaryCover.Cech.paper_dimension_of_standard

import CatalogueLevel28
import FourMultiplierMenus

namespace ZInQBlueprint.WildLevel
open Sun28 Sun28.Concrete Sun28.MultiplierChoice ZInQBlueprint.FiveMetric
open Sun28.Ordinary Sun28.TwistRank Sun28.TwistExtension Sun28.ScalarHeight
  Sun28.FixedPreparation Sun28.Forward Sun28.WitnessIndices ZInQ
noncomputable section

/-- The four local choices use one nine-tuple and one rational slope for each integer. -/
def JointSelectedMenus : Prop := ∀ k : ℤ,
  ∃ a : Fin 9 → AffineInput, ∃ η : ℚ, SelectedAt (nineAffine a).doubles (k:ℚ) η ∧
    FourMenus (nineAffine a).doubles (k:ℚ) η

theorem polynomial_of_selected_menus (height : LevelApplications)
    (points : JointSelectedMenus) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 fixedPolynomial x w=0) ↔ ∃ k : ℤ, x=(k:ℚ) := by
  refine ⟨WitnessHeight.integral_of_two_loci
    (WitnessHeight.two_loci_of_uniform (five_height_of_surface (surface_of_level height))) x,?_⟩
  rintro ⟨k,rfl⟩
  exact root_of_selected_menus (points k)

end
end ZInQBlueprint.WildLevel
#print axioms ZInQBlueprint.WildLevel.polynomial_of_selected_menus

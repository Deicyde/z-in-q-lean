import CurveDimension
import LineValuation
import SmoothSextic
import LocalFunctionField

/-! The smooth proper model of the rational paper sextic. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.BinaryCover
noncomputable section

/-- The fixed rational model is a smooth proper geometrically integral curve. -/
theorem paper_curve {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    Smooth (paperModel ℚ u).hom ∧ IsProper (paperModel ℚ u).hom ∧
    GeometricallyIntegral (paperModel ℚ u).hom ∧
    topologicalKrullDim (paperModel ℚ u).left = 1 :=
  ⟨smooth_paperModel hu, paper_proper ℚ u, geometricallyIntegral_paperModel hu, paper_dimension ℚ u⟩

end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.paper_curve

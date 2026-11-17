import HeightComparison
import TwoCurves
import RemainingSections

namespace ZInQBlueprint.FiveMetric
noncomputable section
set_option maxRecDepth 12000
/-- The surface-height route applied to the specified polynomial with 28 rational witnesses. -/
theorem polynomial_of_surface (realCurves : Sun28.RealComponents.PublishedProposition72)
    (quadric : Sun28.ConeCount.PublishedQuadricCount) (inputs : SurfaceApplications)
    (moments : Sun28.PrimeValues.FirstMomentInputs) (points : RemainingSections) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, Sun28.eval28 Sun28.Concrete.fixedPolynomial x w=0) ↔ ∃ k : ℤ,x=(k:ℚ) :=
  Sun28.WitnessHeight.two_loci_projection realCurves quadric
    (Sun28.WitnessHeight.two_loci_of_uniform (five_height_of_surface inputs)) moments
    (remaining_sections_iff.mp points) x

end
end ZInQBlueprint.FiveMetric
#print axioms ZInQBlueprint.FiveMetric.polynomial_of_surface

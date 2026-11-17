import ChartProjection28
import LogarithmicResidual
import GlobalSections
import MomentRows

/-! The fixed polynomial with a fixed-base lower count and relative first moments. -/
namespace Sun28.ReducedArithmetic
open Sun28.HeightExtension Sun28.HeightBudget Sun28.HeightFibres.Sharp Sun28.Ordinary

theorem moments_projection (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (pell : PublishedAllPell)
    (classes : PublishedClassRegulator) (characters : QuadraticCharacterDiscriminants)
    (quadric : ConeCount.PublishedQuadricCount) (elliptic : HeightCubics.Refinement.PublishedElliptic)
    (height : HeightCubics.Pooled.Logarithmic.Remaining)
    (moments : PrimeValues.FirstMomentInputs) (points : GlobalSections.SectionResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ, x=(z:ℚ) := by
  have h := (HeightCubics.Pooled.Logarithmic.original_iff_logarithmic units pell classes characters elliptic).mpr height
  have regular := GlobalSections.residual_iff_sections.mpr points
  have loc := PointLifts.residual_iff_regular.mpr regular
  have norm := PointFibres.norm_residual_iff_pencil.mpr (PointLifts.pencil_residual_iff_local_ratios.mpr loc)
  exact PrimeMass.integer_projection realCurves units pell classes characters quadric
    ((HeightRefinement.Sharp.original_iff_sharp units pell classes characters).mp h)
    (PrimeValues.hybrid_inputs_of_moments moments) norm x

end Sun28.ReducedArithmetic
#print axioms Sun28.ReducedArithmetic.moments_projection

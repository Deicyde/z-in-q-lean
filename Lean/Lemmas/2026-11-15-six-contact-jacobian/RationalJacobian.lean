import CurveGeometry
import ValuationStalks
import AbelianModel
import Nyll.JacobianVarieties.Picard.Unpointed.UnpointedJacobian
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.SmoothSmoothOfRelativeDimension
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.SmoothOfRelativeDimensionTopologicalKrullDimPreimageSingletonEq
import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.RelativeGroupLawGrpObj

/-! The unpointed Jacobian of the actual genus-two paper curve as a rational commutative group scheme. -/
open CategoryTheory AlgebraicGeometry
open ZInQBlueprint.BinaryCover GoodReductionJacobian
namespace ZInQBlueprint.SixJacobian
noncomputable section

/-- For a smooth integral curve over a field the relative dimension is captured by
the dimension of its sole set-theoretic fibre. -/
theorem relative_dimension_one {K : Type} [Field K] {C : Scheme} (f : C ⟶ Spec (.of K))
    [Smooth f] [AlgebraicGeometry.IsIntegral C] (dim : topologicalKrullDim C = 1) :
    SmoothOfRelativeDimension 1 f := by
  obtain ⟨n,hn⟩ := Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace f
  let : SmoothOfRelativeDimension n f := hn
  let y : Spec (.of K) := Classical.choice (inferInstanceAs (Nonempty (PrimeSpectrum K)))
  have hy : f.base ⁻¹' {y} = Set.univ := Set.eq_univ_iff_forall.mpr fun x =>
    (show f x = y from Subsingleton.elim _ _)
  have H : topologicalKrullDim (f.base ⁻¹' {y}) = n :=
    SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq _ _ y (hy ▸ Set.univ_nonempty)
  rw [hy,IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ C).isHomeomorph,dim] at H
  have e : n=1 := by exact_mod_cast H.symm
  exact e ▸ hn

private abbrev C (u : ℚ) := (paperModel ℚ u).left
private abbrev c (u : ℚ) := (paperModel ℚ u).hom

private theorem curve_dimension {u : ℚ} (hu : u ∉ ZInQ.contactSet) : SmoothOfRelativeDimension 1 (c u) := by
  let := smooth_paperModel hu
  let : AlgebraicGeometry.IsIntegral (C u) := paper_reglued_integral ℚ hu
  exact relative_dimension_one (c u) (paper_dimension ℚ u)

/-- An unpointed Picard descent presentation for this specific rational curve. -/
def presentation {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    JacobianVarieties.Picard.Unpointed.Presentation ℚ (c u) := by
  let : IsProper (c u) := paper_proper ℚ u
  let : SmoothOfRelativeDimension 1 (c u) := curve_dimension hu
  let : GeometricallyIntegral (c u) := geometricallyIntegral_paperModel hu
  exact JacobianVarieties.Picard.Unpointed.presentation ℚ (c u)

/-- The group law is transported from tensor product of line bundles over the
finite extension used by the effective unpointed Picard descent. -/
def jacobian {u : ℚ} (hu : u ∉ ZInQ.contactSet) : AbelianModel.GroupScheme ℚ := by
  let : IsProper (c u) := paper_proper ℚ u
  let : SmoothOfRelativeDimension 1 (c u) := curve_dimension hu
  let : GeometricallyIntegral (c u) := geometricallyIntegral_paperModel hu
  let f := JacobianVarieties.Picard.Unpointed.toBase ℚ (c u)
  let G := JacobianVarieties.Picard.Unpointed.groupLaw ℚ (c u)
  let : GrpObj (Over.mk f) := G.grpObjOverMk
  let : IsCommMonObj (Over.mk f) := G.isCommMonObj_grpObjOverMk_iff_mul_comm.mpr
    (JacobianVarieties.Picard.Unpointed.groupLaw_commutative ℚ (c u))
  exact ⟨Over.mk f⟩

/-- The stated group scheme is an actual abelian variety over Q, on the same
carrier as the finite faithfully flat descent of the relative Picard variety. -/
theorem isAbelian {u : ℚ} (hu : u ∉ ZInQ.contactSet) : AbelianModel.IsAbelianScheme (jacobian hu) := by
  let : IsProper (c u) := paper_proper ℚ u
  let : SmoothOfRelativeDimension 1 (c u) := curve_dimension hu
  let : GeometricallyIntegral (c u) := geometricallyIntegral_paperModel hu
  exact ⟨JacobianVarieties.Picard.Unpointed.proper ℚ (c u),
    JacobianVarieties.Picard.Unpointed.smooth ℚ (c u),
    JacobianVarieties.Picard.Unpointed.geometricallyConnected ℚ (c u)⟩

theorem jacobian_of_descent {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    (jacobian hu).X.left = (presentation hu).carrier := rfl

end
end ZInQBlueprint.SixJacobian
#print axioms ZInQBlueprint.SixJacobian.relative_dimension_one
#print axioms ZInQBlueprint.SixJacobian.presentation
#print axioms ZInQBlueprint.SixJacobian.jacobian
#print axioms ZInQBlueprint.SixJacobian.isAbelian
#print axioms ZInQBlueprint.SixJacobian.jacobian_of_descent

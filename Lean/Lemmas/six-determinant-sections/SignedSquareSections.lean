import SignedDifferenceMap
import SectionDescent

/-! To determine the sections of the determinant theta line on the Jacobian,
it suffices to determine the sections of its unshifted pullback to the curve square. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.DeterminantSections
open SixAbelMap GeometricMarking NormalDescent CanonicalTheta AbelianModel
noncomputable section
variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)

/-- The dual determinant on the curve square.  Its entries are the actual
pointed Poincaré determinant and the original scheme difference morphism. -/
abbrev squareTheta := (Scheme.Modules.pullback (differenceMap hu).left).obj (signedThetaLine hu)

/-- The single remaining geometric input is a dimension on C × C.
The nonzero theta section, the smoothness of J, and coverage are already proved. -/
theorem signed_rank_one (square : ThetaLinearSystem.rankH0 (curveSquare u).hom (squareTheta hu) = 1) :
    ThetaLinearSystem.rankH0 (geometricJacobian hu).X.hom (signedThetaLine hu) = 1 := by
  let : Smooth (SixJacobian.jacobian hu).X.hom := (SixJacobian.isAbelian hu).smooth
  let : Smooth (geometricJacobian hu).X.hom :=
    inferInstanceAs (Smooth (pullback.snd (SixJacobian.jacobian hu).X.hom (specExtension ℚ Qbar)))
  let : IsReduced (geometricJacobian hu).X.left :=
    isReduced_of_smooth_over_field (g := (geometricJacobian hu).X.hom) inferInstance
  exact rank_one_descends (differenceMap hu) (signedThetaLine_invertible hu)
    (signedThetaSection_ne_zero hu) (differenceMap_surjective hu) square

end
end ZInQBlueprint.DeterminantSections
#print axioms ZInQBlueprint.DeterminantSections.signed_rank_one

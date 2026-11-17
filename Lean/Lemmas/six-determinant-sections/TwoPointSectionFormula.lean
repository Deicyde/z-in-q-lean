import SignedSquareSections
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The comparison left to the two-point determinant formula is an isomorphism
of actual vector spaces. Both Riemann–Roch dimensions are calculated here. -/
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped CategoryTheory.MonObj KaehlerDifferential TensorProduct ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.DeterminantSections
open SixAbelMap GeometricMarking NormalDescent CanonicalTheta
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000
variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)

/-- The geometric rank-one two-point formula for N = O(b).  A choice of
nonzero rational differential identifies K_C(-b) with its divisor model.
The constant determinant line over the ground field can be trivialized. -/
def TwoPointSectionFormula : Prop :=
  letI := sourceIntegral hu
  letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let N := signedModel hu
  letI := N.curve
  letI := paper_essentially_finite hu
  let F := (paperCurve u).left.functionField
  letI : HasCanonicalDivisor (K:=Qbar) (F:=F) := hasCanonicalDivisor_of_isCurveOver
  let b := normalizedPlace N (basepoint hu)
  let D : Divisor Qbar F := Finsupp.single b 1
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (curveSquare u).hom (squareTheta hu) ⊤
  ∃ (ω : Ω[F⁄Qbar]) (hω : ω ≠ 0), Nonempty
    (Γ(squareTheta hu,⊤) ≃ₗ[Qbar] (LSpace D ⊗[Qbar] LSpace (canonicalDivisorOf hω - D)))

theorem square_rank_of_two_point_formula (form : TwoPointSectionFormula hu) :
    ThetaLinearSystem.rankH0 (curveSquare u).hom (squareTheta hu) = 1 := by
  let := sourceIntegral hu
  let := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let N := signedModel hu
  let := N.curve
  let := paper_essentially_finite hu
  let F := (paperCurve u).left.functionField
  let : HasCanonicalDivisor (K:=Qbar) (F:=F) := hasCanonicalDivisor_of_isCurveOver
  let b := normalizedPlace N (basepoint hu)
  let D : Divisor Qbar F := Finsupp.single b 1
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (curveSquare u).hom (squareTheta hu) ⊤
  obtain ⟨ω,hω,⟨e⟩⟩ := form
  have hg : genusFF Qbar F = 2 := paper_functionField_genus hu
  have d1 : Module.finrank Qbar (LSpace D) = 1 := by
    obtain ⟨t,ht,hfin,-⟩ := IsCurveOver.exists_separating_transcendental (K:=Qbar) (F:=F)
    have hC := constantsAreBase_of_isAlgClosed_of_transcendental t ht
    rw [show LSpace D = LSpace 0 from lSpace_point_eq_constants (show 0 < genusFF Qbar F by rw [hg]; decide) b]
    exact ell_zero_eq_one_of_constantsAreBase hC
  have d2 : Module.finrank Qbar (LSpace (canonicalDivisorOf hω - D)) = 1 :=
    (paper_canonical_pencil hu b ω hω).2
  change Module.finrank Qbar Γ(squareTheta hu,⊤) = 1
  exact e.finrank_eq.trans (by rw [Module.finrank_tensorProduct,d1,d2])

theorem signed_rank_of_two_point_formula (form : TwoPointSectionFormula hu) :
    ThetaLinearSystem.rankH0 (geometricJacobian hu).X.hom (signedThetaLine hu) = 1 :=
  signed_rank_one hu (square_rank_of_two_point_formula hu form)

end
end ZInQBlueprint.DeterminantSections
#print axioms ZInQBlueprint.DeterminantSections.square_rank_of_two_point_formula
#print axioms ZInQBlueprint.DeterminantSections.signed_rank_of_two_point_formula

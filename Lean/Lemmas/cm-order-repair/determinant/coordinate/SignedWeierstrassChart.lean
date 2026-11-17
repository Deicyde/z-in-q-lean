import WeierstrassCoordinates

/-! Identify the two-chart model of the explicit signed sextic in the
general formula. Transport to the actual scalar extension is carried out
only after the finite coordinates are identified on the reglued model. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.WeierstrassCoordinates
open BinaryCover WeightedCurvePoints GeometricMarking MarkedForm SixAbelMap
open NormalDescent SexticIgusaChart
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000

def signedCoefficients (u : ℚ) : Coeff Qbar 6 :=
  scale (paperScale u (δ u) / 60) (coeffs (parameter u : Qbar))

theorem signedCoefficients_eval {u : ℚ} (hu : u ∉ ZInQ.contactSet) (p : Qbar × Qbar) :
    evalF (signedCoefficients u) p.1 p.2 = paperForm u (δ u) p := by
  obtain ⟨x,z⟩ := p
  rw [signedCoefficients,eval_scale,coeffs_eval,paper_formula hu]
  change paperScale u (δ u) / 60 * (60 * _) = _
  ring

theorem signed_affine_eval (u : ℚ) (x : Qbar) :
    aeval x (paper Qbar u false) = paperForm u (δ u) (x,1) := paper_evaluate Qbar u false x

def signedReader (u : ℚ) :
    Finite (paperForm u (δ u)) → Sections Qbar (paperModel Qbar u) :=
  finiteReader _ _ (paper_overlap Qbar u) _ (signed_affine_eval u)

theorem signedReader_eq {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (p : Finite (paperForm u (δ u))) :
    weightedEquiv_reglued hu (finitePoint p) = signedReader u p := by
  change weightedSections Qbar hu (toWeighted _ (.inl p)) = _
  apply (weighted_finite Qbar hu p).trans
  apply congrArg (chartSection _ _ (paper_overlap Qbar u) false)
  exact Subtype.ext rfl

theorem signed_reglued_action (coordinates : VoightCoordinateFormula) {u : ℚ}
    (hu : u ∉ ZInQ.contactSet) :
    HasFiniteAction (paperModel Qbar u) (paperForm u (δ u)) (signedReader u) :=
  coordinates _ _ (paper_overlap Qbar u) (signedCoefficients u) _ (finite_degree Qbar hu)
    (paper_chart_regular Qbar hu false).2 (signedCoefficients_eval hu) (signed_affine_eval u)

theorem signed_pullback_action (coordinates : VoightCoordinateFormula) {u : ℚ}
    (hu : u ∉ ZInQ.contactSet) : HasFiniteAction (paperCurve u) (paperForm u (δ u))
        (fun p => weightedEquiv_pullback hu (finitePoint p)) := by
  apply finiteAction_of_iso (baseChangeIso hu) _ (signedReader u) _ _ (signed_reglued_action coordinates hu)
  intro p
  rw [weightedEquiv_pullback_apply, signedReader_eq hu p]

end
end ZInQBlueprint.WeierstrassCoordinates
#print axioms ZInQBlueprint.WeierstrassCoordinates.signedCoefficients_eval
#print axioms ZInQBlueprint.WeierstrassCoordinates.signedReader_eq
#print axioms ZInQBlueprint.WeierstrassCoordinates.signed_reglued_action
#print axioms ZInQBlueprint.WeierstrassCoordinates.signed_pullback_action

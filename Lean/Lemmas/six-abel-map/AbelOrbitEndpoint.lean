import SignedSixAbel
import SixAbelPlaceAction
import SixAbelOrbitSum
import PaperDeckAction

/-! The literal deck involution and its covariant action on normalized geometric places. -/
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.SixAbelMap
open WeightedCurvePoints BinaryCover GeometricMarking NormalDescent MarkedForm GoodReductionJacobian
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

/-- The deck involution on the original scalar extension, with its finite-chart normalization. -/
def geometricDeck {u : ℚ} (hu : u ∉ ZInQ.contactSet) : paperCurve u ≅ paperCurve u :=
  (baseChangeIso hu).symm ≪≫ paperDeck u ≪≫ baseChangeIso hu

theorem weighted_deck {u : ℚ} (hu : u ∉ ZInQ.contactSet) (p : FibrePoints u) :
    weightedEquiv_pullback hu (negY (paperForm u (δ u)) p) =
      weightedEquiv_pullback hu p ≫ (geometricDeck hu).hom := by
  rw [weightedEquiv_pullback_apply,weightedEquiv_pullback_apply]
  change (weightedSections Qbar hu (negY _ p)) ≫ _ = _
  rw [equiv_deck hu]
  simp only [geometricDeck,Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.hom_inv_id_assoc]
  rfl

/-- The actual function field, with base scalar map from the geometric structure morphism. -/
def PrincipalFibres {u : ℚ} (hu : u ∉ ZInQ.contactSet) : Prop :=
  letI := sourceIntegral hu
  letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let s := SemilinearAut.ofAlgAut (functionAction (geometricDeck hu))
  ∀ P Q : Place Qbar (paperCurve u).left.functionField,
    (degreeTwo P (s • P) - degreeTwo Q (s • Q)).IsPrincipal

/-- The only input is a principal-divisor calculation in the function field of the curve. -/
def divisorData_of_principal {u : ℚ} (hu : u ∉ ZInQ.contactSet) (h : PrincipalFibres hu) :
    DivisorData hu where
  abel := weightedAbel hu
  generate := weighted_generate hu
  fibres p q := by
    let := sourceIntegral hu
    let := (baseToFunctionField (paperCurve u).hom).toAlgebra
    let N := signedModel hu
    let := N.curve
    let e := geometricDeck hu
    let P := weightedEquiv_pullback hu p
    let Q := weightedEquiv_pullback hu q
    have hp := h (normalizedPlace N P) (normalizedPlace N Q)
    rw [←normalizedPlace_action N e P,←normalizedPlace_action N e Q] at hp
    change abel hu P + abel hu (weightedEquiv_pullback hu (negY _ p)) =
      abel hu Q + abel hu (weightedEquiv_pullback hu (negY _ q))
    rw [weighted_deck hu p,weighted_deck hu q]
    exact (realization hu).sum_eq_of_principal P (P ≫ e.hom) Q (Q ≫ e.hom) hp

end
end ZInQBlueprint.SixAbelMap
#print axioms ZInQBlueprint.SixAbelMap.geometricDeck
#print axioms ZInQBlueprint.SixAbelMap.weighted_deck
#print axioms ZInQBlueprint.SixAbelMap.divisorData_of_principal

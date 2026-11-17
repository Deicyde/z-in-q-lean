import WeightedPointEndpoint
import SixFixedPoints
import GeometricFibrePoints
import UnramifiedParameter

/-! Explicit projection and hyperelliptic involution on the literal scalar
extension of the rational paper curve. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.WeightedCurvePoints
open BinaryCover MarkedForm GeometricMarking NormalDescent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def pullbackDeck {u : ℚ} (hu : u∉ZInQ.contactSet) : paperPullback Qbar u ≅ paperPullback Qbar u :=
  (baseChangeIso hu).symm ≪≫ paperDeck u ≪≫ baseChangeIso hu

theorem weightedEquiv_pullback_deck {u : ℚ} (hu : u∉ZInQ.contactSet) (p : FibrePoints u) :
    weightedEquiv_pullback hu (negY _ p) = weightedEquiv_pullback hu p ≫ (pullbackDeck hu).hom := by
  rw [weightedEquiv_pullback_apply,weightedEquiv_pullback_apply]
  change weightedSections Qbar hu (negY _ p) ≫ (baseChangeIso hu).hom =
    (weightedSections Qbar hu p ≫ (baseChangeIso hu).hom) ≫
      (baseChangeIso hu).inv ≫ (paperDeck u).hom ≫ (baseChangeIso hu).hom
  rw [equiv_deck,Category.assoc,Category.assoc,Iso.hom_inv_id_assoc]

def pullbackProjection {u : ℚ} (hu : u∉ZInQ.contactSet) :
    (paperPullback Qbar u).left ⟶ projectiveLine Qbar :=
  (baseChangeIso hu).inv.left ≫ toLine Qbar _ _ (paper_overlap Qbar u)

theorem weightedEquiv_pullback_line {u : ℚ} (hu : u∉ZInQ.contactSet) (p : FibrePoints u) :
    (weightedEquiv_pullback hu p).left ≫ pullbackProjection hu =
      (weightedEquiv_reglued hu p).left ≫ toLine Qbar _ _ (paper_overlap Qbar u) := by
  rw [weightedEquiv_pullback_apply]
  let e := (Over.forget _).mapIso (baseChangeIso hu)
  change (_ ≫ e.hom) ≫ e.inv ≫ _ = _
  rw [Category.assoc,Iso.hom_inv_id_assoc]

theorem infinity_fibre_two {u : ℚ} (hu : u∉ZInQ.contactSet) :
    Nat.card (LineFibre _ _ (paper_overlap Qbar u) true 0)=2 := by
  classical
  rw [fibre_count]
  have hn : aeval (0:Qbar) (paper Qbar u true) ≠ 0 := by
    simpa only [paper_evaluate,ite_true] using (infinity_value_ne (K:=Qbar) hu)
  exact ite_eq_right hn
end
end ZInQBlueprint.WeightedCurvePoints
#print axioms ZInQBlueprint.WeightedCurvePoints.weightedEquiv_pullback_deck
#print axioms ZInQBlueprint.WeightedCurvePoints.weightedEquiv_pullback_line
#print axioms ZInQBlueprint.WeightedCurvePoints.infinity_fibre_two

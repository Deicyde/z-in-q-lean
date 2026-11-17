import WeightedRepresentatives
import GluedCurvePoints

/-! The actual paper sextic and its finite and infinite equations. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.WeightedCurvePoints
open BinaryCover CurveChart MarkedForm
noncomputable section
variable (K : Type) [Field K] [CharZero K]

abbrev F (u : ℚ) := paperForm u (GlobalTwist.delta u : K)

theorem paper_homogeneous {u : ℚ} (hu : u∉ZInQ.contactSet) (c x z : K) :
    F K u (c*x,c*z) = c^6 * F K u (x,z) := by
  rw [F, paper_formula hu, paper_formula hu,form_homogeneous]
  ring

theorem paper_evaluate (u : ℚ) (i : Bool) (x : K) :
    aeval x (paper K u i) = F K u (if i then 1 else x, if i then x else 1) := by
  let φ := (aeval x : K[X] →ₐ[K] K).toRingHom
  have hc : φ.comp ((C : K →+* K[X]).comp (Rat.castHom K)) = Rat.castHom K := by
    ext v
    simp [φ]
  have hv : (fun j => φ (![if i then (1:K[X]) else X, if i then X else 1] j)) =
      ![if i then 1 else x,if i then x else 1] := by
    funext j
    fin_cases j <;> cases i <;> simp [φ]
  change φ (C _ * _) = (GlobalTwist.delta u : K)*_
  rw [map_mul]
  rw [MvPolynomial.hom_eval₂, hc, hv]
  change aeval x (C _) * _ = _
  rw [aeval_C]
  rfl

def coordinateEquiv (u : ℚ) : Normal (F K u) ≃ GluedCoords (paper K u false) (paper K u true) :=
  Equiv.sumCongr
    (Equiv.subtypeEquivProp (by funext p; simp only [paper_evaluate, Bool.false_eq_true,ite_false]))
    (Equiv.subtypeEquivProp (by funext y; simp only [paper_evaluate, ite_true]))

def weightedSections {u : ℚ} (hu : u∉ZInQ.contactSet) :
    Points (F K u) ≃ Sections K (paperModel K u) :=
  ((normalEquiv _ (paper_homogeneous K hu)).symm.trans (coordinateEquiv K u)).trans
    (gluedPointEquiv _ _ (paper_overlap K u))

theorem weighted_finite {u : ℚ} (hu : u∉ZInQ.contactSet) (p : Finite (F K u)) :
    weightedSections K hu (toWeighted _ (.inl p)) =
      chartSection _ _ (paper_overlap K u) false
        ⟨p.val, by simpa only [paper_evaluate,Bool.false_eq_true,ite_false] using p.property⟩ := by
  change gluedPointEquiv _ _ _ (coordinateEquiv K u ((normalEquiv _ _).symm (normalEquiv _ (paper_homogeneous K hu) (.inl p)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem weighted_infinity {u : ℚ} (hu : u∉ZInQ.contactSet) (p : Infinity (F K u)) :
    weightedSections K hu (toWeighted _ (.inr p)) =
      chartSection _ _ (paper_overlap K u) true (infinityCoord _
        ⟨p.val, by simpa only [paper_evaluate,ite_true] using p.property⟩) := by
  change gluedPointEquiv _ _ _ (coordinateEquiv K u ((normalEquiv _ _).symm (normalEquiv _ (paper_homogeneous K hu) (.inr p)))) = _
  rw [Equiv.symm_apply_apply]
  rfl
end
end ZInQBlueprint.WeightedCurvePoints
#print axioms ZInQBlueprint.WeightedCurvePoints.paper_homogeneous
#print axioms ZInQBlueprint.WeightedCurvePoints.paper_evaluate
#print axioms ZInQBlueprint.WeightedCurvePoints.weightedSections
#print axioms ZInQBlueprint.WeightedCurvePoints.weighted_finite
#print axioms ZInQBlueprint.WeightedCurvePoints.weighted_infinity

module

public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Descent

public section

namespace DivisionResidues
open WeierstrassCurve
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F)

/-- For a finite signed multiple, division by the canonical denominator is justified. -/
theorem affine_quotient {x y x' y' : F} (P : E.toAffine.Nonsingular x y)
    (Q : E.toAffine.Nonsingular x' y') {n : ℤ}
    (h : n • (Affine.Point.some _ _ P) = Affine.Point.some _ _ Q) :
    (E.ΨSq n).eval x ≠ 0 ∧ x' = (E.Φ n).eval x / (E.ΨSq n).eval x := by
  have cleared := E.mul_eval_ΨSq_eq_eval_Φ_of_zsmul P Q h
  have live : (E.ΨSq n).eval x ≠ 0 := by
    intro he
    have hz := (E.eval_ΨSq_eq_zero_iff_zsmul_eq_zero P n).mp he
    have hz' := zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero.mp hz
    rw [h] at hz'
    exact Affine.Point.some_ne_zero Q hz'
  exact ⟨live,(eq_div_iff live).mpr cleared⟩

/-- In the reciprocal chart this reads ΨSqₙ/Φₙ whenever the output abscissa is nonzero. -/
theorem reciprocal_quotient {x y x' y' : F} (P : E.toAffine.Nonsingular x y)
    (Q : E.toAffine.Nonsingular x' y') {n : ℤ}
    (h : n • (Affine.Point.some _ _ P) = Affine.Point.some _ _ Q) (hx : x' ≠ 0) :
    (E.Φ n).eval x ≠ 0 ∧ x'⁻¹ = (E.ΨSq n).eval x / (E.Φ n).eval x := by
  obtain ⟨hn,e⟩ := affine_quotient E P Q h
  have hf : (E.Φ n).eval x ≠ 0 := by
    rw [← E.mul_eval_ΨSq_eq_eval_Φ_of_zsmul P Q h]
    exact mul_ne_zero hx hn
  exact ⟨hf,by rw [e,inv_div]⟩

#print axioms affine_quotient
#print axioms reciprocal_quotient
end DivisionResidues

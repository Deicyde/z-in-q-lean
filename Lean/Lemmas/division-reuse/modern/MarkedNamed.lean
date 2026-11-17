module

public import ActualGenerator
public import CanonicalQuotient

@[expose] public section

namespace MarkedNamed
open WeierstrassCurve

/-- Reciprocal abscissa. The group identity and the vertical line x = 0 have value zero. -/
def reciprocal {F : Type*} [Field F] (W : WeierstrassCurve F) : W.toAffine.Point → F
  | .zero => 0
  | .some x _ _ => x⁻¹

theorem named_reciprocal {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    reciprocal W (n • Affine.Point.some x y h) = (W.ΨSq n).eval x / (W.Φ n).eval x := by
  generalize he : n • Affine.Point.some x y h = M
  cases M with
  | zero =>
    change n • Affine.Point.some x y h = (0 : W.toAffine.Point) at he
    have hj := congrArg (Jacobian.Point.toAffineAddEquiv W).symm he
    rw [map_zsmul, map_zero] at hj
    have hz : (W.ΨSq n).eval x = 0 :=
      (W.eval_ΨSq_eq_zero_iff_zsmul_eq_zero h n).mpr (by simpa using hj)
    simp [reciprocal, hz]
  | some x' y' h' =>
    obtain ⟨_, eq⟩ := DivisionResidues.affine_quotient W h h' he
    change x'⁻¹ = _
    rw [eq, inv_div]

open EllipticOrbit.Field

/-- The field, curve, marked point P = 2R and both coordinates are the project definitions. -/
theorem physical_named (n : ℤ) :
    reciprocal E (n • P) =
      (E.ΨSq n).eval (ofPair (57/8,-7/2)) / (E.Φ n).eval (ofPair (57/8,-7/2)) := by
  have h : E.toAffine.Nonsingular (ofPair (57/8,-7/2)) (ofPair (-165/8,417/32)) :=
    (Affine.equation_iff_nonsingular (W:=E)).mp ((equation ..).mpr (by decide +kernel))
  have hp : P=Affine.Point.some _ _ h := coordinates_injective P_pair
  rw [hp]
  exact named_reciprocal E h n

#print axioms named_reciprocal
#print axioms physical_named
end MarkedNamed

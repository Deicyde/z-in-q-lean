import ScalarQuotient
import TorsionPolynomials

namespace Sun28.ScalarQuotients
open Sun28.WitnessHeight Sun28.ScalarHeight WeierstrassCurve WeierstrassCurve.Affine
open WeierstrassCurve.Affine.Point
noncomputable section

theorem equation_iff (m x y:ℚ) :
    (elliptic m).toAffine.Equation x y ↔ y^2=cubic m x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  dsimp [elliptic,cubic]
  constructor <;> intro e <;> linear_combination e

private theorem neg_ne {m x y:ℚ} (yn:y≠0): y≠(elliptic m).toAffine.negY x y := by
  simp [elliptic,WeierstrassCurve.Affine.negY];intro e;apply yn;linarith

private theorem double_coord {m x y:ℚ} (yn:y≠0) :
    (elliptic m).toAffine.addX x x ((elliptic m).toAffine.slope x x y y)=doubledX m x y := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl (neg_ne yn)]
  unfold doubledX WeierstrassCurve.Affine.addX WeierstrassCurve.Affine.negY
  dsimp [elliptic]
  ring_nf

theorem three_ne {m x y:ℚ} (mn:m≠0) (yn:y≠0) (h:(elliptic m).toAffine.Nonsingular x y) :
    (3:ℕ) • (some x y h)≠0 := by
  let P:=(some x y h)
  intro v
  have e:P+P= -P:=by apply eq_neg_of_add_eq_zero_left;convert v using 1; abel
  have same:=congrArg (fun T : (elliptic m).toAffine.Point => T.xRep 0) e
  dsimp [P] at same
  rw [add_self_of_Y_ne (neg_ne yn)] at same
  change (elliptic m).toAffine.addX x x ((elliptic m).toAffine.slope x x y y)=x at same
  rw [double_coord yn] at same
  exact doubled_ne_self mn yn ((equation_iff ..).mp h.1) same

theorem four_ne {m x y:ℚ} (mn:m≠0) (yn:y≠0) (h:(elliptic m).toAffine.Nonsingular x y) :
    (4:ℕ) • (some x y h)≠0 := by
  let P:=(some x y h)
  intro v
  have e:(P+P)+(P+P)=0:=by convert v using 1; abel
  have hn:=neg_ne (m:=m) (x:=x) yn
  dsimp [P] at e
  rw [add_self_of_Y_ne hn] at e
  have tors:=isRoot_twoTorsionPolynomial_of_add_self _ e
  rw [Polynomial.IsRoot.def,WeierstrassCurve.eval_toPoly_twoTorsionPolynomial] at tors
  rw [double_coord yn] at tors
  let X:=doubledX m x y
  have eqn:4*X*(X-32*m)*(X+3*m)=0:=by
    dsimp [elliptic,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆] at tors
    dsimp [X];linear_combination tors
  obtain ⟨h0,h1,h2⟩:=doubled_not_root mn yn ((equation_iff ..).mp h.1)
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h0) (sub_ne_zero.mpr h1))
    (by dsimp [X];intro z;apply h2; linarith)) eqn

/-- The only external group-theoretic input in this torsion reduction is the list of possible
exponents of rational torsion for an elliptic curve with full rational two-torsion (Mazur, Theorem 8). -/
def MazurExponentList : Prop := ∀ m:ℚ, m≠0 → ∀ P:(elliptic m).toAffine.Point,
  IsOfFinAddOrder P → (4:ℕ) • P=0 ∨ (6:ℕ) • P=0 ∨ (8:ℕ) • P=0

private theorem two_iff {m x y:ℚ} (h:(elliptic m).toAffine.Nonsingular x y) :
    (2:ℕ) • (some x y h)=0 ↔ y=0 := by
  rw [two_nsmul]
  constructor
  · intro z
    by_contra yn
    rw [add_self_of_Y_ne (neg_ne yn)] at z
    exact some_ne_zero _ z
  · rintro rfl
    apply add_self_of_Y_eq
    simp [elliptic,WeierstrassCurve.Affine.negY]

theorem four_implies_two {m:ℚ} (mn:m≠0) (P:(elliptic m).toAffine.Point)
    (h:(4:ℕ) • P=0) : (2:ℕ) • P=0 := by
  cases P with
  | zero => exact nsmul_zero ..
  | some x y valid =>
    apply (two_iff valid).mpr
    by_contra yn
    exact four_ne mn yn valid h

theorem three_implies_zero {m:ℚ} (mn:m≠0) (P:(elliptic m).toAffine.Point)
    (h:(3:ℕ) • P=0) : P=0 := by
  cases P with
  | zero => rfl
  | some x y valid =>
    by_cases yn:y=0
    · have two:=(two_iff valid).mpr yn
      have z:(3:ℕ) • (some x y valid)=(2:ℕ) • (some x y valid)+some x y valid:=by abel
      rw [z,two,zero_add] at h;exact h
    · exact False.elim (three_ne mn yn valid h)

theorem torsion_iff_two (mazur:MazurExponentList) {m:ℚ} (mn:m≠0) (P:(elliptic m).toAffine.Point) :
    IsOfFinAddOrder P ↔ (2:ℕ) • P=0 := by
  constructor
  · intro f
    rcases mazur m mn P f with h|h|h
    · exact four_implies_two mn P h
    · exact three_implies_zero mn _ (by rw [←mul_nsmul];exact h)
    · apply four_implies_two mn P
      have z:=four_implies_two mn ((2:ℕ) • P) (by rw [←mul_nsmul];exact h)
      rw [←mul_nsmul] at z;exact z
  · intro h
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2,by decide,h⟩

/-- Every scalar value actually attained produces a rational point of infinite order on the explicit twist. -/
theorem infinite_order_of_scalar (mazur:MazurExponentList) (x:ℚ) :
    ∃ P:(elliptic (21*(scalarClass x:ℚ))).toAffine.Point, ¬IsOfFinAddOrder P := by
  obtain ⟨sf,y,yn,h⟩:=octic_twist x
  let d:ℚ:=scalarClass x
  let m:ℚ:=21*d
  have dn:d≠0:=by dsimp [d];exact_mod_cast sf.ne_zero
  have mn:m≠0:=mul_ne_zero (by norm_num) dn
  let X:=twistX d x
  let Y:=twistY d x y
  have eqn:(elliptic m).toAffine.Equation X Y:=(equation_iff ..).mpr (elliptic_point h)
  have delta:(elliptic m).Δ≠0:=by rw [discriminant];positivity [mn]
  have ns:=(WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero delta).mp eqn
  refine ⟨some X Y ns,fun tors=>?_⟩
  exact (elliptic_strict dn yn h).1 ((two_iff ns).mp ((torsion_iff_two mazur mn _).mp tors))

end
end Sun28.ScalarQuotients
#print axioms Sun28.ScalarQuotients.equation_iff
#print axioms Sun28.ScalarQuotients.three_ne
#print axioms Sun28.ScalarQuotients.four_ne
#print axioms Sun28.ScalarQuotients.four_implies_two
#print axioms Sun28.ScalarQuotients.three_implies_zero
#print axioms Sun28.ScalarQuotients.torsion_iff_two
#print axioms Sun28.ScalarQuotients.infinite_order_of_scalar

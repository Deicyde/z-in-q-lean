import TYZPeriodRank

/-! The rational 2-isogeny of Tian--Yuan--Zhang, constructed from CM and
the existing short-Weierstrass scaling homomorphism. -/

namespace ZInQBlueprint.TYZ

noncomputable section
attribute [local instance] Classical.decEq
open WeierstrassCurve.Affine

/-- The inherited scaling proof is private in the pinned 4.35 build of TwistGroup.
Resolve that one declaration by its module and source name; the kernel still
checks the complete type of each application below. -/
local macro "shortCurveScaling" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `TwistGroup `ZInQBlueprint.Rank.scaleHom))

private abbrev K := Rank.Qbar
private def i : K := Rank.sqrtMinus 1
private def c : K := (1+i)/2

private theorem i_sq : i^2 = -1 := by simpa [i] using Rank.sqrtMinus_sq 1
private theorem i_ne : i ≠ 0 := by
  intro h
  have t := i_sq
  rw [h] at t
  norm_num at t

private theorem ki_sq : (-i)^2 = -1 := by simpa only [neg_sq] using i_sq
private theorem ki_cube : (-i)^3 = i := by linear_combination -i*i_sq
private theorem c_sq : c^2 = i/2 := by dsimp [c]; linear_combination i_sq/4
private theorem c_cube : c^3 = (i-1)/4 := by
  rw [show c^3 = c*c^2 by ring, c_sq]
  dsimp [c]
  linear_combination i_sq/4
private theorem c_ne : c ≠ 0 := by
  intro h
  have t := c_sq
  rw [h] at t
  apply i_ne
  linear_combination -2*t

private def cmI : genusCurve.toAffine.Point →+ genusCurve.toAffine.Point :=
  shortCurveScaling (RingHom.id K) 4 4 (-i) (neg_ne_zero.mpr i_ne) (by
    simp only [RingHom.id_apply]
    rw [show (-i)^4 = ((-i)^2)^2 by ring, ki_sq]
    norm_num)

private def scaleToE : genusCurve.toAffine.Point →+ Rank.baseCurve.toAffine.Point :=
  shortCurveScaling (RingHom.id K) 4 (-1) c c_ne (by
    simp only [RingHom.id_apply]
    rw [show c^4 = (c^2)^2 by ring, c_sq]
    linear_combination -i_sq)

/-- The fixed group homomorphism S∘(1+[i]); S scales with (1+i)/2. -/
def tyzIsogeny : genusCurve.toAffine.Point →+ Rank.baseCurve.toAffine.Point :=
  scaleToE.comp ((AddMonoidHom.id _) + cmI)

private theorem scaleToE_kernel (P : genusCurve.toAffine.Point) (h : scaleToE P = 0) : P = 0 := by
  cases P with
  | zero => rfl
  | some x y hxy =>
    change Point.some _ _ _ = Point.zero at h
    contradiction

theorem tyzIsogeny_kernel_two (Q : genusCurve.toAffine.Point) (h : tyzIsogeny Q = 0) :
    (2:ℕ) • Q = 0 := by
  change scaleToE (Q + cmI Q) = 0 at h
  have heq := eq_neg_of_add_eq_zero_right (scaleToE_kernel _ h)
  cases Q with
  | zero => exact nsmul_zero 2
  | some x y hxy =>
    rw [Point.neg_some] at heq
    change Point.some _ _ _ = Point.some x (genusCurve.toAffine.negY x y) _ at heq
    have hy := (Point.some.inj heq).2
    change (-i)^3 * (RingHom.id K) y = genusCurve.toAffine.negY x y at hy
    simp only [ki_cube, RingHom.id_apply, negY, genusCurve, WeierstrassCurve.toAffine,
      zero_mul, sub_zero] at hy
    have hip : i+1 ≠ 0 := by
      intro hz
      have hneg : i = -1 := by linear_combination hz
      have hh := i_sq
      rw [hneg] at hh
      norm_num at hh
    have hyy : (i+1)*y=0 := by linear_combination hy
    have hy0 := (mul_eq_zero.mp hyy).resolve_left hip
    rw [two_nsmul]
    apply Point.add_of_Y_eq rfl
    simp [hy0, negY, genusCurve]


/-- Ordered affine coordinates; the identity has no affine coordinates. -/
def targetCoords : Rank.baseCurve.toAffine.Point → Option (K × K)
  | .zero => none
  | .some x y _ => some (x,y)

/-- In the normalized coordinates this is exactly TYZ's rational two-isogeny. -/
theorem tyzIsogeny_chart {x y : K} (hx : x ≠ 0) (hxy : genusCurve.toAffine.Nonsingular x y) :
    targetCoords (tyzIsogeny (.some x y hxy)) =
      some ((x^2+4)/(4*x), y*(x^2-4)/(8*x^2)) := by
  have hcurve : y^2 = x^3+4*x := by simpa [equation_iff, genusCurve] using hxy.1
  have hn : x ≠ (-i)^2*x := by
    rw [ki_sq, neg_one_mul]
    intro e
    apply hx
    linear_combination e/2
  change targetCoords (scaleToE (Point.some x y hxy + Point.some ((-i)^2*x) ((-i)^3*y) _)) = _
  erw [Point.add_of_X_ne (W := genusCurve.toAffine) (h₁ := hxy) (y₂ := (-i)^3*y) hn]
  change some (c^2 * _, c^3 * _) = _
  simp only [Option.some.injEq, Prod.mk.injEq, ki_sq, neg_one_mul, ki_cube, addX, addY,
    negAddY, negY, genusCurve, WeierstrassCurve.toAffine, zero_mul, add_zero, sub_zero,
    RingHom.id_apply, c_sq, c_cube]
  have hnx : x ≠ -x := by intro e; apply hx; linear_combination e/2
  erw [slope_of_X_ne (W := genusCurve.toAffine) (y₁ := y) (y₂ := i*y) hnx]
  rw [show x- -x=2*x by ring]
  have hi3 : i^3 = -i := by linear_combination i*i_sq
  have hi4 : i^4 = 1 := by rw [show i^4=(i^2)^2 by ring, i_sq]; norm_num
  constructor <;> field_simp [hx] <;> rw [hcurve] <;> ring_nf <;>
    simp only [i_sq, hi3, hi4] <;> ring


theorem tyzIsogeny_at_infinity : tyzIsogeny 0 = 0 := map_zero _

/-- The unique affine source point with X=0 is the remaining kernel point. -/
theorem tyzIsogeny_at_zero {y : K} (h : genusCurve.toAffine.Nonsingular 0 y) :
    tyzIsogeny (.some 0 y h) = 0 := by
  have hy : y^2 = 0 := by simpa [equation_iff, genusCurve] using h.1
  obtain rfl : y = 0 := (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hy
  have hcm : cmI (.some 0 0 h) = .some 0 0 h := by
    change Point.some _ _ _ = Point.some 0 0 h
    erw [Point.some.injEq]
    simp
  change scaleToE (Point.some 0 0 h + cmI (Point.some 0 0 h)) = 0
  erw [hcm, Point.add_of_Y_eq (h₁ := h) (h₂ := h) rfl (by simp [negY,genusCurve]), map_zero]

theorem tyzIsogeny_zero_iff {x y : K} (h : genusCurve.toAffine.Nonsingular x y) :
    tyzIsogeny (.some x y h) = 0 ↔ x = 0 := by
  constructor
  · intro hz
    by_contra hx
    have ha := tyzIsogeny_chart hx h
    rw [hz] at ha
    contradiction
  · rintro rfl
    exact tyzIsogeny_at_zero h

#print axioms tyzIsogeny_zero_iff
#print axioms tyzIsogeny_at_zero

#print axioms tyzIsogeny_chart

#print axioms tyzIsogeny
#print axioms tyzIsogeny_kernel_two

end
end ZInQBlueprint.TYZ

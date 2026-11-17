import TYZGaussianTorsion

/-! The two-primary subgroup of the integral TYZ curve over a field omitting √2. -/
namespace ZInQBlueprint.TYZ.Specialization.TraceAction
noncomputable section
attribute [local instance] Classical.decEq
open WeierstrassCurve.Affine

private def affineCoords : A → Option (K × K)
  | .zero => none
  | .some x y _ => some (x,y)

private theorem y_ne_negY {x y : K} (hy : y ≠ 0) : y ≠ genusCurve.toAffine.negY x y := by
  intro h
  simp [negY, genusCurve] at h
  exact hy (by linear_combination h / 2)

private theorem y_of_double_zero {x y : K} (h : genusCurve.toAffine.Nonsingular x y)
    (h2 : (2:ℕ) • (.some x y h : A) = 0) : y = 0 := by
  by_contra hne
  rw [two_nsmul,Point.add_self_of_Y_ne (y_ne_negY hne)] at h2
  exact Point.some_ne_zero _ h2

private theorem sqrtTwo_mem_of_square {F : SubfieldQ} {a : K} (ha : a ∈ F) (h : a^2 = 2) :
    sqrtDivisor 2 ∈ F := by
  have eq : a^2 = (sqrtDivisor 2)^2 := h.trans (by simpa using (sqrtDivisor_sq 2).symm)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp eq with eq | eq
  · rwa [←eq]
  · rw [eq] at ha
    simpa using F.neg_mem ha

/-- If a point on y²=x³+4x doubles to a nonzero two-torsion point other than
(0,0), its field of definition contains a square root of two. -/
theorem sqrtTwo_mem_of_noncentral_half {F : SubfieldQ} {P : A} (hP : P ∈ pointsOver F)
    {t : K} (ht : genusCurve.toAffine.Nonsingular t 0) (ht0 : t ≠ 0)
    (h2 : (2:ℕ) • P = .some t 0 ht) : sqrtDivisor 2 ∈ F := by
  have htEq : (0:K)^2 = t^3+4*t := by simpa [equation_iff,genusCurve] using ht.1
  have htSq : t^2 = -4 := by
    have fac : t*(t^2+4) = 0 := by linear_combination -htEq
    have := (mul_eq_zero.mp fac).resolve_left ht0
    linear_combination this
  have htF : t ∈ F := by
    have hm := (pointsOver F).nsmul_mem hP 2
    rw [h2] at hm
    exact ((some_mem_pointsOver F _ _ ht).mp hm).1
  cases P with
  | zero =>
    change (2:ℕ) • (0:A) = _ at h2
    rw [nsmul_zero] at h2
    exact False.elim (Point.some_ne_zero _ h2.symm)
  | some x y h =>
    have hxF := ((some_mem_pointsOver F x y h).mp hP).1
    have hy : y ≠ 0 := by
      rintro rfl
      rw [two_nsmul,Point.add_self_of_Y_eq (by simp [negY,genusCurve])] at h2
      exact Point.some_ne_zero _ h2.symm
    have he := congrArg affineCoords h2
    rw [two_nsmul,Point.add_self_of_Y_ne (y_ne_negY hy)] at he
    have ex := (Prod.mk.inj (Option.some.inj he)).1
    change genusCurve.toAffine.addX x x (genusCurve.toAffine.slope x x y y) = t at ex
    rw [slope_of_Y_ne rfl (y_ne_negY hy)] at ex
    simp [addX,negY,genusCurve] at ex
    field_simp [hy] at ex
    have eq : y^2 = x^3+4*x := by simpa [equation_iff,genusCurve] using h.1
    have sqZero : (x^2-2*t*x+4)^2=0 := by
      linear_combination ex + (8*x+4*t)*eq + 4*x^2*htSq
    have quad := (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp sqZero
    apply sqrtTwo_mem_of_square (F.div_mem (F.sub_mem hxF htF) htF)
    field_simp [ht0]
    linear_combination quad - htSq

/-- The four-torsion over a field omitting √2 is contained in A[(1+i)³]. -/
theorem gaussian_of_four {F : SubfieldQ} (hF : sqrtDivisor 2 ∉ F)
    {P : A} (hP : P ∈ pointsOver F) (h4 : (4:ℕ) • P = 0) :
    onePlusI (onePlusI (onePlusI P)) = 0 := by
  apply (onePlusI_cube_kernel P).mpr
  cases h2 : (2:ℕ) • P with
  | zero => exact Or.inl rfl
  | some t s ht =>
    have hd : (2:ℕ) • (.some t s ht : A) = 0 := by
      rw [←h2,←mul_nsmul]; exact h4
    obtain rfl := y_of_double_zero ht hd
    by_cases ht0 : t = 0
    · subst t; exact Or.inr rfl
    · exact (hF (sqrtTwo_mem_of_noncentral_half hP ht ht0 h2)).elim

private theorem cmI_square (P : A) : multiplyI (multiplyI P) = -P := by
  cases P with
  | zero => change multiplyI (multiplyI (0:A)) = -(0:A); simp
  | some x y h =>
    let i := Rank.sqrtMinus 1
    have sq : i^2 = -1 := by simpa [i] using Rank.sqrtMinus_sq 1
    have cube : (-i)^3=i := by linear_combination -i*sq
    change Point.some ((-i)^2*((-i)^2*x)) ((-i)^3*((-i)^3*y)) _ =
      Point.some x (genusCurve.toAffine.negY x y) _
    erw [Point.some.injEq]
    rw [cube,neg_sq,sq]
    constructor
    · ring
    · simp only [negY,genusCurve,WeierstrassCurve.toAffine,zero_mul,sub_zero]
      linear_combination y*sq

private theorem gaussian_square (P : A) : onePlusI (onePlusI P) = multiplyI ((2:ℕ) • P) := by
  change P + multiplyI P + multiplyI (P + multiplyI P) = _
  rw [map_add,cmI_square,map_nsmul,two_nsmul]
  abel

private theorem gaussian_fourth (P : A) :
    onePlusI (onePlusI (onePlusI (onePlusI P))) = -((4:ℕ) • P) := by
  rw [gaussian_square,gaussian_square,←map_nsmul,cmI_square,←mul_nsmul]

/-- Over any intermediate field containing i and omitting √2, all points of
two-power order on A already lie in the kernel of (1+i)³. -/
theorem gaussian_of_twoPower {F : SubfieldQ} (hi : Rank.sqrtMinus 1 ∈ F)
    (hF : sqrtDivisor 2 ∉ F) {P : A} (hP : P ∈ pointsOver F) (k : ℕ)
    (hkill : (2^k : ℕ) • P = 0) : onePlusI (onePlusI (onePlusI P)) = 0 := by
  induction k generalizing P with
  | zero =>
    have hz : P = 0 := by simpa using hkill
    simp [hz]
  | succ k ih =>
    have h2 : onePlusI (onePlusI (onePlusI ((2:ℕ) • P))) = 0 := by
      apply ih ((pointsOver F).nsmul_mem hP 2)
      rwa [←mul_nsmul,←pow_succ']
    have h4 : (4:ℕ) • onePlusI P = 0 := by
      rw [←map_nsmul,show 4=2*2 by decide,mul_nsmul]
      rcases (onePlusI_cube_kernel _).mp h2 with e | e
      · rw [e,map_zero]
      · rw [e]
        exact (one_plus_i_kernel twiceCusp).mpr (Or.inr rfl)
    have hmem : onePlusI P ∈ pointsOver F := (pointsOver F).add_mem hP (multiplyI_mem hi hP)
    have hh := gaussian_of_four hF hmem h4
    rw [gaussian_fourth,neg_eq_zero] at hh
    exact gaussian_of_four hF hP hh

end
end ZInQBlueprint.TYZ.Specialization.TraceAction
#print axioms ZInQBlueprint.TYZ.Specialization.TraceAction.sqrtTwo_mem_of_noncentral_half
#print axioms ZInQBlueprint.TYZ.Specialization.TraceAction.gaussian_of_four
#print axioms ZInQBlueprint.TYZ.Specialization.TraceAction.gaussian_of_twoPower

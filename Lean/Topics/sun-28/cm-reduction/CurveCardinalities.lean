import CMPointCounts

namespace Sun28.CMReduction
open ZInQ ZInQ.Density ManuscriptV15.Arithmetic

/-- There is an oriented root at which the nonsingular groups themselves have the stated orders. -/
theorem exists_oriented_cardinalities {p : ℕ} [Fact p.Prime] {z : Gaussian} (norm : gaussianNorm z=p)
    (r16 : gaussianCongruent 16 z (9,0)) (r7 : gaussianCongruent 7 z (1,3)) :
    ∃ r : ZMod p, r^2=2 ∧
      Nat.card (shortCurve (-(3-r)^2)).toAffine.Point=adjacentNorm z true ∧
      Nat.card (shortCurve (-(3+r)^2)).toAffine.Point=adjacentNorm z false := by
  obtain ⟨r,hr,left,right⟩:=exists_oriented_root norm r16 r7
  have cls:=selected_class norm r16 r7
  let _ : NeZero (2:ZMod p) := ⟨ZInQ.Mult.two_ne_zero_zmod cls.ne_two⟩
  have product : (3-r)*(3+r)=7 := by linear_combination -hr
  have nz : (3-r)*(3+r)≠0 := by rw [product]; exact seven_ne_zero cls
  let _ : (shortCurve (-(3-r)^2)).IsElliptic :=
    shortCurve_isElliptic (neg_ne_zero.mpr (pow_ne_zero _ (left_ne_zero_of_mul nz)))
  let _ : (shortCurve (-(3+r)^2)).IsElliptic :=
    shortCurve_isElliptic (neg_ne_zero.mpr (pow_ne_zero _ (right_ne_zero_of_mul nz)))
  exact ⟨r,hr,(card_point_shortCurve p _).trans left,(card_point_shortCurve p _).trans right⟩

end Sun28.CMReduction
#print axioms Sun28.CMReduction.exists_oriented_cardinalities

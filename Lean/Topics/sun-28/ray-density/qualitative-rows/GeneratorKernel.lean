import ReducedGenerator

namespace Sun28.QualitativeRows
open ZInQ ZInQ.Mult Sun28.Scalar Sun28.ScalarTrace Sun28.Ordinary Sun28.Forward Sun28.WitnessIndices
open Sun28.SelectedTrace WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
open private denominator finite_elliptic from ReducedGenerator

private theorem x_formula : generatorX sqrt2 * 8 = Zs.toK0 (57-28*sqrt2Z) := by
  simp [generatorX,map_ofNat]
  ring

private theorem y_formula : generatorY sqrt2 * 32 = Zs.toK0 (-660+417*sqrt2Z) := by
  simp [generatorY,map_ofNat]
  ring

/-- Divisibility by the order of the actual reduced point is sufficient to put
a multiple of the published point in the formal kernel at the chosen prime. -/
theorem anchor_from_period {p : ℕ} [Fact p.Prime] (large : 65<p)
    {r : ZMod p} (hr : r^2=2) {π : Zs} (hπ : Prime π)
    (kernel : ∀ a, residueAt r hr a=0 ↔ π∣a) {h : ℤ}
    (order : (pointPeriod large hr:ℤ)∣h) :
    h • paperGenerator sqrt2_sq ∈ W1 (vP π hπ) (-(3-sqrt2)^2) := by
  let b : K0 := -(3-sqrt2)^2
  let B : Zs := -(3-sqrt2Z)^2
  let ρ := residueAt r hr
  have lift : Zs.toK0 B=b := by simp [B,b,map_ofNat]
  have bInt : VGe π 0 b := by rw [←lift];exact Or.inr (vp_nonneg hπ B)
  have bRes : res π ρ b= -(3-r)^2 := by
    rw [←lift,res_toK0 hπ ρ kernel]
    simp only [B,map_neg,map_pow,map_sub,map_ofNat]
    have root : ρ sqrt2Z=r := by simp [ρ,sqrt2Z]
    rw [root]
  have three : (3-sqrt2:K0)≠0 := by
    intro e
    have same : sqrt2=3 := (sub_eq_zero.mp e).symm
    have two:=sqrt2_sq
    rw [same] at two
    norm_num at two
  let _ : (shortCurve b).IsElliptic := shortCurve_isElliptic (neg_ne_zero.mpr (pow_ne_zero _ three))
  let _ := finite_elliptic large hr
  have den (k : ℕ) (pos : 0<k) (small : k≤32) : ¬π∣(k:Zs) := by
    intro d
    have zero:= (kernel (k:Zs)).mpr d
    rw [map_natCast] at zero
    exact denominator large k pos small zero
  have hx : VGe π 0 (generatorX sqrt2) := by
    have vzero : vp π (8:K0)=0 := (vp_eq_zero_iff hπ (by norm_num : (8:Zs) ≠ 0)).mpr
      (den 8 (by decide) (by decide))
    have int := (vge_toK0 hπ (57-28*sqrt2Z)).div hπ (by norm_num : (8:K0)≠0)
    rw [vzero, sub_zero] at int
    exact (eq_div_iff (by norm_num : (8:K0)≠0)).mpr x_formula ▸ int
  have rx : res π ρ (generatorX sqrt2)=redX r := by
    rw [res_eq ρ kernel (a:=57-28*sqrt2Z) (b:=(8:Zs)) (den 8 (by decide) (by decide))
      (by simpa only [map_ofNat] using x_formula)]
    simp [redX,ρ,sqrt2Z,sub_eq_add_neg]
  have ry : res π ρ (generatorY sqrt2)=redY r := by
    rw [res_eq ρ kernel (a:=-660+417*sqrt2Z) (b:=(32:Zs)) (den 32 (by decide) (by decide))
      (by simpa only [map_ofNat] using y_formula)]
    simp [redY,ρ,sqrt2Z]
  let P : (shortCurve b).toAffine.Point:=paperGenerator sqrt2_sq
  have redP : red hπ ρ kernel bInt bRes P=reducedPoint large hr := by
    change red hπ ρ kernel bInt bRes (Point.some (generatorX sqrt2) (generatorY sqrt2) (generator_on_curve sqrt2_sq)) = _
    simp only [red, dite_eq_left hx]
    simp only [reducedPoint, Point.mk, rx, ry]
  have redZero : red hπ ρ kernel bInt bRes (h • P)=0 := by
    have reduced := addOrderOf_dvd_iff_zsmul_eq_zero.mp order
    rw [←redHom_apply,map_zsmul,redHom_apply,redP]
    exact reduced
  change h • P ∈ W1 (vP π hπ) b
  generalize h • P=Z at redZero ⊢
  cases Z with
  | zero => exact trivial
  | some x y he =>
    by_cases integral : VGe π 0 x
    · rw [red_some_of_vge hπ ρ kernel bInt bRes he integral] at redZero
      exact False.elim ((Point.some_ne_zero _) redZero)
    · have xn : x≠0 := fun e => integral (Or.inl e)
      change vP π hπ x<0
      rw [vP_apply hπ xn]
      exact WithTop.coe_lt_coe.mpr (lt_of_not_ge ((vge_iff xn).not.mp integral))

end
end Sun28.QualitativeRows
#print axioms Sun28.QualitativeRows.anchor_from_period

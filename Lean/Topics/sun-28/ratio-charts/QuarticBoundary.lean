import ConductorProjection28

namespace Sun28.PointLifts
noncomputable section

/-- A zero ordinate on either normalized conic gives the old torsion section. -/
theorem one_of_zero_conic {b θ s z h j : ℚ} (bp : 0<b) (tn : θ≠0)
    (F : ConicFibre b θ s z h j) (root : h=0 ∨ j=0) : PrescribedPoints.OneQuartic b θ := by
  apply (PrescribedPoints.zero_pair_iff_one bp tn).mp
  let l:=b/z
  let v:=s^2/θ*z
  have L : l*z=b := by dsimp [l];field_simp [F.z_ne]
  have V : (l*θ)*v=b*s^2 := by dsimp [l,v];field_simp [F.z_ne]
  have g : (v-1)*(v+3)=b*j^2 := F.second
  refine ⟨l,1,s,b*l*h,b*s*l*θ*j,div_ne_zero bp.ne' F.z_ne,one_ne_zero,F.s_ne,?_,?_,?_⟩
  · rcases root with h|j
    · left;simp [h]
    · right;simp [j]
  · norm_num
    calc
      (b*l*h)^2=b*l^2*(b*h^2):=by ring
      _=b*l^2*((z-1)*(z+3)):=by rw [F.first]
      _=b*(b-l)*(b+3*l):=by linear_combination b*(l*z+b+2*l)*L
  · calc
      (b*s*l*θ*j)^2=(b*s^2)*(l*θ)^2*(b*j^2):=by ring
      _=(b*s^2)*(l*θ)^2*((v-1)*(v+3)):=by rw [g]
      _=(b*s^2)*(b*s^2-l*θ)*(b*s^2+3*(l*θ)):=by
        linear_combination (b*s^2)*(l*θ*v+b*s^2+2*(l*θ))*V

/-- In the physical quartic a projective coordinate zero kills the first
ordinate and W=0 kills the second. All three give OneQuartic. -/
theorem one_of_boundary {b θ s U V W : ℚ} (bp : 0<b) (tn : θ≠0) (sn : s≠0)
    (L : U^2-b*V^2≠0) (E : b*W^2=singlePolynomial b θ s U V)
    (root : U=0 ∨ V=0 ∨ W=0) : PrescribedPoints.OneQuartic b θ := by
  let H := U^2+3*b*V^2
  let D := U^2-b*V^2
  have num : H≠0 := by
    dsimp [H]
    by_cases un : U=0
    · have vn : V≠0 := by intro e;apply L;simp [un,e]
      positivity
    · positivity
  have den : D≠0 := L
  have det : θ*D≠0 := mul_ne_zero tn den
  have f : (H/D-1)*(H/D+3)=b*(4*U*V/D)^2 := by dsimp [H,D] at *;field_simp;ring
  have g : (s^2/θ*(H/D)-1)*(s^2/θ*(H/D)+3)=b*(W/(θ*D))^2 := by
    change b*W^2=(s^2*H-θ*D)*(s^2*H+3*θ*D) at E
    field_simp
    linear_combination -E
  apply one_of_zero_conic bp tn (show ConicFibre b θ s (H/D) (4*U*V/D) (W/(θ*D)) from
    ⟨sn,div_ne_zero num den,f,g⟩)
  rcases root with u|v|w
  · left;simp [u]
  · left;simp [v]
  · right;simp [w]

theorem integral_boundary {b θ n m U V Y : ℤ} (bp : 0<b) (tp : 0<θ)
    (nn : n≠0) (mn : m≠0) (L : U^2-b*V^2≠0)
    (E : Y^2=b*leftForm b (n^2) (θ*m^2) U V*rightForm b (n^2) (θ*m^2) U V)
    (root : U=0 ∨ V=0 ∨ Y=0) : PrescribedPoints.OneQuartic (b:ℚ) θ := by
  have B : (b:ℚ)≠0 := by exact_mod_cast bp.ne'
  have M : (m:ℚ)≠0 := by exact_mod_cast mn
  have YQ : (Y:ℚ)^2=b*leftForm (b:ℚ) ((n:ℚ)^2) (θ*(m:ℚ)^2) U V*
      rightForm (b:ℚ) ((n:ℚ)^2) (θ*(m:ℚ)^2) U V := by
    unfold leftForm rightForm at *;exact_mod_cast E
  apply one_of_boundary (s:=(n:ℚ)/m) (U:=(U:ℚ)) (V:=(V:ℚ)) (W:=(Y:ℚ)/(b*m^2))
    (by exact_mod_cast bp) (by exact_mod_cast tp.ne') (div_ne_zero (by exact_mod_cast nn) M)
    (by exact_mod_cast L)
  · apply (cleared_quartic _ _ _ _ _ _ _ B M).mpr
    rw [mul_comm (b*m^2:ℚ),div_mul_cancel₀ _ (mul_ne_zero B (pow_ne_zero 2 M))]
    exact YQ
  · rcases root with u|v|y
    · left;exact_mod_cast u
    · right;left;exact_mod_cast v
    · right;right;simp [y]

end
end Sun28.PointLifts
#print axioms Sun28.PointLifts.one_of_zero_conic
#print axioms Sun28.PointLifts.one_of_boundary
#print axioms Sun28.PointLifts.integral_boundary

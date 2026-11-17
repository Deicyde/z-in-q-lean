import CompactRealCurve

/-! Separation by the degree-zero functions XᵢXⱼ/∑Xₖ². -/
namespace Sun28.RealCharts
open WeierstrassCurve
open scoped WeierstrassCurve.Projective Sun28.RealCharts
noncomputable section
private abbrev V := Fin 3 → ℝ

private def sumSquares (v : V) : ℝ := v 0^2 + v 1^2 + v 2^2

private theorem sumSquares_pos {v : V} (live : v≠0) : 0<sumSquares v := by
  by_contra! h
  unfold sumSquares at h
  apply live
  funext i
  fin_cases i
  · change v 0=0
    by_contra n
    nlinarith [sq_pos_of_ne_zero n,sq_nonneg (v 1),sq_nonneg (v 2)]
  · change v 1=0
    by_contra n
    nlinarith [sq_nonneg (v 0),sq_pos_of_ne_zero n,sq_nonneg (v 2)]
  · change v 2=0
    by_contra n
    nlinarith [sq_nonneg (v 0),sq_nonneg (v 1),sq_pos_of_ne_zero n]

private def coefficient (i j : Fin 3) : Plane → ℝ :=
  Quotient.lift (fun v : V => v i*v j / sumSquares v) (by
    rintro x y ⟨u,rfl⟩
    have scale : sumSquares (u • y)=(u:ℝ)^2*sumSquares y := by
      change ((u:ℝ)*y 0)^2+((u:ℝ)*y 1)^2+((u:ℝ)*y 2)^2=_*(_+_+_)
      ring
    rw [scale]
    change ((u:ℝ)*y i)*((u:ℝ)*y j)/(_^2*sumSquares y)=_
    by_cases zero : sumSquares y=0
    · simp [zero]
    · field_simp [zero,u.ne_zero])

private theorem coefficient_continuousAt (i j : Fin 3) {v : V} (live : v≠0) :
    ContinuousAt (coefficient i j) (Quotient.mk (MulAction.orbitRel ℝˣ V) v) := by
  have quotient : IsOpenQuotientMap (Quotient.mk (MulAction.orbitRel ℝˣ V)) :=
    MulAction.isOpenQuotientMap_quotientMk
  apply quotient.continuousAt_comp_iff.mp
  change ContinuousAt (fun v : V => v i*v j / sumSquares v) v
  apply ((continuous_apply i).mul (continuous_apply j)).continuousAt.div _ (sumSquares_pos live).ne'
  unfold sumSquares
  fun_prop

private theorem affine_coefficient (W : WeierstrassCurve ℝ) (Q : W.toAffine.Point) (i j : Fin 3) :
    ContinuousAt (fun Q : W.toAffine.Point => coefficient i j Q.toProjective.point) Q := by
  have cont : ContinuousAt (coefficient i j) Q.toProjective.point := by
    cases Q with
    | zero =>
      apply coefficient_continuousAt (v:=![0,1,0])
      intro zero
      have y:=congrFun zero (1:Fin 3)
      norm_num at y
    | some x y on =>
      apply coefficient_continuousAt (v:=![x,y,1])
      intro zero
      have z:=congrFun zero (2:Fin 3)
      norm_num at z
  exact ContinuousAt.comp (f:=fun Q : W.toAffine.Point => Q.toProjective.point) cont (projective_continuous W).continuousAt

private def coordinates (W : WeierstrassCurve ℝ) (Q : W.toAffine.Point) : Fin 3 → Fin 3 → ℝ :=
  fun i j => coefficient i j Q.toProjective.point

private theorem coordinates_injective (W : WeierstrassCurve ℝ) : Function.Injective (coordinates W) := by
  intro Q R h
  have eq (i j : Fin 3) := congrFun (congrFun h i) j
  cases Q with
  | zero =>
    cases R with
    | zero => rfl
    | some x y on =>
      have z:=eq 2 2
      change 0*0 / ((0:ℝ)^2+1^2+0^2)=1*1/(x^2+y^2+1^2) at z
      have pos : 0<x^2+y^2+1 := by positivity
      simp at z
      exact (pos.ne' z.symm).elim
  | some x y on =>
    cases R with
    | zero =>
      have z:=eq 2 2
      change 1*1/(x^2+y^2+1^2)=0*0 / ((0:ℝ)^2+1^2+0^2) at z
      have pos : 0<x^2+y^2+1 := by positivity
      simp [pos.ne'] at z
    | some u v on' =>
      have d:=eq 2 2
      have a:=eq 0 2
      have b:=eq 1 2
      change 1*1/(x^2+y^2+1^2)=1*1/(u^2+v^2+1^2) at d
      change x*1/(x^2+y^2+1^2)=u*1/(u^2+v^2+1^2) at a
      change y*1/(x^2+y^2+1^2)=v*1/(u^2+v^2+1^2) at b
      have sp : 0<u^2+v^2+1 := by positivity
      simp only [mul_one,one_pow,one_div,inv_inj] at d
      simp only [mul_one,one_pow,d,div_left_inj' sp.ne'] at a b
      rw [Affine.Point.some.injEq]
      exact ⟨a,b⟩

/-- All real Weierstrass point spaces carry Hausdorff projective topologies, including singular models. -/
theorem elliptic_t2Space (W : WeierstrassCurve ℝ) : T2Space W.toAffine.Point := by
  apply T2Space.of_injective_continuous (coordinates_injective W)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_iff_continuousAt.mpr (fun Q => affine_coefficient W Q i j)

end
end Sun28.RealCharts
#print axioms Sun28.RealCharts.elliptic_t2Space

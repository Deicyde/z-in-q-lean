import ZInQKernel.Model.Generator.Certificate

/-! Sun's four equations for an odd multiple on the fixed curve over ℚ(√2). -/
namespace Sun28.WitnessIndices
open ZInQ ZInQ.Descent WeierstrassCurve WeierstrassCurve.Affine
noncomputable section

abbrev CPoint := curveC.toAffine.Point

/-- The distinguished point P of Sun. -/
def P : CPoint := (2 : ℕ) • pointR

/-- Sun, Lemma 3.2, with the nonzero guard on h. -/
def OddChart (Q : CPoint) : Prop :=
  ∃ (x y : K0) (onCurve : curveC.toAffine.Nonsingular x y),
    Q = .some x y onCurve ∧ ∃ h j u v : K0, h ≠ 0 ∧ h^2 = x ∧ y = h*j ∧
      u^2 = 2*(x+j) ∧ u*h+x+j = epsilon*v^2

theorem chart_half {Q : CPoint} (chart : OddChart Q) :
    ∃ B : CPoint, (2 : ℕ) • B = Q ∧ kummer (-delta^2) B = sqc epsilon := by
  obtain ⟨x,y,onCurve,rfl,h,j,u,v,hn,hh,hy,hu,hv⟩ := chart
  have xn : x ≠ 0 := hh ▸ pow_ne_zero 2 hn
  have he := (curveC_equation_iff x y).1 onCurve.1
  have hj : j^2 = x^2-delta^2 := by
    apply mul_left_cancel₀ xn
    calc
      x*j^2 = (h*j)^2 := by rw [← hh]; ring
      _ = x*(x^2-delta^2) := by rw [← hy]; linear_combination he
  let X := u*h+x+j
  let Y := X*u
  have quad : X^2-u^2*X = delta^2 := by
    calc
      X^2-u^2*X = (u*h)^2-(x+j)^2 := by dsimp [X]; rw [hu]; ring
      _ = delta^2 := by rw [mul_pow,hu,hh]; linear_combination -hj
  have Xn : X ≠ 0 := by
    intro emp
    rw [emp] at quad
    simp only [zero_pow (by decide : (2:ℕ)≠0),mul_zero,sub_zero] at quad
    exact (pow_ne_zero 2 delta_ne_zero) quad.symm
  have un : u ≠ 0 := by
    intro emp
    have hjx : x+j = 0 := by rw [emp] at hu; linear_combination -hu / 2
    apply Xn
    dsimp [X]
    rw [emp,zero_mul,zero_add,hjx]
  have Yn : Y ≠ 0 := mul_ne_zero Xn un
  have onHalf : curveC.toAffine.Nonsingular X Y := by
    apply equation_iff_nonsingular.mp ((curveC_equation_iff X Y).2 ?_)
    dsimp [Y]
    linear_combination -X*quad
  refine ⟨.some X Y onHalf,?_,?_⟩
  · have hyne : Y ≠ curveC.toAffine.negY X Y := by
      rw [curveC,shortCurve_negY]
      intro eq
      apply Yn
      linear_combination eq / 2
    have slope : curveC.toAffine.slope X X Y Y = h+u := by
      rw [Affine.slope_of_Y_ne rfl hyne]
      simp only [curveC,shortCurve_negY,shortCurve_a₁,shortCurve_a₂,shortCurve_a₄]
      have den : Y - -Y ≠ 0 := by
        intro ez
        apply Yn
        linear_combination ez / 2
      apply (div_eq_iff den).2
      have hxw : 2*X = 2*u*h+u^2 := by dsimp [X]; linear_combination -hu
      dsimp [Y]
      linear_combination quad + X*hxw
    have xx : (h+u)^2-2*X=x := by dsimp [X]; linear_combination hh + hu
    have yy : (h+u)*(X-x)-Y=y := by dsimp [Y,X]; linear_combination u*hh - hy
    rw [two_nsmul,Point.add_self_of_Y_ne hyne]
    simp only [Point.some.injEq,Affine.addY,Affine.negAddY,Affine.addX,slope]
    simp only [curveC,shortCurve_negY,shortCurve_a₁,shortCurve_a₂]
    constructor
    · rw [← xx]; ring
    · calc
        _ = (h+u)*(X-((h+u)^2-2*X))-Y := by ring
        _ = y := by rw [xx,yy]
  · have vn : v ≠ 0 := by
      intro emp
      apply Xn
      change u*h+x+j = 0
      simpa [emp] using hv
    calc
      _ = sqc X := kummer_some_of_ne _ onHalf Xn
      _ = sqc epsilon := by rw [show X=epsilon*v^2 from hv,sqc_mul_sq _ vn]

/-- The public Kummer sign computation rules out an even index for an accepted chart. -/
theorem odd_of_chart {k : ℤ} (chart : OddChart (k • P)) : Odd k := by
  obtain ⟨B,double,kummerB⟩ := chart_half chart
  by_contra contra
  rw [Int.not_odd_iff_even] at contra
  obtain ⟨j,rfl⟩ := contra
  let T : CPoint := B - (j+j) • pointR
  have T2 : (2:ℕ) • T=0 := by
    dsimp [T]
    rw [nsmul_sub,double]
    have comm (n : ℤ) : (2:ℕ) • (n • pointR) = n • P := by
      rw [P,two_nsmul,two_nsmul,zsmul_add]
    rw [comm,sub_self]
  let S' : (shortCurve (-delta^2)).toAffine.Point := pointR
  let T' : (shortCurve (-delta^2)).toAffine.Point := T
  have decomp : B=(j+j) • S' + T' := by
    change B = (j+j) • pointR + (B-(j+j) • pointR)
    rw [add_comm,sub_add_cancel]
  have hw := congrArg (kummer (-delta^2)) decomp
  have twice : kummer (-delta^2) ((j+j) • S')=1 := by
    rw [kummer_zsmul,zpow_add,SqClass.mul_self]
  rw [kummerB,kummer_add (b := -delta^2),twice,one_mul] at hw
  have signs := congrArg (fun a => (sqcInvariant a).2) hw
  simp only [sqcInvariant_epsilon] at signs
  rcases kummerC_two_torsion_signs T2 with same | same <;>
    rw [same] at signs <;> revert signs <;> decide

#print axioms chart_half
#print axioms odd_of_chart
end
end Sun28.WitnessIndices

import WitnessIndices

/-! The reverse implication and finiteness in Sun's odd-index test. -/
namespace Sun28.WitnessIndices
open ZInQ ZInQ.Descent WeierstrassCurve WeierstrassCurve.Affine
noncomputable section

/-- Recover all four chart variables from a half with Kummer class ε. -/
private theorem chart_of_half {X Y : K0} (onCurve : curveC.toAffine.Nonsingular X Y)
    (Yn : Y ≠ 0) (sqclass : kummer (-delta^2) (.some X Y onCurve) = sqc epsilon) :
    OddChart ((2:ℕ) • (Point.some X Y onCurve : CPoint)) := by
  have he := (curveC_equation_iff X Y).1 onCurve.1
  have Xn : X≠0 := by
    intro hz
    rw [hz] at he
    simp at he
    exact Yn he
  have kx : sqc X = sqc epsilon := (kummer_some_of_ne _ onCurve Xn).symm.trans sqclass
  obtain ⟨v,_,xv⟩ := (sqc_eq_sqc_iff Xn epsilon_ne_zero).1 kx
  let u := Y/X
  let h := (X-u^2/2)/u
  let j := u^2/2 - h^2
  have un : u≠0 := div_ne_zero Yn Xn
  have Yu : Y=X*u := by dsimp [u]; field_simp [Xn]
  have hx : 2*X=2*u*h+u^2 := by dsimp [h]; field_simp [un]; ring
  have quad : X^2-u^2*X=delta^2 := by
    apply mul_left_cancel₀ Xn
    rw [Yu] at he
    linear_combination -he
  have hn : h≠0 := by
    intro hz
    have vanish : X^2 + delta^2 = 0 := by rw [hz] at hx; linear_combination X*hx-quad
    have dv : K0.embPlus delta ≠ 0 := (map_ne_zero K0.embPlus).2 delta_ne_zero
    have realEq := congrArg K0.embPlus vanish
    rw [map_add,map_pow,map_pow,map_zero] at realEq
    nlinarith [sq_nonneg (K0.embPlus X),sq_pos_of_ne_zero dv]
  have hyne : Y ≠ curveC.toAffine.negY X Y := by
    rw [curveC,shortCurve_negY]
    intro hh
    exact Yn (by linear_combination hh / 2)
  have slope : curveC.toAffine.slope X X Y Y = h+u := by
    rw [Affine.slope_of_Y_ne rfl hyne]
    simp only [curveC,shortCurve_negY,shortCurve_a₁,shortCurve_a₂,shortCurve_a₄]
    have den : Y - -Y ≠ 0 := by intro e; apply Yn; linear_combination e / 2
    apply (div_eq_iff den).2
    rw [Yu]
    linear_combination quad+X*hx
  have xx : (h+u)^2-2*X=h^2 := by linear_combination -hx
  have yy : (h+u)*(X-h^2)-Y=h*j := by rw [Yu]; dsimp [j]; linear_combination h*hx/2
  rw [two_nsmul,Point.add_self_of_Y_ne hyne]
  refine ⟨_,_,_,rfl,h,j,u,v,hn,?_,?_,?_,?_⟩
  all_goals simp only [Affine.addY,Affine.negAddY,Affine.addX,slope]
  all_goals simp only [curveC,shortCurve_negY,shortCurve_a₁,shortCurve_a₂]
  · linear_combination -xx
  · calc
      _ = (h+u)*(X-((h+u)^2-2*X))-Y := by ring
      _ = _ := by rw [xx, yy]
  · dsimp [j]; linear_combination -2*xx
  · dsimp [j]; linear_combination xx - hx/2 + xv

theorem chart_of_odd {k : ℤ} (odd : Odd k) : OddChart (k • P) := by
  have kn : k≠0 := fun hk => by simp [hk] at odd
  have dbl : (2:ℕ) • (k • pointR) = k • P := by rw [P,two_nsmul,two_nsmul,zsmul_add]
  have nz : (2:ℕ) • (k • pointR) ≠ 0 := by
    rw [dbl]
    intro h
    exact kn (index_injective (h.trans (zero_zsmul P).symm))
  have km : kummer (-delta^2) (k • pointR) = sqc epsilon := by
    obtain ⟨j,rfl⟩ := odd
    let R' : (shortCurve (-delta^2)).toAffine.Point := pointR
    change kummer (-delta^2) ((2*j+1) • R')=sqc epsilon
    rw [kummer_zsmul]
    rw [show kummer (-delta^2) R'=sqc epsilon from kummerC_pointR]
    rw [zpow_add,zpow_mul,show (sqc epsilon)^(2:ℤ)=1 by norm_cast; exact SqClass.pow_two _]
    simp
  rw [← dbl]
  cases e : k • pointR with
  | zero => rw [e] at nz; exact False.elim (nz (nsmul_zero ..))
  | some X Y onCurve =>
    have Yn : Y≠0 := by
      intro hz
      apply nz
      rw [e]
      exact (shortCurve_two_nsmul_some_eq_zero_iff (A := -delta^2) onCurve).2 hz
    exact chart_of_half onCurve Yn (e ▸ km)

theorem odd_chart_iff (k : ℤ) : OddChart (k • P) ↔ Odd k := ⟨odd_of_chart,chart_of_odd⟩

/-- Enumeration from the three quadratic equations. The second coordinate is y/h. -/
def chartChoices (x y : K0) : Finset (K0 × K0 × K0 × K0) :=
  (Polynomial.nthRoots 2 x).toFinset.biUnion fun h =>
    (Polynomial.nthRoots 2 (2*(x+y/h))).toFinset.biUnion fun u =>
      (Polynomial.nthRoots 2 ((u*h+x+y/h)/epsilon)).toFinset.image fun v => (h,y/h,u,v)

theorem choice_mem {x y h j u v : K0} (hn : h≠0) (hx : h^2=x)
    (hy : y=h*j) (hu : u^2=2*(x+j)) (hv : u*h+x+j=epsilon*v^2) :
    (h,j,u,v) ∈ chartChoices x y := by
  have hj : y/h=j := by rw [hy]; field_simp
  rw [chartChoices]
  refine Finset.mem_biUnion.mpr ⟨h,?_,Finset.mem_biUnion.mpr ⟨u,?_,Finset.mem_image.mpr ⟨v,?_,?_⟩⟩⟩
  · exact Multiset.mem_toFinset.mpr ((Polynomial.mem_nthRoots (by decide)).2 hx)
  · rw [hj]; exact Multiset.mem_toFinset.mpr ((Polynomial.mem_nthRoots (by decide)).2 hu)
  · rw [hj]; apply Multiset.mem_toFinset.mpr ((Polynomial.mem_nthRoots (by decide)).2 ?_)
    apply (eq_div_iff epsilon_ne_zero).2
    linear_combination -hv
  · rw [hj]

#print axioms chart_of_odd
#print axioms odd_chart_iff
#print axioms choice_mem
end
end Sun28.WitnessIndices

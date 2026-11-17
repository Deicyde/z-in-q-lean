import CurveIndices

namespace Sun28.Ordinary
open ZInQ ZInQ.Mult WeierstrassCurve.Affine NumberField

/-- At either real embedding each nonidentity multiple has abscissa at least δ. -/
theorem generator_real_lower (σ : K0 →+* ℝ) (emb : 1 ≤ σ delta) {m : ℤ} (nz : m≠0) :
    σ delta ≤ σ (indexX m) := by
  have twice : m • curveGenerator = 2 • (m • pointR) := by
    unfold curveGenerator
    simp only [two_nsmul,zsmul_add]
  have nn := index_nonidentity nz
  rw [twice] at nn
  obtain ⟨x,y,h,e⟩ : ∃ x y h, m • pointR = Point.some x y h := by
    generalize step : m • pointR = Q at nn ⊢
    cases Q with
    | zero => exact (nn (by simp [← Point.zero_def])).elim
    | some x y h => exact ⟨x,y,h,rfl⟩
  rw [e] at twice nn
  have yn : y≠0 := fun hy => nn (two_smul_C_of_y_eq_zero h hy)
  obtain ⟨u,h₂,dub⟩ := curveC_two_smul_some h yn
  have sq : indexX m = ((x^2+delta^2)/(2*y))^2 := by
    unfold indexX
    rw [twice,dub]
    change (x^2+delta^2)^2/(4*x*(x^2-delta^2))=_
    have eq := (curveC_equation_iff _ _).mp h.1
    rw [show 4*x*(x^2-delta^2)=(2*y)^2 by linear_combination -4*eq, div_pow]
  have px : 0 < σ (indexX m) := by
    rw [sq,map_pow,map_div₀,map_add,map_pow,map_pow,map_mul,map_ofNat]
    apply sq_pos_of_ne_zero
    apply div_ne_zero
    · nlinarith [sq_nonneg (σ x)]
    · exact mul_ne_zero two_ne_zero (by simpa using σ.injective.ne yn)
  obtain ⟨v,on,_⟩ := index_affine nz
  have ecurve := congrArg σ ((curveC_equation_iff _ _).mp on.1)
  simp only [map_pow,map_mul,map_sub] at ecurve
  by_contra! bad
  have neg : σ (indexX m)^2-σ delta^2 < 0 := by nlinarith [sq_lt_sq' (by linarith : -σ delta < σ (indexX m)) bad]
  nlinarith [mul_neg_of_pos_of_neg px neg,sq_nonneg (σ v)]

theorem indexX_nonzero {m : ℤ} (nz : m≠0) : indexX m≠0 := by
  have h := generator_real_lower K0.embPlus embPlus_delta_mem.1 nz
  intro q
  rw [q,map_zero] at h
  linarith [embPlus_delta_mem.1]

theorem all_infinite_abscissas {m : ℤ} (nz : m≠0) (w : InfinitePlace K0) :
    1 ≤ w (indexX m) := by
  have which : w=wPlus ∨ w=wMinus := by
    have mem : w ∈ (Finset.univ : Finset (InfinitePlace K0)) := Finset.mem_univ _
    rw [infinitePlace_K0.1] at mem
    simpa only [Finset.mem_insert,Finset.mem_singleton] using mem
  obtain rfl|rfl := which
  · rw [wPlus_apply]
    exact (embPlus_delta_mem.1.trans (generator_real_lower K0.embPlus embPlus_delta_mem.1 nz)).trans (le_abs_self _)
  · rw [wMinus_apply]
    exact (embMinus_delta_mem.1.trans (generator_real_lower K0.embMinus embMinus_delta_mem.1 nz)).trans (le_abs_self _)

end Sun28.Ordinary
#print axioms Sun28.Ordinary.generator_real_lower
#print axioms Sun28.Ordinary.indexX_nonzero
#print axioms Sun28.Ordinary.all_infinite_abscissas

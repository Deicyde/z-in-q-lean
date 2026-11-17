import QuadraticAverage
import Mathlib.Basic.Real.Basic

/-! The real bound used in Sun's preparation constant for the new scalar. -/
namespace Sun28.ScalarTrace

private theorem real_factor_bound {r x L : ℝ} (hr : 1 ≤ r) (hx : |x| ≤ L) {k : ℕ} (hk : 1 ≤ k) :
    1 ≤ factor r x k ∧ factor r x k ≤ 1+L^2 := by
  have hpos : 0 < r := by linarith
  have hx2 : x^2 ≤ L^2 := by
    rw [←sq_abs x]
    nlinarith [abs_nonneg x]
  have hrk : r ≤ r^k := by
    simpa using (pow_le_pow_right₀ hr hk)
  have hkpos : 1 ≤ r^k := one_le_pow₀ hr
  have hrk2 : r ≤ (r^k)^2 := by nlinarith
  have hdiv : r*(x/r^k)^2 ≤ L^2 := by
    rw [div_pow,←mul_div_assoc,div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hx2 hpos.le,
      mul_le_mul_of_nonneg_left hrk2 (sq_nonneg L)]
  exact ⟨by dsimp [factor]; nlinarith [mul_nonneg hpos.le (sq_nonneg (x/r^k))],by dsimp [factor]; linarith⟩

theorem real_weight_bounds {r x y L : ℝ} (hr : 1 ≤ r) (hx : |x| ≤ L) (hy : |y| ≤ L) :
    1 ≤ weight r x y ∧ weight r x y ≤ (1+L^2)^2 := by
  obtain ⟨a,b⟩ := real_factor_bound hr hx (k:=1) (by decide)
  obtain ⟨c,d⟩ := real_factor_bound hr hy (k:=48) (by decide)
  unfold weight
  rw [sq (1+L^2)]
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_right a (show 0 ≤ factor r y 48 by linarith)],
    mul_le_mul b d (by linarith) (by positivity)⟩

theorem real_average_bounds {u w C : ℝ} (hu : 1 ≤ u) (hw : 1 ≤ w) (huc : u ≤ C) (hwc : w ≤ C) :
    1 ≤ (average u w)⁻¹ ∧ (average u w)⁻¹ ≤ C := by
  have up : 0 < u := by linarith
  have wp : 0 < w := by linarith
  have cp : 0 < C := lt_of_lt_of_le up huc
  have bound : C⁻¹ ≤ average u w ∧ average u w ≤ 1 := by
    unfold average
    have a := inv_anti₀ up huc
    have b := inv_anti₀ wp hwc
    have c := inv_anti₀ (by norm_num:0<(1:ℝ)) hu
    have d := inv_anti₀ (by norm_num:0<(1:ℝ)) hw
    simp only [inv_one] at c d
    constructor <;> linarith
  have pos : 0 < average u w := lt_of_lt_of_le (inv_pos.mpr cp) bound.1
  exact ⟨by simpa using inv_anti₀ pos bound.2,by simpa using inv_anti₀ (inv_pos.mpr cp) bound.1⟩

/-- The exact Archimedean constant follows from both embeddings of the actual
quadratic field, and one uniform bound for the two unnormalized tests. -/
theorem real_scalarTheta_bounds {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsQuadraticExtension ℚ K]
    (ι : K →ₐ[ℚ] ℝ) (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) {r : ℚ} {x y : K} {L : ℝ}
    (hr : (1:ℝ) ≤ r) (hx : |ι x| ≤ L) (hy : |ι y| ≤ L)
    (hx' : |ι (σ x)| ≤ L) (hy' : |ι (σ y)| ≤ L) :
    1 ≤ ((scalarTheta r x y:ℚ):ℝ)⁻¹ ∧ ((scalarTheta r x y:ℚ):ℝ)⁻¹ ≤ (1+L^2)^2 := by
  have eq := congrArg ι (scalarTheta_embeddings σ hσ r x y)
  have val : ((scalarTheta r x y:ℚ):ℝ) = average (weight (r:ℝ) (ι x) (ι y))
      (weight (r:ℝ) (ι (σ x)) (ι (σ y))) := by
    simpa [average,weight,factor,map_ofNat] using eq
  rw [val]
  obtain ⟨a,b⟩ := real_weight_bounds hr hx hy
  obtain ⟨c,d⟩ := real_weight_bounds hr hx' hy'
  exact real_average_bounds a c b d

end Sun28.ScalarTrace
#print axioms Sun28.ScalarTrace.real_weight_bounds
#print axioms Sun28.ScalarTrace.real_average_bounds
#print axioms Sun28.ScalarTrace.real_scalarTheta_bounds

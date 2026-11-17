import FixedData

/-! The real size of the signed seven-leaf scalar test on the integer-input branch. -/
namespace Sun28.FixedPreparation
open Sun28.ScalarHeight
noncomputable section

/-- Rewriting in reciprocal powers avoids estimates that grow with the integer radicand. -/
theorem reciprocal_tree (r : ℚ) (g : Fin 6 → ℚ) (nz : r≠0) :
    scalarTree r g =
    ((1+(g 0)^2*r⁻¹)^2+r⁻¹*((g 1)^2*r⁻¹+(g 2)^2)^2)^2+
    (r⁻¹)^3*((g 3)^2+(r⁻¹)^187*((g 4)^2*r⁻¹+(g 5)^2)^2)^2 := by
  rw [scalarTree_display _ _ nz]
  field_simp [nz]

private theorem times {a b A B : ℚ} (ha : |a|≤A) (hb : |b|≤B) : |a*b|≤A*B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) ((abs_nonneg a).trans ha)

private theorem add {a b A B : ℚ} (ha : |a|≤A) (hb : |b|≤B) : |a+b|≤A+B :=
  (abs_add_le a b).trans (add_le_add ha hb)

private theorem power {a A : ℚ} (ha : |a|≤A) (n : ℕ) : |a^n|≤A^n := by
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg a) ha n

theorem scalar_tree_bound (r : ℚ) (g : Fin 6 → ℚ) (h : 1≤|r|)
    (entries : ∀ i, |g i|≤1) : |scalarTree r g|≤89 := by
  have nz : r≠0 := by rintro rfl; norm_num at h
  have ht : |r⁻¹|≤1 := by rw [abs_inv]; exact inv_le_one_of_one_le₀ h
  have u (n : ℕ) : |(r⁻¹)^n|≤1 := by simpa only [one_pow] using power ht n
  have a (i : Fin 6) : |(g i)^2|≤1 := by simpa only [one_pow] using power (entries i) 2
  have b (i j : Fin 6) : |(g i)^2*r⁻¹+(g j)^2|≤2 := by
    exact (add (times (a i) ht) (a j)).trans (by norm_num)
  have base : |1+(g 0)^2*r⁻¹|≤2 := by
    exact (add (by norm_num : |(1:ℚ)|≤1) (times (a 0) ht)).trans (by norm_num)
  have left : |(1+(g 0)^2*r⁻¹)^2+r⁻¹*((g 1)^2*r⁻¹+(g 2)^2)^2|≤8 := by
    exact (add (power base 2) (times ht (power (b 1 2) 2))).trans (by norm_num)
  have right : |(g 3)^2+(r⁻¹)^187*((g 4)^2*r⁻¹+(g 5)^2)^2|≤5 := by
    exact (add (a 3) (times (u 187) (power (b 4 5) 2))).trans (by norm_num)
  rw [reciprocal_tree _ _ nz]
  exact (add (power left 2) (times (u 3) (power right 2))).trans (by norm_num)

/-- For the positive sign branch, the chosen denominator coefficient gives the real
inequality in Sun's pole completeness proposition. -/
theorem scalar_real_preparation (r : ℚ) (g : Fin 6 → ℚ) (δ : ℚ)
    (large : 1≤|r|) (sign : δ*r=|r|) (entries : ∀ i, |g i|≤1)
    (nonzero : scalarTree r g≠0) :
    0<signedValue r δ gamma denominator (scalarTree r g) ∧
    signedValue r δ gamma denominator (scalarTree r g)<1/2 := by
  rw [signedValue_display,sign]
  let t := |r|
  let W := scalarTree r g
  have t1 : 1≤t := large
  have tp : 0<t := by linarith
  have w0 : 0<W^2 := sq_pos_of_ne_zero nonzero
  have cap : W^2≤89^2 := by
    rw [←sq_abs W]
    exact pow_le_pow_left₀ (abs_nonneg _) (scalar_tree_bound r g large entries) 2
  have gp : 0<(gamma:ℚ) := by exact_mod_cast gamma_positive
  have D : (denominator:ℚ) = 126*(gamma:ℚ) := by simp [denominator]
  change 0 < (gamma:ℚ)^2*t*W^2/(1+(denominator:ℚ)*t^2)^2 ∧ _ < _
  rw [D]
  have pos : 0 < 1+126*(gamma:ℚ)*t^2 := by positivity
  refine ⟨by positivity,?_⟩
  rw [div_lt_iff₀ (sq_pos_of_pos pos)]
  have t3 : t≤t^4 := by simpa only [pow_one] using pow_le_pow_right₀ t1 (by decide : 1≤4)
  have w := mul_le_mul_of_nonneg_left cap (show 0≤(gamma:ℚ)^2*t by positivity)
  have good := mul_le_mul_of_nonneg_left t3 (show 0≤(gamma:ℚ)^2*(126^2) by positivity)
  change (gamma:ℚ)^2*t*W^2 < 1/2*(1+126*(gamma:ℚ)*t^2)^2
  nlinarith [mul_pos (sq_pos_of_pos gp) tp, mul_nonneg gp.le (sq_nonneg t)]

end
end Sun28.FixedPreparation
#print axioms Sun28.FixedPreparation.reciprocal_tree
#print axioms Sun28.FixedPreparation.scalar_tree_bound
#print axioms Sun28.FixedPreparation.scalar_real_preparation

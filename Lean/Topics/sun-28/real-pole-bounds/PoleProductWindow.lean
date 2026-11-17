import PoleDetectorWindow

namespace Sun28.RealPoleBounds
open Sun28.Ordinary Sun28.ScalarTrace

/-- Cancel the growing normalizers as u^(k+1) R^k = u (uR)^k. -/
theorem bounded_factor {A u r C x : ℝ} (ap : 0<A) (up : 0<u) (rp : 0<r) (rsmall : r≤1)
    (low : 1/A^5≤r*u) (size : |x|≤C) (deep : C*loss A≤u)
    (k : ℕ) (order : k≤64) :
    1≤factor r (x/u^(k+1)) k ∧ factor r (x/u^(k+1)) k≤2 := by
  have mulBound : 1≤(A^5)*(r*u) := by
    have h:=(div_le_iff₀ (pow_pos ap 5)).mp low
    nlinarith only [h]
  have power : 1 ≤ (A^5)^k*(r*u)^k := by
    rw [←mul_pow]
    exact one_le_pow₀ mulBound
  have ak : (A^5)^k≤loss A := by
    by_cases ge : 1≤A^5
    · exact (pow_le_pow_right₀ ge order).trans (le_max_right _ _)
    · exact (pow_le_one₀ (pow_nonneg ap.le 5) (le_of_not_ge ge)).trans (le_max_left _ _)
  have enlarge : 1≤loss A*(r*u)^k :=
    power.trans (mul_le_mul_of_nonneg_right ak (by positivity))
  have enough : |x|≤u*(r*u)^k := by
    calc
      |x| ≤ C*1 := by simpa using size
      _ ≤ C*(loss A*(r*u)^k) := mul_le_mul_of_nonneg_left enlarge ((abs_nonneg x).trans size)
      _ = (C*loss A)*(r*u)^k := by ring
      _ ≤ u*(r*u)^k := mul_le_mul_of_nonneg_right deep (by positivity)
  have id : (x/u^(k+1))/r^k = x/(u*(r*u)^k) := by
    rw [div_div,mul_pow,pow_succ]
    ring
  have unit : |(x/u^(k+1))/r^k|≤1 := by
    rw [id,abs_div,abs_of_pos (show 0<u*(r*u)^k by positivity)]
    exact (div_le_one (by positivity)).2 enough
  have squared : ((x/u^(k+1))/r^k)^2 ≤ 1 := by
    have := pow_le_pow_left₀ (abs_nonneg _) unit 2
    simpa [sq_abs] using this
  have add : r*((x/u^(k+1))/r^k)^2≤1 :=
    (mul_le_mul_of_nonneg_left squared rp.le).trans (by simpa using rsmall)
  unfold factor
  constructor
  · linarith [mul_nonneg rp.le (sq_nonneg ((x/u^(k+1))/r^k))]
  · linarith

/-- The product has exactly 16 positive factors; both embeddings get this estimate. -/
theorem bounded_product {A u r C : ℝ} (ap : 0<A) (up : 0<u) (rp : 0<r) (rsmall : r≤1)
    (low : 1/A^5≤r*u) (deep : C*loss A≤u) (D : OrdinaryTest→ℝ) (bounds : ∀ i, |D i|≤C) :
    1≤weightProduct r (fun i=>D i/u^(orderRequired i+1)) orderRequired ∧
    weightProduct r (fun i=>D i/u^(orderRequired i+1)) orderRequired≤2^16 := by
  classical
  have b i:=bounded_factor ap up rp rsmall low (bounds i) deep (orderRequired i) (order_le i)
  constructor
  · exact Finset.one_le_prod₀ (fun i _=>(b i).1)
  · calc
      _ ≤ ∏ _i : OrdinaryTest,(2:ℝ) := Finset.prod_le_prod₀ (fun i _=>zero_le_one.trans (b i).1) (fun i _=>(b i).2)
      _ = 2^16 := by simp [sixteen_orders.1]

end Sun28.RealPoleBounds
#print axioms Sun28.RealPoleBounds.bounded_factor
#print axioms Sun28.RealPoleBounds.bounded_product

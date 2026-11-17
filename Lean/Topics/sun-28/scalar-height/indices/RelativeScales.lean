import CertificateHeights

/-! Two projective ratios of the three slopes recover the ordinary comparison.
The common, freely chosen rational multiplier disappears from these heights. -/
namespace Sun28.IndexHeights
open ZInQ ZInQ.Mult Sun28.Ordinary Sun28.FixedPreparation Height
noncomputable section

def ratioHeight (t : Fin 3→ℚ) :=
  logHeight₁ (t 1/t 0)/2+logHeight₁ (t 2/t 0)/4

theorem ratio_invariant (t : Fin 3→ℚ) {u : ℚ} (live : u≠0) :
    ratioHeight (fun i=>t i*u)=ratioHeight t := by
  simp only [ratioHeight,mul_div_mul_right _ _ live]

theorem ratio_le_max (t : Fin 3→ℚ) {H : ℝ} (mx : ∀ i, logHeight₁ (t i)≤H) :
    ratioHeight t≤3/2*H := by
  have a:=logHeight₁_mul_le (t 1) (t 0)⁻¹
  have b:=logHeight₁_mul_le (t 2) (t 0)⁻¹
  rw [←div_eq_mul_inv,logHeight₁_inv] at a b
  unfold ratioHeight
  linarith [mx 0,mx 1,mx 2]

theorem intrinsic_from_ratios (C : K0) {η : ℚ} (nz : η≠0) :
    hK0 C≤ratioHeight (fun i=>(scaleRoot C.re C.im i)^2*η)+3/2*Real.log 2 := by
  have base:=hK0_ratCast_add_mul_sqrt2_le C.re C.im
  rw [←K0.eq_re_add_im_mul_sqrt2,ratHeight_eq_logHeight₁,ratHeight_eq_logHeight₁] at base
  have first : (scaleRoot C.re C.im 0)^2*η=η := by simp [scaleRoot]
  have a : (scaleRoot C.re C.im 1)^2*η/η=C.re^2 := by simp [scaleRoot,nz]
  have b : (scaleRoot C.re C.im 2)^2*η/η=(1+C.im^2)^2 := by simp [scaleRoot,nz]
  simp only [ratioHeight,first,a,b,logHeight₁_pow,Nat.cast_ofNat]
  linarith [twice_height_le_one_add_square C.im]

theorem product_bound (n : Fin 4→ℤ) (odd : ∀ i, Odd (n i)) :
    (indexSize n)^2≤hK0 (coordinateProduct n)+3*Real.log 7+Real.log 676/3 := by
  let A:=hK0 (coordinateProduct n)+3*Real.log 7+Real.log 676/3
  have one : 1 ≤ A := by
    have odd0:=odd 0
    have step : n 0≠0 := by obtain ⟨k,h⟩:=odd0;omega
    have c : 1≤(n 0).natAbs:=Int.natAbs_pos.mpr step
    have r : (1:ℝ)≤|(n 0:ℝ)| := by rw [←Int.cast_abs,←Nat.cast_natAbs];exact_mod_cast c
    have q:=quadratic_index_height (n 0)
    have p:=abscissa_product_bound n odd 0
    have k:=one_le_pow₀ r (n:=2)
    rw [sq_abs] at k
    dsimp [A]; linarith
  have get (i:Fin 4) : |(n i:ℝ)|≤Real.sqrt A := by
    apply (Real.le_sqrt (abs_nonneg _) (by linarith)).mpr
    rw [sq_abs]
    dsimp [A]
    linarith [quadratic_index_height (n i),abscissa_product_bound n odd i]
  have u1 : 1≤Real.sqrt A := (Real.le_sqrt zero_le_one (by linarith)).mpr (by simpa using one)
  have big : indexSize n≤Real.sqrt A := by
    unfold indexSize
    exact max_le u1 (max_le (get 0) (max_le (get 1) (max_le (get 2) (get 3))))
  simpa only [Real.sq_sqrt (show 0≤A by linarith)] using pow_le_pow_left₀ (zero_le_one.trans (one_le_indexSize n)) big 2

theorem ratio_bound (n : Fin 4→ℤ) (odd : ∀ i,Odd (n i)) {η:ℚ} (nz:η≠0) :
    (indexSize n)^2 ≤ ratioHeight (fun i => (scaleRoot (coordinateProduct n).re
      (coordinateProduct n).im i)^2*η)+10 := by
  have h :=intrinsic_from_ratios (coordinateProduct n) nz
  have p := product_bound n odd
  have cost : 3/2*Real.log 2+Real.log 676/3+3*Real.log 7 < (10:ℝ) := by
    have small (x : ℝ) (n k : ℕ) (one : (1:ℝ)<x) (h : x^n < (2.718:ℝ)^k) :
        (n:ℝ)*Real.log x < k := by
      have w : (2.718:ℝ)^k ≤ (Real.exp 1)^k :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) k
      have logs := Real.log_lt_log (pow_pos (zero_lt_one.trans one) _) (h.trans_le w)
      rw [Real.log_pow,Real.log_pow,Real.log_exp,mul_one] at logs
      exact logs
    have a := small 2 4 3 (by norm_num) (by norm_num)
    have b := small 676 1 7 (by norm_num) (by norm_num)
    have c := small 7 1 2 (by norm_num) (by norm_num)
    norm_num at a b c
    linarith
  linarith

end
end Sun28.IndexHeights
#print axioms Sun28.IndexHeights.ratio_invariant
#print axioms Sun28.IndexHeights.ratio_le_max
#print axioms Sun28.IndexHeights.intrinsic_from_ratios
#print axioms Sun28.IndexHeights.product_bound
#print axioms Sun28.IndexHeights.ratio_bound

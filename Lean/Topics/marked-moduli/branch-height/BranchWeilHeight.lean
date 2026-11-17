import ThetaQuotient

/-! A degree-ten formula bounds the rational invariant using only its branch weights. -/
namespace ZInQBlueprint.BranchHeight
open Height Height.AdmissibleAbsValues ThetaQuotient
noncomputable section
variable {K : Type*} [Field K]

def invariantPair (b : Fin 10 → K) : Fin 2 → K :=
  ![(3779136:K)^2 * ∏ i, b i, (∑ i, b i)^10]

private theorem product_bound (v : AbsoluteValue K ℝ) (b : Fin 10 → K) :
    ∏ i, v (b i) ≤ (⨆ j, v (b j))^10 := by
  simpa using Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => v.nonneg (b i))
    (g := fun _ => ⨆ j, v (b j)) (fun i _ => Finite.le_ciSup (fun j => v (b j)) i)

private theorem arch_bound (v : AbsoluteValue K ℝ) (b : Fin 10 → K) :
    (⨆ j, v (invariantPair b j)) ≤ (3779136:ℝ)^2 * (⨆ i, v (b i))^10 := by
  let R := ⨆ i, v (b i)
  have hsum : v (∑ i, b i) ≤ 10*R := (v.sum_le _ _).trans (by
    calc
      ∑ i, v (b i) ≤ ∑ _ : Fin 10, R := Finset.sum_le_sum fun i _ => Finite.le_ciSup (fun j => v (b j)) i
      _ = _ := by simp)
  refine ciSup_le fun j => ?_
  fin_cases j
  · change v ((3779136:K)^2 * ∏ i, b i) ≤ _
    rw [map_mul, map_pow, map_prod]
    exact mul_le_mul (pow_le_pow_left₀ (v.nonneg _) (v.apply_nat_le_self 3779136) 2)
      (product_bound v b) (Finset.prod_nonneg fun i _ => v.nonneg _) (by norm_num)
  · change v ((∑ i, b i)^10) ≤ _
    rw [map_pow]
    calc
      _ ≤ (10*R)^10 := pow_le_pow_left₀ (v.nonneg _) hsum _
      _ = 10^10 * R^10 := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass v b) _)

private theorem nonarch_bound (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (b : Fin 10 → K) : (⨆ j, v (invariantPair b j)) ≤ (⨆ i, v (b i))^10 := by
  refine ciSup_le fun j => ?_
  fin_cases j
  · change v ((3779136:K)^2 * ∏ i, b i) ≤ _
    rw [map_mul,map_pow,map_prod]
    apply le_trans (mul_le_of_le_one_left (Finset.prod_nonneg fun i _ => v.nonneg _)
      (pow_le_one₀ (v.nonneg _) (hv.apply_natCast_le_one (map_zero_le v 1) (map_one v) (n:=3779136))))
    exact product_bound v b
  · change v ((∑ i, b i)^10) ≤ _
    rw [map_pow]
    exact pow_le_pow_left₀ (v.nonneg _) (hv.apply_sum_univ_le (l:=b)) _

private theorem sup_tenth (v : AbsoluteValue K ℝ) (b : Fin 10 → K) :
    (⨆ i, v ((b^10) i)) = (⨆ i, v (b i))^10 := by
  obtain ⟨j,hj⟩ := exists_eq_ciSup_of_finite (f:=fun i => v (b i))
  refine le_antisymm (ciSup_le fun i => ?_) (Finite.le_ciSup_of_le j ?_)
  · simpa using pow_le_pow_left₀ (v.nonneg _) (Finite.le_ciSup (fun j => v (b j)) i) 10
  · simp [←hj]

theorem mulHeight_pair [AdmissibleAbsValues K] (b : Fin 10 → K) (hs : ∑ i, b i ≠ 0) :
    mulHeight (invariantPair b) ≤ ((3779136:ℝ)^2)^totalWeight K * mulHeight b^10 := by
  classical
  have hp : invariantPair b ≠ 0 := fun he => (pow_ne_zero 10 hs) (congrFun he 1)
  have hb : b ≠ 0 := by rintro rfl; simp at hs
  have hw : b^10 ≠ 0 := by simpa using hb
  rw [← mulHeight_pow b 10, Height.mulHeight_eq hp, Height.mulHeight_eq hw]
  let arch (x : Fin 10 → K) := (archAbsVal.map fun v => ⨆ i, v (x i)).prod
  have ha : (archAbsVal.map fun v => ⨆ j, v (invariantPair b j)).prod ≤
      ((3779136:ℝ)^2)^totalWeight K * arch (b^10) := by
    change _ ≤ _^(archAbsVal (K:=K)).card * _
    rw [← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul]
    exact Multiset.prod_map_le_prod_map₀ _ _ (fun v _ => Real.iSup_nonneg_of_nonnegHomClass v _)
      fun v _ => (arch_bound v b).trans_eq (by rw [sup_tenth])
  have hf : (∏ᶠ v : nonarchAbsVal, ⨆ j, v.val (invariantPair b j)) ≤
      ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val ((b^10) i) := by
    refine finprod_le_finprod₀ (by fun_prop (disch := assumption))
      (fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _) (by fun_prop (disch := assumption))
      fun v => ?_
    rw [sup_tenth]
    exact nonarch_bound _ (isNonarchimedean _ v.prop) b
  rw [← mul_assoc]
  exact mul_le_mul ha hf (finprod_nonneg fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _)
    (mul_nonneg (by positivity) (Multiset.prod_map_nonneg fun v _ => Real.iSup_nonneg_of_nonnegHomClass v _))

/-- The projective height of the ten weights bounds the ordinary logarithmic height of j. -/
theorem rational_height [NumberField K] (b : Fin 10 → K) (j : ℚ)
    (hs : ∑ i, b i ≠ 0) (he : (j:K)^2 = ((3779136:K)^2 * ∏ i, b i)/(∑ i, b i)^10) :
    ZInQ.ratHeight j ≤ 5 * normalizedHeight b + Real.log 3779136 := by
  have hh := Real.log_le_log (mulHeight_pos _) (mulHeight_pair b hs)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow] at hh
  change logHeight (invariantPair b) ≤ totalWeight K * (2 * Real.log 3779136) + 10 * logHeight b at hh
  have eqh : logHeight (invariantPair b) = logHeight₁ ((j:K)^2) := by
    rw [he,logHeight₁_div_eq_logHeight]
    rfl
  rw [eqh,logHeight₁_pow,relative_rational_height,NumberField.totalWeight_eq_finrank] at hh
  unfold normalizedHeight
  have hd : 0 < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  norm_num only [Nat.cast_ofNat] at hh
  field_simp
  linarith only [hh]

end
end ZInQBlueprint.BranchHeight
#print axioms ZInQBlueprint.BranchHeight.mulHeight_pair
#print axioms ZInQBlueprint.BranchHeight.rational_height

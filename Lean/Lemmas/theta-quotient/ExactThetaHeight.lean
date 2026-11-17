import ThetaQuotient
import Mathlib.Analysis.MeanInequalities

/-! The Euclidean archimedean norm absorbs the coefficient of the theta quotient. -/
namespace ZInQBlueprint.ThetaQuotient
open Height Height.AdmissibleAbsValues
noncomputable section

/-- The ordinary, tenth-power form of AM–GM for ten nonnegative entries. -/
private theorem prod_le_tenth_mean (a : Fin 10 → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∏ i, a i ≤ ((∑ i, a i)/10)^10 := by
  have hm := Real.geom_mean_le_arith_mean Finset.univ (fun _ : Fin 10 => (1:ℝ)) a
    (fun _ _ => zero_le_one) (by norm_num) (fun i _ => ha i)
  have hm' : (∏ i, a i)^((10:ℝ)⁻¹) ≤ (∑ i, a i)/10 := by simpa using hm
  have hp := Finset.prod_nonneg (fun i (_ : i ∈ Finset.univ) => ha i)
  calc
    _ = ((∏ i, a i)^((10:ℝ)⁻¹))^(10:ℕ) :=
      (Real.rpow_inv_natCast_pow hp (by decide : (10:ℕ) ≠ 0)).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hp _) hm' _

private theorem sum_even_le (a : Fin 16 → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∑ i, a (evenIndices i) ≤ ∑ i, a i := by
  let e : Fin 10 ↪ Fin 16 := ⟨evenIndices,evenIndices_injective⟩
  have h := Finset.sum_le_sum_of_subset_of_nonneg (s := Finset.univ.map e) (t := Finset.univ)
    (by simp) (f := a) (fun i _ _ => ha i)
  simpa [e] using h

variable {K : Type*} [Field K]
private def targetPair (x : Fin 16 → K) : Fin 2 → K :=
  ![numerator (x ∘ evenIndices), denominator (x ∘ evenIndices)]

/-- Both homogeneous polynomials have norm at most the fortieth power of the
Euclidean norm of all sixteen coordinates. -/
theorem archimedean_euclidean_bound (v : AbsoluteValue K ℝ) (x : Fin 16 → K) :
    (⨆ i, v (targetPair x i)) ≤ (Real.sqrt (∑ i, v (x i)^2))^40 := by
  let a (i : Fin 16) := v (x i)^2
  let T := ∑ i, a i
  let z := x ∘ evenIndices
  have ha (i) : 0 ≤ a i := sq_nonneg _
  have ht : 0 ≤ T := Finset.sum_nonneg fun i _ => ha i
  have hsub : ∑ i, a (evenIndices i) ≤ T := sum_even_le _ ha
  have hg := (prod_le_tenth_mean (fun i => a (evenIndices i)) (fun i => ha _)).trans
    (pow_le_pow_left₀ (div_nonneg (Finset.sum_nonneg fun i _ => ha (evenIndices i)) (by norm_num))
      (div_le_div_of_nonneg_right hsub (by norm_num)) 10)
  have hp : (∏ i, v (z i))^4 ≤ (T/10)^20 := calc
    _ = (∏ i, a (evenIndices i))^2 := by simp [a,z,Finset.prod_pow]; ring
    _ ≤ ((T/10)^10)^2 :=
      pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => ha _) hg 2
    _ = _ := by ring
  have hnum : v (numerator z) ≤ T^20 := by
    unfold numerator
    rw [map_mul,map_pow,map_prod]
    calc
      _ ≤ 3779136*(T/10)^20 := mul_le_mul (v.apply_nat_le_self 3779136) hp (by positivity)
        (by norm_num)
      _ = (3779136/(10:ℝ)^20)*T^20 := by ring
      _ ≤ 1*T^20 := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg ht _)
      _ = _ := one_mul _
  have hsum : v (∑ i, (z i)^8) ≤ T^4 := calc
    _ ≤ ∑ i, v ((z i)^8) := v.sum_le _ _
    _ = ∑ i, (a (evenIndices i))^4 := by simp only [a,z,Function.comp_apply,map_pow]; ring_nf
    _ ≤ ∑ i, a (evenIndices i)*T^3 := Finset.sum_le_sum fun i _ => calc
      _ = a (evenIndices i)*(a (evenIndices i))^3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ha _) (Finset.single_le_sum
        (fun j _ => ha j) (Finset.mem_univ (evenIndices i))) 3) (ha _)
    _ = (∑ i, a (evenIndices i))*T^3 := by rw [Finset.sum_mul]
    _ ≤ T*T^3 := mul_le_mul_of_nonneg_right hsub (pow_nonneg ht _)
    _ = _ := by ring
  have hden : v (denominator z) ≤ T^20 := by
    unfold denominator; rw [map_pow]
    exact (pow_le_pow_left₀ (v.nonneg _) hsum 5).trans_eq (by ring)
  change _ ≤ (Real.sqrt T)^40
  rw [show (40:ℕ) = 2*20 by decide,pow_mul,Real.sq_sqrt ht]
  exact ciSup_le fun i => by fin_cases i <;> first | exact hnum | exact hden

private theorem finite_euclidean_bound (v : AbsoluteValue K ℝ) (hn : IsNonarchimedean v)
    (x : Fin 16 → K) : (⨆ i, v (targetPair x i)) ≤ (⨆ i, v (x i))^40 := by
  refine (nonarchimedean_bound v hn (x ∘ evenIndices)).trans ?_
  exact pow_le_pow_left₀ (Real.iSup_nonneg_of_nonnegHomClass v _)
    (ciSup_le fun i => Finite.le_ciSup (fun j => v (x j)) (evenIndices i)) _

/-- Local Euclidean bounds give a rational height estimate with zero additive constant. -/
theorem ratHeight_le_level_two_exact [NumberField K] (x : Fin 16 → K) (j : ℚ)
    (h : (j : K) = numerator (x ∘ evenIndices) / denominator (x ∘ evenIndices))
    (hd : denominator (x ∘ evenIndices) ≠ 0) :
    ZInQ.ratHeight j ≤ 40*euclideanHeight x := by
  classical
  have hp : targetPair x ≠ 0 := fun hc => hd (congrFun hc 1)
  have hx : x ≠ 0 := by rintro rfl; simp [denominator,Function.comp_def] at hd
  let A := ((archAbsVal (K := K)).map fun v : AbsoluteValue K ℝ =>
    Real.sqrt (∑ i, v (x i)^2)).prod
  let F := ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i)
  have ha : ((archAbsVal (K := K)).map fun v => ⨆ i, v (targetPair x i)).prod ≤ A^40 := by
    unfold A
    rw [← Multiset.prod_map_pow]
    exact Multiset.prod_map_le_prod_map₀ _ _ (fun v _ => Real.iSup_nonneg_of_nonnegHomClass v _)
      fun v _ => archimedean_euclidean_bound v x
  have hf : (∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (targetPair x i)) ≤ F^40 := by
    unfold F
    rw [finprod_pow (by fun_prop (disch := assumption))]
    refine finprod_le_finprod₀ (by fun_prop (disch := assumption))
      (fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _) (by fun_prop (disch := assumption))
      fun v => finite_euclidean_bound v.val (isNonarchimedean _ v.prop) x
  have hm : Height.mulHeight (targetPair x) ≤ (A*F)^40 := by
    rw [Height.mulHeight_eq hp,mul_pow]
    exact mul_le_mul ha hf (finprod_nonneg fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _)
      (by positivity)
  have hl := Real.log_le_log (Height.mulHeight_pos _) hm
  rw [Real.log_pow] at hl
  change Height.logHeight (targetPair x) ≤ 40*Real.log (A*F) at hl
  rw [show Height.logHeight (targetPair x) = Height.logHeight₁ (j:K) by
    rw [h,Height.logHeight₁_div_eq_logHeight]; rfl,relative_rational_height] at hl
  have hdg : 0 < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  unfold euclideanHeight
  rw [if_neg hx]
  change ZInQ.ratHeight j ≤ 40*(Real.log (A*F)/(Module.finrank ℚ K:ℝ))
  rw [← mul_div_assoc, le_div_iff₀ hdg]
  linarith

end
end ZInQBlueprint.ThetaQuotient
#print axioms ZInQBlueprint.ThetaQuotient.archimedean_euclidean_bound
#print axioms ZInQBlueprint.ThetaQuotient.ratHeight_le_level_two_exact

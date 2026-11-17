import ThetaQuotient

/-! Supremum and Euclidean heights after removing zero coordinates. -/
namespace ZInQBlueprint.SixMetric
open Height Height.AdmissibleAbsValues ThetaQuotient
noncomputable section
variable {K ι κ : Type*} [Field K] [NumberField K]
  [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]

/-- Delete any zero coordinates, in any order. -/
theorem sparse_heights (e : ι → κ) (inj : Function.Injective e) (x : κ → K)
    (off : ∀ j, (¬ ∃ i, e i=j) → x j=0) :
    normalizedHeight (x ∘ e)=normalizedHeight x ∧ euclideanHeight (x ∘ e)=euclideanHeight x := by
  classical
  by_cases hx : x=0
  · subst x
    change normalizedHeight (0 : ι → K)=normalizedHeight (0 : κ → K) ∧
      euclideanHeight (0 : ι → K)=euclideanHeight (0 : κ → K)
    simp [normalizedHeight,euclideanHeight]
  have hsub : x ∘ e ≠ 0 := by
    intro h
    apply hx
    funext j
    obtain ⟨i,rfl⟩ | h₁ := em (∃ i, e i=j)
    · exact congrFun h i
    · exact off j h₁
  have H (v : AbsoluteValue K ℝ) : (⨆ i, v ((x ∘ e) i))=⨆ j, v (x j) := by
    refine le_antisymm (ciSup_le fun i => Finite.le_ciSup (fun j => v (x j)) (e i)) ?_
    refine ciSup_le fun j => ?_
    by_cases hj : ∃ i, e i=j
    · obtain ⟨i,rfl⟩ := hj
      exact Finite.le_ciSup (fun t => v ((x ∘ e) t)) i
    · simpa [off j hj] using Real.iSup_nonneg_of_nonnegHomClass v (x ∘ e)
  have S (v : AbsoluteValue K ℝ) : (∑ i, v ((x ∘ e) i)^2) = ∑ j, v (x j)^2 := by
    apply Fintype.sum_of_injective e inj
    · intro j hj
      simp [off j hj]
    · intro i; rfl
  constructor
  · unfold normalizedHeight
    simp only [logHeight_eq_log_mulHeight,mulHeight_eq hsub,mulHeight_eq hx,H]
  · unfold euclideanHeight
    simp only [hx,hsub,↓reduceIte,H,S]

/-- For a list of n coordinates the normalized Euclidean height exceeds the
supremum height by at most one half of log n. -/
theorem euclidean_upper (x : ι → K) :
    euclideanHeight x ≤ normalizedHeight x+Real.log (Fintype.card ι)/2 := by
  classical
  by_cases hx : x=0
  · subst x
    have hcard : (1:ℝ) ≤ Fintype.card ι := by exact_mod_cast (Fintype.card_pos (α:=ι))
    simpa [normalizedHeight,euclideanHeight] using (div_nonneg (Real.log_nonneg hcard) (by norm_num : (0:ℝ)≤2))
  let c : ℝ := Real.sqrt (Fintype.card ι)
  have cpos : 0<c := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have bound (v : AbsoluteValue K ℝ) :
      Real.sqrt (∑ i, v (x i)^2) ≤ c*(⨆ i, v (x i)) := by
    let m := ⨆ i, v (x i)
    have hm : 0 ≤ m := Real.iSup_nonneg_of_nonnegHomClass v x
    have sum : (∑ i, v (x i)^2) ≤ (Fintype.card ι:ℝ)*m^2 := by
      calc
        _ ≤ ∑ _i : ι, m^2 := Finset.sum_le_sum fun i _ =>
          pow_le_pow_left₀ (v.nonneg _) (Finite.le_ciSup (fun j => v (x j)) i) _
        _ = _ := by simp
    have b := Real.sqrt_le_sqrt sum
    simpa [Real.sqrt_mul (Nat.cast_nonneg _),Real.sqrt_sq hm,c,m] using b
  let T := (archAbsVal.map (fun v : AbsoluteValue K ℝ => Real.sqrt (∑ i, v (x i)^2))).prod *
        ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i)
  have low : mulHeight x ≤ T := by
    rw [mulHeight_eq hx]
    apply mul_le_mul_of_nonneg_right _ (finprod_nonneg fun v : nonarchAbsVal =>
      Real.iSup_nonneg_of_nonnegHomClass v.val x)
    exact Multiset.prod_map_le_prod_map₀ _ _ (fun v _ => Real.iSup_nonneg_of_nonnegHomClass v x)
      fun v _ => ciSup_le fun i => Real.le_sqrt_of_sq_le
        (Finset.single_le_sum (fun j _ => sq_nonneg (v (x j))) (Finset.mem_univ i))
  have total : T ≤ c^(totalWeight K) * mulHeight x := by
    rw [mulHeight_eq hx,←mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (finprod_nonneg fun v : nonarchAbsVal =>
      Real.iSup_nonneg_of_nonnegHomClass v.val x)
    change _ ≤ c^(archAbsVal (K:=K)).card * _
    rw [← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul]
    exact Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ => Real.sqrt_nonneg _) fun v _ => bound v
  have h := Real.log_le_log ((mulHeight_pos x).trans_le low) total
  rw [Real.log_mul (pow_pos cpos _).ne' (mulHeight_pos x).ne',Real.log_pow,
    NumberField.totalWeight_eq_finrank] at h
  have hd : 0<(Module.finrank ℚ K:ℝ) := by exact_mod_cast Module.finrank_pos
  have hc : Real.log c=Real.log (Fintype.card ι)/2 := Real.log_sqrt (Nat.cast_nonneg _)
  simp only [euclideanHeight,hx,↓reduceIte,normalizedHeight,logHeight_eq_log_mulHeight]
  change Real.log T / _ ≤ _
  rw [div_le_iff₀ hd,add_mul,div_mul_cancel₀ _ hd.ne',←hc]
  linarith only [h]

end
end ZInQBlueprint.SixMetric
#print axioms ZInQBlueprint.SixMetric.sparse_heights
#print axioms ZInQBlueprint.SixMetric.euclidean_upper

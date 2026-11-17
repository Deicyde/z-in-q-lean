import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.MvPolynomial
import Mathlib.Analysis.Complex.ExponentialBounds
import ZInQKernel.Hypotheses.Height

/-! The degree-40 theta quotient over an arbitrary number field. -/
namespace ZInQBlueprint.ThetaQuotient
open Height Height.AdmissibleAbsValues
noncomputable section

variable {K : Type*} [Field K]

def numerator (z : Fin 10 → K) : K := 3779136 * (∏ i, z i)^4
def denominator (z : Fin 10 → K) : K := (∑ i, z i ^ 8)^5

private def pair (z : Fin 10 → K) : Fin 2 → K := ![numerator z, denominator z]

private lemma prod_bound (v : AbsoluteValue K ℝ) (z : Fin 10 → K) :
    v (∏ i, z i) ≤ (⨆ i, v (z i)) ^ 10 := by
  rw [map_prod]
  simpa using Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ ↦ v.nonneg (z i))
    (g := fun _ ↦ ⨆ i, v (z i)) (fun i _ ↦ Finite.le_ciSup (fun j ↦ v (z j)) i)

private lemma summand_bound (v : AbsoluteValue K ℝ) (z : Fin 10 → K) (i : Fin 10) :
    v (z i ^ 8) ≤ (⨆ j, v (z j)) ^ 8 := by
  rw [map_pow]
  exact pow_le_pow_left₀ (v.nonneg _) (Finite.le_ciSup (fun j ↦ v (z j)) i) _

theorem archimedean_bound (v : AbsoluteValue K ℝ) (z : Fin 10 → K) :
    (⨆ i, v (pair z i)) ≤ 3779136 * (⨆ i, v (z i)) ^ 40 := by
  let R := ⨆ i, v (z i)
  have hR : 0 ≤ R := Real.iSup_nonneg_of_nonnegHomClass v z
  have hsum : v (∑ i, z i ^ 8) ≤ 10 * R ^ 8 := calc
    _ ≤ ∑ i, v (z i ^ 8) := v.sum_le _ _
    _ ≤ ∑ _ : Fin 10, R ^ 8 := Finset.sum_le_sum fun i _ ↦ summand_bound v z i
    _ = _ := by simp
  refine ciSup_le fun i ↦ ?_
  fin_cases i
  · change v (3779136 * (∏ i, z i) ^ 4) ≤ 3779136 * R ^ 40
    rw [map_mul, map_pow]
    calc
      _ ≤ (3779136 : ℝ) * (R ^ 10)^4 := mul_le_mul (v.apply_nat_le_self 3779136)
        (pow_le_pow_left₀ (v.nonneg _) (prod_bound v z) _) (by positivity) (by norm_num)
      _ = _ := by ring
  · change v ((∑ i, z i ^ 8)^5) ≤ 3779136 * R ^ 40
    rw [map_pow]
    calc
      _ ≤ (10 * R ^ 8)^5 := pow_le_pow_left₀ (v.nonneg _) hsum _
      _ = 100000 * R ^ 40 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hR _)

theorem nonarchimedean_bound (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (z : Fin 10 → K) : (⨆ i, v (pair z i)) ≤ (⨆ i, v (z i)) ^ 40 := by
  let R := ⨆ i, v (z i)
  have hsum : v (∑ i, z i ^ 8) ≤ R ^ 8 :=
    hv.apply_sum_univ_le.trans (ciSup_le fun i ↦ summand_bound v z i)
  refine ciSup_le fun i ↦ ?_
  fin_cases i
  · change v (3779136 * (∏ i, z i) ^ 4) ≤ R ^ 40
    rw [map_mul, map_pow]
    have hc : v 3779136 ≤ 1 := hv.apply_natCast_le_one (map_zero_le v 1) (map_one v)
      (n := 3779136)
    calc
      _ ≤ 1 * (R ^ 10)^4 := mul_le_mul hc
        (pow_le_pow_left₀ (v.nonneg _) (prod_bound v z) _) (by positivity) zero_le_one
      _ = _ := by ring
  · change v ((∑ i, z i ^ 8)^5) ≤ R ^ 40
    rw [map_pow]
    calc
      _ ≤ (R ^ 8)^5 := pow_le_pow_left₀ (v.nonneg _) hsum _
      _ = _ := by ring

private lemma sup_pow (v : AbsoluteValue K ℝ) (z : Fin 10 → K) :
    (⨆ i, v ((z ^ 40) i)) = (⨆ i, v (z i)) ^ 40 := by
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ v (z i))
  refine le_antisymm (ciSup_le fun i ↦ ?_) (Finite.le_ciSup_of_le j ?_)
  · simpa using pow_le_pow_left₀ (v.nonneg _) (Finite.le_ciSup (fun j ↦ v (z j)) i) 40
  · simp [← hj]

theorem multiplicative_bound [AdmissibleAbsValues K] (z : Fin 10 → K)
    (hd : denominator z ≠ 0) :
    mulHeight (pair z) ≤ (3779136 : ℝ) ^ totalWeight K * mulHeight z ^ 40 := by
  classical
  have hp : pair z ≠ 0 := fun h ↦ hd (congrFun h 1)
  have hz : z ≠ 0 := by rintro rfl; simp [denominator] at hd
  have hw : z ^ 40 ≠ 0 := by simpa using hz
  rw [← mulHeight_pow z 40, Height.mulHeight_eq hp, Height.mulHeight_eq hw]
  let arch (x : Fin 10 → K) := (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod
  have ha : (archAbsVal.map fun v ↦ ⨆ i, v (pair z i)).prod ≤
      3779136 ^ totalWeight K * arch (z ^ 40) := by
    change _ ≤ 3779136 ^ (archAbsVal (K := K)).card * _
    rw [← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul]
    exact Multiset.prod_map_le_prod_map₀ _ _ (fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _)
      fun v _ ↦ (archimedean_bound v z).trans_eq (by rw [sup_pow])
  have hf : (∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (pair z i)) ≤
      ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val ((z ^ 40) i) := by
    refine finprod_le_finprod₀ (by fun_prop (disch := assumption))
      (fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _) (by fun_prop (disch := assumption))
      fun v ↦ ?_
    rw [sup_pow]
    exact nonarchimedean_bound v.val (isNonarchimedean _ v.prop) z
  rw [← mul_assoc]
  exact mul_le_mul ha hf (finprod_nonneg fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _)
    (mul_nonneg (by positivity) (Multiset.prod_map_nonneg fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _))

variable [NumberField K]

/-- The logarithmic projective Weil height over a number field, divided by the field degree. -/
def normalizedHeight {ι : Type*} (z : ι → K) : ℝ :=
  logHeight z / (Module.finrank ℚ K : ℝ)

omit [NumberField K] in
private lemma maximum_pair (v : AbsoluteValue K ℝ) (a b : K) :
    (⨆ i, v (![a,b] i)) = max (v a) (v b) := by
  refine le_antisymm (ciSup_le fun i ↦ ?_) (max_le ?_ ?_)
  · fin_cases i <;> simp
  · exact Finite.le_ciSup_of_le 0 le_rfl
  · exact Finite.le_ciSup_of_le 1 le_rfl

private lemma finite_coprime (v : nonarchAbsVal (K := K)) (j : ℚ) :
    (⨆ i, v.val (![(j.num : K),(j.den : K)] i)) = 1 := by
  have hv := isNonarchimedean _ v.prop
  have hZ (n : ℤ) : v.val n ≤ 1 :=
    hv.apply_intCast_le_one (map_zero_le v.val 1) (map_one v.val) (map_neg_eq_map v.val)
  have hN : v.val (j.den : K) ≤ 1 :=
    hv.apply_natCast_le_one (map_zero_le v.val 1) (map_one v.val)
  obtain ⟨a,b,hab⟩ := Rat.isCoprime_num_den j
  have h : (a : K) * (j.num : K) + (b : K) * (j.den : K) = 1 := by exact_mod_cast hab
  rw [maximum_pair]
  refine le_antisymm (max_le (hZ _) hN) ?_
  calc
    1 = v.val ((a : K) * j.num + (b : K) * j.den) := by rw [h, map_one]
    _ ≤ max (v.val ((a : K) * j.num)) (v.val ((b : K) * j.den)) := hv ..
    _ ≤ _ := by
      simp only [map_mul]
      exact max_le_max (mul_le_of_le_one_left (v.val.nonneg _) (hZ _))
        (mul_le_of_le_one_left (v.val.nonneg _) (hZ _))

/-- For a rational number, the relative height over K is the field degree times the
ordinary height of its reduced numerator and denominator. -/
theorem relative_rational_height (j : ℚ) :
    Height.logHeight₁ (j : K) = (Module.finrank ℚ K : ℝ) * ZInQ.ratHeight j := by
  let M := max |(j.num : ℝ)| (j.den : ℝ)
  have hn : (j.den : K) ≠ 0 := by exact_mod_cast j.den_nz
  have hpair : (![(j.num : K),(j.den : K)] : Fin 2 → K) ≠ 0 := fun h ↦ hn (congrFun h 1)
  have ha (v : AbsoluteValue K ℝ) (hv : v ∈ archAbsVal (K := K)) :
      (⨆ i, v (![(j.num : K),(j.den : K)] i)) = M := by
    obtain ⟨w,rfl⟩ := (NumberField.isInfinitePlace_iff v).mp (NumberField.mem_multisetInfinitePlace.mp hv)
    rw [maximum_pair]
    change max (w (j.num : K)) (w (j.den : K)) = _
    simp only [← NumberField.InfinitePlace.norm_embedding_eq, map_intCast, map_natCast,
      Complex.norm_intCast, Complex.norm_natCast]
    rfl
  have hm : Height.mulHeight₁ (j : K) = M ^ totalWeight K := by
    rw [Rat.cast_def, Height.mulHeight₁_div_eq_mulHeight, Height.mulHeight_eq hpair,
      finprod_eq_one_of_forall_eq_one (fun v ↦ finite_coprime v j), mul_one]
    change _ = M ^ (archAbsVal (K := K)).card
    rw [← Multiset.prod_replicate, ← Multiset.map_const']
    exact congrArg Multiset.prod (Multiset.map_congr rfl ha)
  rw [Height.logHeight₁_eq_log_mulHeight₁, hm, Real.log_pow, NumberField.totalWeight_eq_finrank]
  rfl

theorem log_coefficient_le : Real.log 3779136 ≤ 16 := by
  calc
    _ ≤ Real.log (2 ^ 22) := Real.log_le_log (by norm_num) (by norm_num)
    _ = 22 * Real.log 2 := by rw [Real.log_pow]; norm_num
    _ ≤ 16 := by linarith [Real.log_two_lt_d9]

/-- The rational height used by the public theorem satisfies the projective bound
for algebraic theta coordinates in any common number field. -/
theorem ratHeight_le_sixteen (z : Fin 10 → K) (j : ℚ)
    (h : (j : K) = numerator z / denominator z) (hd : denominator z ≠ 0) :
    ZInQ.ratHeight j ≤ 40 * normalizedHeight z + 16 := by
  have hlog := Real.log_le_log (mulHeight_pos _) (multiplicative_bound z hd)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  change logHeight (pair z) ≤ totalWeight K * Real.log 3779136 + 40 * logHeight z at hlog
  rw [show logHeight (pair z) = logHeight₁ (j : K) by
    rw [h, logHeight₁_div_eq_logHeight]; rfl,
    relative_rational_height, NumberField.totalWeight_eq_finrank] at hlog
  have hdeg : 0 < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hc := mul_le_mul_of_nonneg_left log_coefficient_le hdeg.le
  unfold normalizedHeight
  field_simp
  nlinarith

theorem ratHeight_le (z : Fin 10 → K) (j : ℚ)
    (h : (j : K) = numerator z / denominator z) (hd : denominator z ≠ 0) :
    ZInQ.ratHeight j ≤ 40 * normalizedHeight z + 22 :=
  (ratHeight_le_sixteen z j h hd).trans (by linarith)

open Classical in
/-- At archimedean places use the Euclidean norm of the full list of coordinates.
Finite places retain the supremum norm. The zero list has height zero. -/
def euclideanHeight {ι : Type*} [Fintype ι] (x : ι → K) : ℝ :=
  if x = 0 then 0 else
    Real.log ((archAbsVal.map (fun v : AbsoluteValue K ℝ ↦
      Real.sqrt (∑ i, v (x i) ^ 2))).prod *
       ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i)) / (Module.finrank ℚ K : ℝ)

theorem normalizedHeight_le_euclideanHeight {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → K) :
    normalizedHeight x ≤ euclideanHeight x := by
  classical
  by_cases hx : x = 0
  · simp [normalizedHeight, euclideanHeight, hx]
  unfold normalizedHeight euclideanHeight
  simp only [hx, ↓reduceIte, logHeight_eq_log_mulHeight]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Real.log_le_log (mulHeight_pos _)
  rw [Height.mulHeight_eq hx]
  apply mul_le_mul_of_nonneg_right _ (finprod_nonneg fun v : nonarchAbsVal (K := K) ↦
    Real.iSup_nonneg_of_nonnegHomClass v.val x)
  exact Multiset.prod_map_le_prod_map₀ _ _ (fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _)
    fun v _ ↦ ciSup_le fun i ↦ Real.le_sqrt_of_sq_le
      (Finset.single_le_sum (fun j _ ↦ sq_nonneg (v (x j))) (Finset.mem_univ i))

/-- The ten entries used by the quotient may be selected from the sixteen entries
of the level-two theta point. The six other entries need no vanishing hypothesis. -/
theorem ratHeight_le_euclidean_sixteen (x : Fin 16 → K) (e : Fin 10 → Fin 16) (j : ℚ)
    (h : (j : K) = numerator (x ∘ e) / denominator (x ∘ e)) (hd : denominator (x ∘ e) ≠ 0) :
    ZInQ.ratHeight j ≤ 40 * euclideanHeight x + 16 := by
  apply (ratHeight_le_sixteen _ _ h hd).trans
  have hs : normalizedHeight (x ∘ e) ≤ normalizedHeight x := by
    unfold normalizedHeight
    exact div_le_div_of_nonneg_right (logHeight_comp_le e x) (Nat.cast_nonneg _)
  gcongr
  exact hs.trans (normalizedHeight_le_euclideanHeight x)

theorem ratHeight_le_euclidean (x : Fin 16 → K) (e : Fin 10 → Fin 16) (j : ℚ)
    (h : (j : K) = numerator (x ∘ e) / denominator (x ∘ e)) (hd : denominator (x ∘ e) ≠ 0) :
    ZInQ.ratHeight j ≤ 40 * euclideanHeight x + 22 :=
  (ratHeight_le_euclidean_sixteen x e j h hd).trans (by linarith)

/-- The four bits of `m` encode the characteristic (a₀,a₁;b₀,b₁) in this order,
with a₀ the least significant bit. Half-characteristics are even when a·b is even. -/
def evenCharacteristic (m : Fin 16) : Bool :=
  ((m.val % 2 * (m.val / 4 % 2) + (m.val / 2 % 2) * (m.val / 8 % 2)) % 2) == 0

def evenIndices : Fin 10 → Fin 16 := ![0,1,2,3,4,6,8,9,12,15]

theorem evenIndices_injective : Function.Injective evenIndices := by decide

theorem evenIndices_exact (m : Fin 16) :
    (∃ i, evenIndices i = m) ↔ evenCharacteristic m = true := by
  fin_cases m <;> decide

theorem ratHeight_le_level_two (x : Fin 16 → K) (j : ℚ)
    (h : (j : K) = numerator (x ∘ evenIndices) / denominator (x ∘ evenIndices))
    (hd : denominator (x ∘ evenIndices) ≠ 0) :
    ZInQ.ratHeight j ≤ 40 * euclideanHeight x + 22 :=
  ratHeight_le_euclidean x evenIndices j h hd

theorem ratHeight_le_level_two_sixteen (x : Fin 16 → K) (j : ℚ)
    (h : (j : K) = numerator (x ∘ evenIndices) / denominator (x ∘ evenIndices))
    (hd : denominator (x ∘ evenIndices) ≠ 0) :
    ZInQ.ratHeight j ≤ 40 * euclideanHeight x + 16 :=
  ratHeight_le_euclidean_sixteen x evenIndices j h hd

#print axioms ratHeight_le_euclidean_sixteen
#print axioms ratHeight_le_level_two_sixteen
#print axioms evenIndices_injective
#print axioms evenIndices_exact
#print axioms ratHeight_le_level_two
#print axioms archimedean_bound
#print axioms nonarchimedean_bound
#print axioms multiplicative_bound
#print axioms relative_rational_height
#print axioms log_coefficient_le
#print axioms ratHeight_le_sixteen
#print axioms ratHeight_le
#print axioms normalizedHeight_le_euclideanHeight
#print axioms ratHeight_le_euclidean
end
end ZInQBlueprint.ThetaQuotient

import ArchRootMetric

/-! Completely algebraic bounds on the Archimedean correction, before choosing a period. -/
namespace ZInQBlueprint.SixMetric
open NumberField Function
noncomputable section

theorem distortion_bounds (a : Fin 10 → ℝ) (pos : ∀ i, 0<a i) :
    1 ≤ rootDistortion a ∧ rootDistortion a ≤ Real.sqrt 10 := by
  let b (i : Fin 10) := eighthRoot (a i)
  let M := ⨆ i, b i
  have hpos (i : Fin 10) : 0<b i := by dsimp [b,eighthRoot]; positivity [pos i]
  have mpos : 0<M := (hpos 0).trans_le (Finite.le_ciSup b 0)
  have sq (i : Fin 10) : fourthRoot (a i) = b i^2 := (Real.sq_sqrt (Real.sqrt_nonneg _)).symm
  simp only [rootDistortion,sq]
  change 1 ≤ Real.sqrt (∑ i, b i^2)/M ∧ Real.sqrt (∑ i,b i^2)/M ≤ Real.sqrt 10
  constructor
  · rw [one_le_div mpos]
    obtain ⟨i,hi⟩ := exists_eq_ciSup_of_finite (f:=b)
    change b i=M at hi
    rw [←hi]
    exact Real.le_sqrt_of_sq_le (Finset.single_le_sum (fun j _ => sq_nonneg (b j)) (Finset.mem_univ i))
  · rw [div_le_iff₀ mpos]
    have h : (∑ i, b i^2) ≤ 10*M^2 := by
      calc _ ≤ ∑ _i : Fin 10, M^2 := Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (hpos i).le (Finite.le_ciSup b i) _
           _ = _ := by simp
    simpa only [Real.sqrt_mul (by norm_num : (0:ℝ)≤10),Real.sqrt_sq mpos.le] using Real.sqrt_le_sqrt h

theorem correction_bounds {K : Type*} [Field K] [NumberField K] (w : Fin 10 → K)
    (nonzero : ∀ i, w i≠0) :
    0≤branchCorrection w ∧ branchCorrection w≤ Real.log 10/2 := by
  classical
  have L (φ : K →+* ℂ) : 0≤Real.log (rootDistortion (fun i => ‖φ (w i)‖)) ∧
      Real.log (rootDistortion (fun i => ‖φ (w i)‖)) ≤ Real.log 10/2 := by
    have h := distortion_bounds (fun i => ‖φ (w i)‖)
      (fun i => norm_pos_iff.mpr ((map_ne_zero φ).mpr (nonzero i)))
    exact ⟨Real.log_nonneg h.1,(Real.log_le_log (zero_lt_one.trans_le h.1) h.2).trans_eq
      (Real.log_sqrt (by norm_num))⟩
  have dim : 0<(Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  unfold branchCorrection
  refine ⟨div_nonneg (Finset.sum_nonneg fun σ _ => (L σ).1) dim.le,(div_le_iff₀ dim).mpr ?_⟩
  calc
    _ ≤ ∑ _σ : K →+* ℂ, Real.log 10/2 := Finset.sum_le_sum fun σ _ => (L σ).2
    _ = _ := by simp [NumberField.Embeddings.card, mul_comm]

end
end ZInQBlueprint.SixMetric
#print axioms ZInQBlueprint.SixMetric.distortion_bounds
#print axioms ZInQBlueprint.SixMetric.correction_bounds

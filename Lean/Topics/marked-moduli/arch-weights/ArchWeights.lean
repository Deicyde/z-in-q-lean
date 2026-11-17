import ArchRootBound
import NormalizedFibre

/-! Uniform bounds for the ten pair-of-triples weights on the bounded real chart. -/
namespace ZInQBlueprint.BranchDepth
open Polynomial DirectCharts BranchFormula
noncomputable section

/-- The common upper bound obtained by bounding a close difference and the two remaining
differences in each triple. The normalization used here is division by the sum. -/
def archBound : ℝ := (800*64^2)^4 / (144*27^2)

private theorem close_pair (r : Fin 6 → ℂ) {s : ℝ}
    (hc : ∀ i, ‖r i‖ ≤ s ∨ ‖r i+3‖ ≤ s) (i j k : Fin 6) :
    ‖r i-r j‖ ≤ 2*s ∨ ‖r i-r k‖ ≤ 2*s ∨ ‖r j-r k‖ ≤ 2*s := by
  have near0 (a b : Fin 6) (ha : ‖r a‖ ≤ s) (hb : ‖r b‖ ≤ s) :
      ‖r a-r b‖ ≤ 2*s := by linarith [norm_sub_le (r a) (r b)]
  have near3 (a b : Fin 6) (ha : ‖r a+3‖ ≤ s) (hb : ‖r b+3‖ ≤ s) :
      ‖r a-r b‖ ≤ 2*s := by
    have eq : (r a+3)-(r b+3) = r a-r b := by ring
    have h := norm_sub_le (r a+3) (r b+3)
    rw [eq] at h
    linarith
  rcases hc i with hi|hi <;> rcases hc j with hj|hj <;> rcases hc k with hk|hk <;>
    first | exact .inl (near0 _ _ hi hj) | exact .inl (near3 _ _ hi hj)
          | exact .inr (.inl (near0 _ _ hi hk)) | exact .inr (.inl (near3 _ _ hi hk))
          | exact .inr (.inr (near0 _ _ hj hk)) | exact .inr (.inr (near3 _ _ hj hk))

private theorem triangle_norm {t : ℝ} (ht : |t| ≤ 6) (r : Fin 6 → ℂ)
    (hr : ∀ i, (monicSextic (t:ℂ)).IsRoot (r i)) (i j k : Fin 6) :
    ‖triangle r i j k‖ ≤ (800*64^2) * Real.sqrt |t| := by
  have far (a b : Fin 6) : ‖r a-r b‖ ≤ 64 := by
    linarith [norm_sub_le (r a) (r b),small_chart_norm ht (hr a),small_chart_norm ht (hr b)]
  have H := close_pair r (fun a => near_one_center ht (hr a)) i j k
  rw [triangle,norm_mul,norm_mul]
  rcases H with h|h|h
  · calc _ ≤ (2*(400 * Real.sqrt |t|))*64*64 := by gcongr <;> apply far
         _ = _ := by ring
  · calc _ ≤ 64*(2*(400 * Real.sqrt |t|))*64 := by gcongr <;> apply far
         _ = _ := by ring
  · calc _ ≤ 64*64*(2*(400 * Real.sqrt |t|)) := by gcongr <;> apply far
         _ = _ := by ring

theorem weight_norm_small {t : ℝ} (ht : |t| ≤ 6) (r : Fin 6 → ℂ)
    (hr : ∀ i, (monicSextic (t:ℂ)).IsRoot (r i)) (i : Fin 10) :
    ‖weight r i‖ ≤ (800*64^2)^4 * |t|^2 := by
  unfold weight
  simp only [norm_pow,norm_mul]
  let d : ℝ := 800*64^2
  have H := triangle_norm ht r hr
  calc _ ≤ ((d * Real.sqrt |t|) * (d * Real.sqrt |t|))^2 := by gcongr <;> apply H
       _ = _ := by
         change _ = d^4 * |t|^2
         rw [show d * Real.sqrt |t| * (d * Real.sqrt |t|)=d^2*(Real.sqrt |t|)^2 by ring,
           Real.sq_sqrt (abs_nonneg t)]
         ring

theorem roots_of_factorization {t : ℂ} (r : Fin 6 → ℂ)
    (he : (∏ i, (X-C (r i))) = monicSextic t) (i : Fin 6) :
    (monicSextic t).IsRoot (r i) := by
  rw [← he,IsRoot.def,eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem normalized_bound_small {t : ℝ} (ht : |t| ≤ 6) (hn : t ≠ 0) (r : Fin 6 → ℂ)
    (he : (∏ i, (X-C (r i))) = monicSextic (t:ℂ)) (i : Fin 10) :
    ‖normalized (weight r) i‖ ≤ archBound := by
  have h := weight_norm_small ht r (roots_of_factorization r he) i
  have d : ‖∑ i, weight r i‖ = 144 * |t|^2 * (t^2+27)^2 := by
    rw [monic_weight_sum r _ he]
    norm_cast
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_pow,abs_pow,abs_of_nonneg (by positivity : 0 ≤ t^2+27)]
    norm_num
  rw [normalized,norm_div,d]
  have ht' : 0 < |t| := abs_pos.mpr hn
  apply (div_le_iff₀ (by positivity)).mpr
  unfold archBound
  have lower : (27:ℝ)^2 ≤ (t^2+27)^2 := by nlinarith [sq_nonneg (t^2),sq_nonneg t]
  calc _ ≤ (800*64^2)^4 * |t|^2 := h
       _ = (800*64^2)^4/(144*27^2) * (144*|t|^2*27^2) := by ring
       _ ≤ _ := by gcongr

end
end ZInQBlueprint.BranchDepth
#print axioms ZInQBlueprint.BranchDepth.weight_norm_small
#print axioms ZInQBlueprint.BranchDepth.normalized_bound_small

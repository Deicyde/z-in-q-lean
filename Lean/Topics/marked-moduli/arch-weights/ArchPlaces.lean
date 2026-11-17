import ArchReciprocal
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The product over infinite places in the projective-height formula. -/
namespace ZInQBlueprint.BranchDepth
open Polynomial NumberField SexticThetaHeight
noncomputable section

theorem infinite_factor_bound {K : Type*} [Field K] [NumberField K]
    {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    (r : Fin 6 → K) (hr : Function.Injective r) (hz : ∀ j, aeval (r j) (sextic u δ)=0) :
    (∏ w : InfinitePlace K, (⨆ i, w (normalized (weight r) i))^w.mult) ≤
      archBound ^ Module.finrank ℚ K := by
  classical
  let x := normalized (weight r)
  have hlocal (w : InfinitePlace K) : (⨆ i, w (x i)) ≤ archBound := by
    apply ciSup_le
    intro i
    rw [← w.norm_embedding_eq]
    exact embedding_bound_paper w.embedding hu hδ r hr hz i
  have hpos (w : InfinitePlace K) : 0 ≤ ⨆ i, w (x i) :=
    le_trans (w.1.nonneg _) (Finite.le_ciSup (f := fun i => w (x i)) 0)
  calc _ ≤ ∏ w : InfinitePlace K, archBound^w.mult := by
          apply Finset.prod_le_prod₀
          · intro w _; exact pow_nonneg (hpos w) _
          · intro w _; exact pow_le_pow_left₀ (hpos w) (hlocal w) _
       _ = _ := by rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

/-- The explicit numerical loss in a normalized logarithmic height is less than 49. -/
theorem log_archBound_lt : Real.log archBound < 49 := by
  have lo : (27/10:ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have pow : (27/10:ℝ)^49 < (Real.exp 1)^49 := pow_lt_pow_left₀ lo (by norm_num) (by norm_num)
  have bound : archBound < (27/10:ℝ)^49 := by norm_num [archBound]
  apply (Real.log_lt_iff_lt_exp (by norm_num [archBound] : 0 < archBound)).mpr
  calc archBound < (Real.exp 1)^49 := bound.trans pow
       _ = Real.exp 49 := by rw [← Real.exp_nat_mul]; norm_num

private theorem normalized_sum_embedded {K : Type*} [Field K] [CharZero K] (σ : K →+* ℂ)
    {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    (r : Fin 6 → K) (hr : Function.Injective r) (hz : ∀ j, aeval (r j) (sextic u δ)=0) :
    ∑ i, weight r i ≠ 0 := by
  let e : K →ₐ[ℚ] ℂ := σ.toRatAlgHom
  have ht := (SexticIgusaChart.unmarked hu hδ).1
  let t := SexticIgusaChart.parameter u
  have hn : (t:ℂ) ≠ 0 := by exact_mod_cast ht
  have hd : (t:ℂ)^2+27 ≠ 0 := by exact_mod_cast (by positivity : (t:ℚ)^2+27 ≠ 0)
  have roots (j : Fin 6) : (DirectCharts.monicSextic (t:ℂ)).IsRoot (σ (r j)) := by
    have h : aeval (e (r j)) (sextic u δ)=0 := by rw [aeval_algHom_apply,hz j,map_zero]
    exact paper_monic_root hu hδ h
  have he := monic_factorization (σ ∘ r) (σ.injective.comp hr) roots
  have sum := monic_weight_sum (σ ∘ r) (t:ℂ) he
  have hn' : ∑ i, weight (σ ∘ r) i ≠ 0 := by rw [sum]; exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hn)) (pow_ne_zero _ hd)
  intro h
  apply hn'
  have hh := congrArg σ h
  simpa [weight,triangle,map_sum] using hh

/-- The logarithmic infinite-place contribution per absolute degree is uniformly < 49. -/
theorem normalized_arch_log_lt {K : Type*} [Field K] [NumberField K]
    {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    (r : Fin 6 → K) (hr : Function.Injective r) (hz : ∀ j, aeval (r j) (sextic u δ)=0) :
    Real.log (∏ w : InfinitePlace K, (⨆ i, w (normalized (weight r) i))^w.mult) /
      (Module.finrank ℚ K:ℝ) < 49 := by
  classical
  obtain ⟨σ⟩ := (inferInstance : Nonempty (K →+* ℂ))
  have hsum := normalized_sum_embedded σ hu hδ r hr hz
  obtain ⟨i,hi⟩ : ∃ i,weight r i ≠ 0 := by
    by_contra! h
    exact hsum (by simp [h])
  have hi' : normalized (weight r) i ≠ 0 := div_ne_zero hi hsum
  have lp (w : InfinitePlace K) : 0 < ⨆ j, w (normalized (weight r) j) :=
    lt_of_lt_of_le ((InfinitePlace.pos_iff).mpr hi') (Finite.le_ciSup (f := fun j => w (normalized (weight r) j)) i)
  have H := infinite_factor_bound hu hδ r hr hz
  have hprod : 0 < ∏ w : InfinitePlace K, (⨆ i, w (normalized (weight r) i))^w.mult :=
    Finset.prod_pos (fun w _ => pow_pos (lp w) _)
  have hlog := Real.log_le_log hprod H
  rw [Real.log_pow] at hlog
  have hdegree : 0 < (Module.finrank ℚ K:ℝ) := by exact_mod_cast Module.finrank_pos (R:=ℚ) (M:=K)
  apply (div_lt_iff₀ hdegree).mpr
  exact hlog.trans_lt (by nlinarith [mul_pos hdegree (sub_pos.mpr log_archBound_lt)])

end
end ZInQBlueprint.BranchDepth
#print axioms ZInQBlueprint.BranchDepth.infinite_factor_bound
#print axioms ZInQBlueprint.BranchDepth.log_archBound_lt
#print axioms ZInQBlueprint.BranchDepth.normalized_arch_log_lt

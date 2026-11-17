import ArchWeights
import FixedBranch

/-! Transfer of the bounded chart estimate to every real parameter and every complex
embedding at every unmarked rational parameter of the paper. -/
namespace ZInQBlueprint.BranchDepth
open Polynomial DirectCharts IntegralSextic SexticThetaHeight SexticIgusaChart
noncomputable section
set_option maxHeartbeats 800000

/-- Six distinct labelled roots determine the factorization of a complex monic sextic. -/
theorem monic_factorization {t : ℂ} (r : Fin 6 → ℂ) (hr : Function.Injective r)
    (hz : ∀ i, (monicSextic t).IsRoot (r i)) : (∏ i, (X-C (r i))) = monicSextic t := by
  classical
  let f := monicSextic t
  let e : Fin 6 ↪ ℂ := ⟨r,hr⟩
  let S := Finset.univ.map e
  have hc : S.card=6 := by simp [S]
  have hd : f.natDegree=6 := (monic_six _).2
  have hR : f.roots = S.val := roots_eq_of_natDegree_le_card_of_ne_zero (fun x hx => by
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    exact hz i) (hd.trans hc.symm).le (monic_six _).1.ne_zero
  have h := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := f) (hR ▸ hc.trans hd.symm)
  rw [hR,(monic_six t).1.leadingCoeff,map_one,one_mul] at h
  convert h using 1
  change (∏ i, (X-C (r i))) = ∏ x ∈ S, (X-C x)
  rw [Finset.prod_map]
  rfl

private theorem root_ne_zero {t x : ℂ} (ht : t ≠ 0) (hx : (monicSextic t).IsRoot x) : x ≠ 0 := by
  rintro rfl
  simp [IsRoot.def,monic_eval,form,alpha,beta,gamma,ht] at hx

/-- The involution on the monic parameter chart transforms both the parameter and the root. -/
theorem reciprocal_root {t x : ℂ} (ht : t ≠ 0) (hx : (monicSextic t).IsRoot x) :
    (monicSextic (27/t)).IsRoot (6/x) := by
  have hn := root_ne_zero ht hx
  have h : form 1 t x 1=0 := (monic_eval t x).symm.trans hx.eq_zero
  rw [IsRoot.def,monic_eval]
  have eq : t^2*x^6 * form 1 (27/t) (6/x) 1 = 5832*form 1 t x 1 := by
    unfold form alpha beta gamma
    field_simp [ht,hn]
    ring
  have hp : t^2*x^6 ≠ 0 := mul_ne_zero (pow_ne_zero _ ht) (pow_ne_zero _ hn)
  exact (mul_eq_zero.mp (eq.trans (by rw [h,mul_zero]))).resolve_left hp

/-- Uniform for all nonzero real parameters and all labellings of the six distinct roots. -/
theorem normalized_bound_real {t : ℝ} (ht : t ≠ 0) (r : Fin 6 → ℂ) (hr : Function.Injective r)
    (hz : ∀ i, (monicSextic (t:ℂ)).IsRoot (r i)) (i : Fin 10) :
    ‖normalized (weight r) i‖ ≤ archBound := by
  by_cases hs : |t| ≤ 6
  · exact normalized_bound_small hs ht r (monic_factorization r hr hz) i
  have htC : (t:ℂ) ≠ 0 := by exact_mod_cast ht
  have hR (j : Fin 6) : r j ≠ 0 := root_ne_zero htC (hz j)
  let s (j : Fin 6) : ℂ := 6 / r j
  have hinj : Function.Injective s := by
    intro a b h
    apply hr
    change 6 / r a = 6 / r b at h
    have he := (div_eq_div_iff (hR a) (hR b)).mp h
    linear_combination -he/6
  have hz' (j : Fin 6) : (monicSextic (((27/t:ℝ):ℂ))).IsRoot (s j) := by
    push_cast
    exact reciprocal_root htC (hz j)
  have bound : |27/t| ≤ 6 := by
    rw [abs_div,abs_of_pos (by norm_num : 0 < (27:ℝ)), div_le_iff₀ (abs_pos.mpr ht)]
    linarith [lt_of_not_ge hs]
  have H := normalized_bound_small bound (div_ne_zero (by norm_num) ht) s
    (monic_factorization s hinj hz') i
  have eq := normalized_mobius r 0 6 1 0 (by norm_num) (by simpa using hR) i
  rw [← eq]
  simpa [s,mobius] using H

private theorem monic_aeval {t : ℚ} (x : ℂ) :
    aeval x (monicSextic t) = (monicSextic (t:ℂ)).eval x := by
  norm_num [monicSextic,form,alpha,beta,gamma,map_ofNat]

/-- The rational analytic sextic is a nonzero scalar multiple of the monic chart for every twist. -/
theorem paper_monic_root {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    {x : ℂ} (hx : aeval x (sextic u δ)=0) : (monicSextic (parameter u:ℂ)).IsRoot x := by
  have hs := (unmarked hu hδ).2.1
  rw [sextic,map_mul,aeval_C,monic_aeval] at hx
  exact (mul_eq_zero.mp hx).resolve_left (by simpa only [map_zero] using (algebraMap ℚ ℂ).injective.ne hs)

/-- Every nonzero rational twist at an unmarked rational parameter has the same absolute bound. -/
theorem normalized_bound_paper {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    (r : Fin 6 → ℂ) (hr : Function.Injective r) (hz : ∀ j, aeval (r j) (sextic u δ)=0)
    (i : Fin 10) : ‖normalized (weight r) i‖ ≤ archBound := by
  apply normalized_bound_real (t := (parameter u:ℝ)) (by exact_mod_cast (unmarked hu hδ).1) r hr _ i
  intro j
  simpa using paper_monic_root hu hδ (hz j)

/-- The same statement for the exact finite chart of the glued, squarefree-twisted paper model. -/
theorem normalized_bound_fixed {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (r : Fin 6 → ℂ) (hr : Function.Injective r)
    (hz : ∀ j, aeval (r j) (BinaryCover.paper ℚ u false)=0) (i : Fin 10) :
    ‖normalized (weight r) i‖ ≤ archBound :=
  normalized_bound_paper hu (by exact_mod_cast (GlobalTwist.delta_pos u).ne') r hr
    (fun j => (BinaryCover.paper_root_iff hu _).mp (hz j)) i

/-- The estimate holds simultaneously for every complex embedding of a root field,
including every complex embedding defining an infinite place of a number field. -/
theorem embedding_bound_paper {K : Type*} [Field K] [CharZero K] (σ : K →+* ℂ)
    {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    (r : Fin 6 → K) (hr : Function.Injective r) (hz : ∀ j, aeval (r j) (sextic u δ)=0)
    (i : Fin 10) : ‖σ (normalized (weight r) i)‖ ≤ archBound := by
  have hroot (j : Fin 6) : aeval (σ (r j)) (sextic u δ)=0 := by
    let e : K →ₐ[ℚ] ℂ := σ.toRatAlgHom
    change aeval (e (r j)) (sextic u δ)=0
    rw [aeval_algHom_apply,hz j,map_zero]
  have h := normalized_bound_paper hu hδ (σ ∘ r) (σ.injective.comp hr) hroot i
  simpa [normalized,weight,triangle,map_sum] using h

end
end ZInQBlueprint.BranchDepth
#print axioms ZInQBlueprint.BranchDepth.reciprocal_root
#print axioms ZInQBlueprint.BranchDepth.normalized_bound_real
#print axioms ZInQBlueprint.BranchDepth.normalized_bound_paper
#print axioms ZInQBlueprint.BranchDepth.normalized_bound_fixed
#print axioms ZInQBlueprint.BranchDepth.embedding_bound_paper

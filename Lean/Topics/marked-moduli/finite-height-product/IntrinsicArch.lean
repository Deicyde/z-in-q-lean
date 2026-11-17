import ArchPlaces
import EmbeddedBranches

/-! Archimedean estimates for the intrinsic ratio field, which need not contain the roots. -/
namespace ZInQBlueprint.BranchDepth
open Polynomial NumberField BranchHeight BranchFormula ContactInvariant ThetaPeriod SexticThetaHeight
noncomputable section
/-- The intrinsic sum-normalized coordinates equal the normalized squared Vandermonde products. -/
theorem sumWeights_normalized {r : Fin 6 → ℂ} (hr : Function.Injective r) (i : Fin 10) :
    ((sumWeights r i:weightField r):ℂ) = normalized (weight r) i := by
  let b (j : Fin 10) := branchValue (finiteBranches r) (pairs j)
  have eq : weight r = fun j => (denominator r)^4*b j := by
    funext j
    rw [complex_weight,← clear_row hr]
    exact mul_comm ..
  rw [eq,normalized_scaling b (pow_ne_zero _ (denominator_ne hr))]
  exact sumWeights_complex hr i

/-- Extend an embedding of the coordinate field to the joint root field and evaluate the
same rational functions there. This proves the bound at every intrinsic infinite place. -/
theorem coordinate_embedding_bound {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ j, aeval (r j) (sextic u δ)=0)
    (σ : weightField r →+* ℂ) (i : Fin 10) : ‖σ (sumWeights r i)‖ ≤ archBound := by
  obtain ⟨z,hinj,hz',hcoords⟩ := BranchPlaces.embedded_branches hu hδ hr hz σ
  rw [hcoords i]
  exact normalized_bound_paper hu hδ z hinj hz' i

/-- Product of the true local maxima over the infinite places of the intrinsic field. -/
theorem intrinsic_infinite_factor {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ j, aeval (r j) (sextic u δ)=0) :
    letI := weight_numberField hu hδ hz
    (∏ w : InfinitePlace (weightField r), (⨆ i, w (sumWeights r i))^w.mult) ≤
      archBound ^ Module.finrank ℚ (weightField r) := by
  let := weight_numberField hu hδ hz
  classical
  have local_bound (w : InfinitePlace (weightField r)) : (⨆ i, w (sumWeights r i)) ≤ archBound := by
    apply ciSup_le
    intro i
    rw [← w.norm_embedding_eq]
    exact coordinate_embedding_bound hu hδ hr hz _ i
  calc _ ≤ ∏ w : InfinitePlace (weightField r), archBound^w.mult := by
          apply Finset.prod_le_prod₀
          · intro w _; exact pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass w.val _) _
          · intro w _; exact pow_le_pow_left₀ (Real.iSup_nonneg_of_nonnegHomClass w.val _) (local_bound w) _
       _ = _ := by rw [Finset.prod_pow_eq_pow_sum,InfinitePlace.sum_mult_eq]

end
end ZInQBlueprint.BranchDepth
#print axioms ZInQBlueprint.BranchDepth.sumWeights_normalized
#print axioms ZInQBlueprint.BranchDepth.coordinate_embedding_bound
#print axioms ZInQBlueprint.BranchDepth.intrinsic_infinite_factor

import SumNormalizedOrders
import NormalizedFibre
import BranchFields

/-! Lifting each prescribed intrinsic branch-field embedding to its six ordered roots. -/
open Polynomial
namespace ZInQBlueprint.BranchPlaces
open BranchHeight BranchDepth ContactInvariant SexticThetaHeight
noncomputable section

theorem map_weight {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (r : Fin 6 → K) (i : Fin 10) : f (weight r i)=weight (fun j => f (r j)) i := by
  simp [weight,triangle]

theorem map_normalized {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (v : Fin 10 → K) (i : Fin 10) :
    f (normalized v i)=normalized (fun j => f (v j)) i := by simp [normalized]

/-- Under a specified embedding of the intrinsic field, its actual normalized coordinates
are computed from a six-root labeling in any algebraically closed field of characteristic zero. -/
theorem embedded_branches {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ≠0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ)=0)
    {Ω : Type*} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (σ : weightField r →+* Ω) :
    ∃ z : Fin 6 → Ω, Function.Injective z ∧
      (∀ i, aeval (z i) (sextic u δ)=0) ∧
      (∀ i, σ (sumWeights r i)=normalized (weight z) i) := by
  classical
  let f := sextic u δ
  have hd := (smooth_sextic hu hδ).1
  have hF : f ≠ 0 := by intro h; change f.natDegree=6 at hd; simp [h] at hd
  let T := IntermediateField.adjoin ℚ (f.rootSet ℂ)
  have ht (i : Fin 6) : r i ∈ T :=
    IntermediateField.subset_adjoin ℚ _ (mem_rootSet.mpr ⟨hF,hz i⟩)
  let y : Fin 6 → T := fun i => ⟨r i,ht i⟩
  let j := IntermediateField.inclusion (weightField_le ht)
  let : Algebra (weightField r) T := j.toRingHom.toAlgebra
  let : Algebra (weightField r) Ω := σ.toAlgebra
  let : IsSplittingField ℚ T f := IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  let : FiniteDimensional ℚ T := IsSplittingField.finiteDimensional T f
  let : FiniteDimensional (weightField r) T := FiniteDimensional.right ℚ (weightField r) T
  let : Module.IsTorsionFree (weightField r) T := Module.IsTorsionFree.of_smul_eq_zero (by
    intro a x h
    rw [Algebra.smul_def] at h
    exact (mul_eq_zero.mp h).imp (fun h => (map_eq_zero _).mp h) id)
  let τ : T →ₐ[weightField r] Ω := IsAlgClosed.lift
  have agree (a : weightField r) : τ (j a)=σ a := τ.commutes a
  let z : Fin 6 → Ω := fun i => τ (y i)
  have hy : Function.Injective y := fun _ _ h => hr (congrArg (fun v:T => (v:ℂ)) h)
  refine ⟨z,τ.injective.comp hy,?_,?_⟩
  · intro i
    have hzy : aeval (y i) f = 0 := by
      apply T.val.injective
      change T.val (aeval (y i) f) = T.val 0
      rw [← aeval_algHom_apply T.val (y i) f,map_zero]
      exact hz i
    change aeval (τ.toRingHom.toRatAlgHom (y i)) f=0
    rw [aeval_algHom_apply,hzy,map_zero]
  · have hpr (i : Fin 10) : j (weights r i) = weight y i / weight y 0 := by
      apply T.val.injective
      change branchRatio r i = T.val.toRingHom (weight y i / weight y 0)
      rw [map_div₀,map_weight,map_weight]
      exact projective_branch_ratio hr i
    have h0 : weight y 0 ≠ 0 := by
      intro h
      have hb : weights r 0 ≠ 0 := by
        change (⟨branchRatio r 0,_⟩ : weightField r) ≠ 0
        intro he
        have hv := congrArg (weightField r).val he
        change branchRatio r 0=0 at hv
        simp only [branchRatio,div_self (ThetaPeriod.branchValue_nonzero _ (ThetaPeriod.finiteBranches_injective hr) _)] at hv
        exact one_ne_zero hv
      apply hb
      apply j.injective
      simp [hpr,h]
    intro i
    rw [←agree]
    have jsum : j (sumWeights r i)=normalized (weight y) i := by
      simp only [sumWeights,map_div₀,map_sum,hpr]
      change normalized (fun k => weight y k / weight y 0) i = _
      simpa only [div_eq_inv_mul] using normalized_scaling (weight y) (inv_ne_zero h0) i
    rw [jsum]
    change τ.toRingHom (normalized (weight y) i)=_
    rw [map_normalized]
    simp only [map_weight]
    rfl

end
end ZInQBlueprint.BranchPlaces
#print axioms ZInQBlueprint.BranchPlaces.map_weight
#print axioms ZInQBlueprint.BranchPlaces.map_normalized
#print axioms ZInQBlueprint.BranchPlaces.embedded_branches

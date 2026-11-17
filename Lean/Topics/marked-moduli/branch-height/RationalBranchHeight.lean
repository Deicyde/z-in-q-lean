import BranchWeilHeight
import FixedBranch

/-! The projective branch coordinates are defined over a number field without choosing periods. -/
namespace ZInQBlueprint.BranchHeight
open Polynomial ThetaPeriod ThetaQuotient BranchFormula SexticThetaHeight
noncomputable section

/-- The ratios of the ten branch weights are coordinates on a chart of projective 9-space. -/
def branchRatio (r : Fin 6 → ℂ) (i : Fin 10) : ℂ :=
  branchValue (finiteBranches r) (pairs i) / branchValue (finiteBranches r) (pairs 0)

def weightField (r : Fin 6 → ℂ) := IntermediateField.adjoin ℚ (Set.range (branchRatio r))

def weights (r : Fin 6 → ℂ) (i : Fin 10) : weightField r :=
  ⟨branchRatio r i, IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)⟩

theorem weight_numberField {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    {r : Fin 6 → ℂ} (hr : ∀ i, aeval (r i) (sextic u δ) = 0) : NumberField (weightField r) := by
  have ha := finiteBranches_algebraic (fun i => sextic_root_algebraic hu hδ (hr i))
  have hi (i : Fin 10) := branchValue_algebraic (finiteBranches r) ha (pairs i)
  let : FiniteDimensional ℚ (weightField r) := IntermediateField.finiteDimensional_adjoin (by
    rintro x ⟨i,rfl⟩
    exact ((hi i).isIntegral.mul (hi 0).inv.isIntegral))
  exact NumberField.of_module_finite ℚ _

/-- The reduced equation uses only ratios of algebraic branch values. -/
theorem paper_pair {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ) = 0) :
    (∑ i, weights r i) ≠ 0 ∧
    (SixContact.J u : weightField r)^2 =
      ((3779136:weightField r)^2 * ∏ i, weights r i) / (∑ i, weights r i)^10 := by
  let b := fun i : Fin 10 => branchValue (finiteBranches r) (pairs i)
  have hb (i : Fin 10) : b i ≠ 0 :=
    branchValue_nonzero _ (finiteBranches_injective hr) _
  have hji := (CoarseConic.unmarked_range hu).2.ne
  have hj : (SixContact.J u : ℂ) ≠ 0 := by exact_mod_cast hji
  have he := sextic_branch_invariant hu hδ r hr hz pairs
  rw [invariant hu hδ] at he
  push_cast at he
  change (∑ i, b i)^10/(∏ i, b i) = (3779136/(SixContact.J u : ℂ))^2 at he
  let w := branchRatio r
  have hp : (∏ i, w i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => div_ne_zero (hb i) (hb 0)
  have hk := quotient_of_scaling b w (hb 0) (fun i => div_mul_cancel₀ (b i) (hb 0))
  have e := hk.trans he
  have hs : (∑ i, w i) ≠ 0 := by
    intro h
    rw [h,zero_pow (by decide),zero_div] at e
    exact (pow_ne_zero 2 (div_ne_zero (by norm_num) hj)) e.symm
  have hfield : (∑ i, weights r i) ≠ 0 := by
    intro h
    apply hs
    have hw := congrArg (weightField r).val h
    rw [map_sum,map_zero] at hw
    exact hw
  refine ⟨hfield, ?_⟩
  apply (weightField r).val.injective
  change (SixContact.J u : ℂ)^2 = ((3779136:ℂ)^2 * ∏ i, w i)/(∑ i, w i)^10
  field_simp [hj,hp] at e
  apply (eq_div_iff (pow_ne_zero 10 hs)).2
  linear_combination e

/-- A height bound without a period matrix, a theta tuple or an ordering hypothesis. -/
theorem paper_J_height {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ) = 0) :
    letI := weight_numberField hu hδ hz
    ZInQ.ratHeight (SixContact.J u) ≤ 5 * normalizedHeight (weights r) + Real.log 3779136 := by
  let := weight_numberField hu hδ hz
  obtain ⟨hs,he⟩ := paper_pair hu hδ hr hz
  exact rational_height _ _ hs he

end
end ZInQBlueprint.BranchHeight
#print axioms ZInQBlueprint.BranchHeight.weight_numberField
#print axioms ZInQBlueprint.BranchHeight.paper_pair
#print axioms ZInQBlueprint.BranchHeight.paper_J_height

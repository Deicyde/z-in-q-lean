import BranchFields
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! Splitting a sextic as three quadratics bounds the degree of its ten branch ratios. -/
namespace ZInQBlueprint.BranchHeight
open Polynomial IntermediateField
noncomputable section

/-- The splitting field of a rational polynomial inside the chosen complex numbers. -/
abbrev complexRootField (q : ℚ[X]) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (q.rootSet ℂ)

private theorem rootField_splitting (q : ℚ[X]) : IsSplittingField ℚ (complexRootField q) q :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)

private theorem rootField_finite (q : ℚ[X]) : FiniteDimensional ℚ (complexRootField q) := by
  let _ := rootField_splitting q
  exact IsSplittingField.finiteDimensional _ q

/-- In characteristic zero the splitting field acts faithfully on its distinct
roots even when the polynomial has a repeated factor. -/
theorem complexRootField_degree (q : ℚ[X]) :
    Module.finrank ℚ (complexRootField q) ≤ q.natDegree.factorial := by
  classical
  let _ := rootField_splitting q
  let _ : IsGalois ℚ q.SplittingField := ⟨⟩
  let _ : Fact ((q.map (algebraMap ℚ ℂ)).Splits) := ⟨IsAlgClosed.splits _⟩
  calc
    Module.finrank ℚ (complexRootField q) = Module.finrank ℚ q.SplittingField :=
      (IsSplittingField.algEquiv (complexRootField q) q).toLinearEquiv.finrank_eq
    _ = Fintype.card q.Gal := by
      rw [← Nat.card_eq_fintype_card]
      exact (IsGalois.card_aut_eq_finrank ℚ q.SplittingField).symm
    _ ≤ Fintype.card (Equiv.Perm (q.rootSet ℂ)) :=
      Fintype.card_le_of_injective _ (Gal.galActionHom_injective q ℂ)
    _ = (Fintype.card (q.rootSet ℂ)).factorial := Fintype.card_perm
    _ ≤ q.natDegree.factorial := Nat.factorial_le (by
      rw [Set.fintypeCard_eq_ncard]
      exact q.ncard_rootSet_le ℂ)

/-- The compositum of the three concrete quadratic splitting fields has
degree at most 2·2·2. Reducible and repeated quadratic factors are allowed. -/
theorem threeQuadratic_degree (q₀ q₁ q₂ : ℚ[X]) (h₀ : q₀.natDegree ≤ 2)
    (h₁ : q₁.natDegree ≤ 2) (h₂ : q₂.natDegree ≤ 2) :
    Module.finrank ℚ ↥(complexRootField q₀ ⊔ complexRootField q₁ ⊔ complexRootField q₂) ≤ 8 := by
  have leTwo (q : ℚ[X]) (hq : q.natDegree ≤ 2) : Module.finrank ℚ (complexRootField q) ≤ 2 :=
    (complexRootField_degree q).trans (Nat.factorial_le hq)
  have h01 := (IntermediateField.finrank_sup_le (complexRootField q₀) (complexRootField q₁)).trans
    (Nat.mul_le_mul (leTwo q₀ h₀) (leTwo q₁ h₁))
  exact (IntermediateField.finrank_sup_le (complexRootField q₀ ⊔ complexRootField q₁)
    (complexRootField q₂)).trans (Nat.mul_le_mul h01 (leTwo q₂ h₂))

/-- The six branch coordinates belong to the compositum as soon as they are
roots of the displayed nonzero product. -/
theorem weightField_degree_three_quadratics (q₀ q₁ q₂ : ℚ[X]) {s : ℚ} (hs : s ≠ 0)
    (h₀ : q₀.natDegree ≤ 2) (h₁ : q₁.natDegree ≤ 2) (h₂ : q₂.natDegree ≤ 2)
    {r : Fin 6 → ℂ} (hr : ∀ i, aeval (r i) (C s * q₀ * q₁ * q₂) = 0)
    (hne₀ : q₀ ≠ 0) (hne₁ : q₁ ≠ 0) (hne₂ : q₂ ≠ 0) :
    Module.finrank ℚ (weightField r) ≤ 8 := by
  let _ := rootField_finite q₀
  let _ := rootField_finite q₁
  let _ := rootField_finite q₂
  let L := complexRootField q₀ ⊔ complexRootField q₁ ⊔ complexRootField q₂
  have hroot (q : ℚ[X]) (hq : q ≠ 0) (z : ℂ) (hz : aeval z q = 0) : z ∈ complexRootField q :=
    IntermediateField.subset_adjoin ℚ _ (mem_rootSet.mpr ⟨hq,hz⟩)
  have hmem : weightField r ≤ L := by
    apply weightField_le
    intro i
    have hz := hr i
    rw [map_mul,map_mul,map_mul,aeval_C] at hz
    have hsc : (algebraMap ℚ ℂ) s ≠ 0 := (_root_.map_ne_zero _).mpr hs
    rcases mul_eq_zero.mp hz with hab | h
    · rcases mul_eq_zero.mp hab with ha | h
      · exact (show complexRootField q₀ ≤ L from le_trans le_sup_left le_sup_left)
          (hroot q₀ hne₀ _ ((mul_eq_zero.mp ha).resolve_left hsc))
      · exact (show complexRootField q₁ ≤ L from le_trans le_sup_right le_sup_left) (hroot q₁ hne₁ _ h)
    · exact (show complexRootField q₂ ≤ L from le_sup_right) (hroot q₂ hne₂ _ h)
  exact (LinearMap.finrank_le_finrank_of_injective (f := (IntermediateField.inclusion hmem).toLinearMap)
    (IntermediateField.inclusion hmem).injective).trans (threeQuadratic_degree q₀ q₁ q₂ h₀ h₁ h₂)

end
end ZInQBlueprint.BranchHeight
#print axioms ZInQBlueprint.BranchHeight.complexRootField_degree
#print axioms ZInQBlueprint.BranchHeight.threeQuadratic_degree
#print axioms ZInQBlueprint.BranchHeight.weightField_degree_three_quadratics

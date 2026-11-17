import BranchHeightCriterion
import ZInQKernel.MainLiterature

/-! The algebraic branch-height criterion at the merged public theorem. -/
namespace ZInQBlueprint.BranchHeight
open HeightBudget ZInQ

theorem paper_J_eq_public (u : ℚ) : SixContact.J u = JHeight.Jmap u := rfl

/-- The bound for the ten branch coordinates implies the public j-form. -/
theorem public_jHeight_of_branchHeight (h : BoundedBranchHeight) : JHeight.JHeightBound Mult.S_mul := by
  intro u hu
  obtain ⟨t, hi, ht⟩ := remaining_of_branchHeight h u hu
  rw [paper_J_eq_public] at hi
  have hc := third_comparison u (vonKaenelBudget u) le_rfl
  change max 1 (vonKaenelBudget u) ≤ JHeight.heightX heightD * (contactSupport Mult.S_mul u : ℝ)^24 at hc
  have hpos : 1 ≤ JHeight.heightX heightD * (contactSupport Mult.S_mul u : ℝ)^24 :=
    (le_max_left 1 _).trans hc
  change ratHeight (JHeight.Jmap u) ≤ _
  rw [mul_assoc]
  linarith only [hi, ht, hc, hpos]

theorem frozen_of_branchHeight_and_literature
    (h : BoundedBranchHeight) (ha : Literature.TYZThm35ReadingA)
    (hc : Literature.HeckeContinuation) (hf : Literature.FunctionalEquation5)
    (hg : Literature.GrossZagier) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_jHeightBound_tyzRow5b_functionalEquation5_grossZagier
    (public_jHeight_of_branchHeight h) (Literature.tyzRow5b_of_readingA ha hc) hf hg

theorem frozen_of_branchHeight_and_TYZInputs
    (h : BoundedBranchHeight) (ht : PropN.TYZInputs) (hf : Literature.FunctionalEquation5)
    (hg : Literature.GrossZagier) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzInputs_functionalEquation5_grossZagier
    (sixContactMin_of_branchHeight h) ht hf hg

end ZInQBlueprint.BranchHeight
#print axioms ZInQBlueprint.BranchHeight.paper_J_eq_public
#print axioms ZInQBlueprint.BranchHeight.public_jHeight_of_branchHeight
#print axioms ZInQBlueprint.BranchHeight.frozen_of_branchHeight_and_literature
#print axioms ZInQBlueprint.BranchHeight.frozen_of_branchHeight_and_TYZInputs

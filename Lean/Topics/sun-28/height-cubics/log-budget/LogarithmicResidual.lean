import BudgetComparison
import ConductorDominance

namespace Sun28.HeightCubics.Pooled.Logarithmic
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.HeightExtension Sun28.HeightExtension.SquareSupport Sun28.HeightBudget Sun28.MinimalConductors
open Sun28.HeightFibres Sun28.HeightFibres.Sharp Sun28.HeightCubics.Refinement
noncomputable section

/-- The remaining inputs are the primitive off-mark slopes evading the old
independent sectors and the single direct chart test. Its numerical failure
bounds and the earlier, coarser conductor failure are consequences. -/
def Remaining : Prop :=
  ∀ A B : ℤ,Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (∀ i,¬SparseRepeated i A B) → glazerConstant24*(oddProduct A B:ℝ)^24<vonKanelBound (best A B) →
    (∀ i b c,¬HeightRefinement.Sharp.Test i A B b c) → ¬HeightBalance.Covered A B →
    ¬HeightBalance.PairCovered A B → ¬Ordinate.Covered A B → ¬ChartTest A B → target A B

theorem pooled_iff_logarithmic : Pooled.Remaining ↔ Remaining := by
  constructor
  · intro previous A B cop off sparse least square four pair ordinate direct
    exact previous A B cop off sparse least square four pair ordinate (fun old=>direct (chart_of_previous cop old))
      direct (Pooled.failure_classes cop direct)
  · intro reduced A B cop off sparse least square four pair ordinate _ direct _
    exact reduced A B cop off sparse least square four pair ordinate direct

theorem original_iff_logarithmic (units:PublishedCorollary72) (pell:PublishedAllPell)
    (classes:PublishedClassRegulator) (formula:QuadraticCharacterDiscriminants)
    (pub:PublishedElliptic) : OriginalFiveHeight glazerConstant24 oldCutoff ↔ Remaining :=
  (original_iff_pooled units pell classes formula pub).trans pooled_iff_logarithmic

end
end Sun28.HeightCubics.Pooled.Logarithmic
#print axioms Sun28.HeightCubics.Pooled.Logarithmic.pooled_iff_logarithmic
#print axioms Sun28.HeightCubics.Pooled.Logarithmic.original_iff_logarithmic

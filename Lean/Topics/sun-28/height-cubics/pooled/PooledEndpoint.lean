import ExplicitBudget
import AllChartProduct

namespace Sun28.HeightCubics.Pooled
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.HeightExtension Sun28.HeightExtension.SquareSupport Sun28.HeightBudget Sun28.MinimalConductors
open Sun28.HeightFibres Sun28.HeightFibres.Sharp Refinement
noncomputable section

def Remaining : Prop :=
  ∀ A B : ℤ,Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (∀ i,¬SparseRepeated i A B) → glazerConstant24*(oddProduct A B:ℝ)^24<vonKanelBound (best A B) →
    (∀ i b c,¬HeightRefinement.Sharp.Test i A B b c) → ¬HeightBalance.Covered A B →
    ¬HeightBalance.PairCovered A B → ¬Ordinate.Covered A B → ¬Refinement.Covered A B → ¬ChartTest A B →
    6^5*heightRadical A B^110*classProduct oldCutoff .oddCube A B^2 <
      35^5*classProduct oldCutoff .evenNoncube A B^3*classProduct oldCutoff .evenCube A B → target A B

theorem refinement_iff_pooled (pub:PublishedElliptic) : Refinement.Remaining ↔ Remaining := by
  constructor
  · exact fun full A B cop off a b c d e f g _ _=>full A B cop off a b c d e f g
  · intro rem A B cop off a b c d e f g
    by_cases h:ChartTest A B
    · exact five_height_of_chart pub cop off h
    · exact rem A B cop off a b c d e f g h (failure_classes cop h)

theorem original_iff_pooled (units:PublishedCorollary72) (pell:PublishedAllPell)
    (classes:PublishedClassRegulator) (formula:QuadraticCharacterDiscriminants)
    (pub:PublishedElliptic) : OriginalFiveHeight glazerConstant24 oldCutoff ↔ Remaining :=
  (original_iff_conductor units pell classes formula pub).trans (refinement_iff_pooled pub)

end
end Sun28.HeightCubics.Pooled
#print axioms Sun28.HeightCubics.Pooled.refinement_iff_pooled
#print axioms Sun28.HeightCubics.Pooled.original_iff_pooled

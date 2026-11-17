import ConductorNumbers
import SupportedCoordinates

namespace Sun28.HeightCubics.Refinement
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.HeightExtension Sun28.HeightExtension.SquareSupport Sun28.HeightBudget Sun28.MinimalConductors
open Sun28.HeightFibres Sun28.HeightFibres.Sharp ZInQBlueprint.TwistDescent
noncomputable section

def Remaining : Prop :=
  ∀ A B : ℤ,Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (∀ i,¬SparseRepeated i A B) → glazerConstant24*(oddProduct A B:ℝ)^24<vonKanelBound (best A B) →
    (∀ i b c,¬HeightRefinement.Sharp.Test i A B b c) → ¬HeightBalance.Covered A B →
    ¬HeightBalance.PairCovered A B → ¬Ordinate.Covered A B → ¬Covered A B → target A B

theorem original_iff_conductor (units:PublishedCorollary72) (pell:PublishedAllPell)
    (classes:PublishedClassRegulator) (formula:QuadraticCharacterDiscriminants)
    (pub:PublishedElliptic) : OriginalFiveHeight glazerConstant24 oldCutoff ↔ Remaining := by
  constructor
  · exact fun h A B cop off _ _ _ _ _ _ _=>h A B cop off
  · intro rem
    apply (Ordinate.original_iff_ordinate units pell classes formula (supported_coordinates pub)).2
    intro A B cop off a b c d e f
    by_cases good:Covered A B
    · exact five_height_of_conductor pub cop off good
    · exact rem A B cop off a b c d e f good

theorem remaining_pair_cost {A B:ℤ} (bad:¬Covered A B) (i j:Fin 5) (ij:i≠j) :
    heightRadical A B^21 < hidden i A B*noncubic j A B^2 :=
  lt_of_not_ge (fun le=>bad (pair_covered i j ij le))

end
end Sun28.HeightCubics.Refinement
#print axioms Sun28.HeightCubics.Refinement.original_iff_conductor
#print axioms Sun28.HeightCubics.Refinement.remaining_pair_cost

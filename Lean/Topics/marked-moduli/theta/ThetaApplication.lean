import ThetaMetric
import IgusaRatio
import ExactThetaHeight

/-! Height of the six-contact invariant from a level-two theta point.
The number field and the theta point may vary with the rational parameter. -/
namespace ZInQBlueprint.ThetaApplication
open ZInQ ZInQBlueprint.HeightBudget ZInQBlueprint.ThetaQuotient
noncomputable section

/-- Analytic input at one fibre. The coordinates and Euclidean metric refer
to a single point. The stable height uses the original Faltings metric. -/
structure Fibre (K : Type) [Field K] [NumberField K] (u : ℚ) where
  coordinates : Fin 16 → K
  embedding : K →+* ℂ
  evenProduct : (∏ i, embedding (coordinates (evenIndices i))) ≠ 0
  absoluteInvariant :
    (∑ i, embedding (coordinates (evenIndices i))^8)^5 / (∏ i, embedding (coordinates (evenIndices i)))^4 =
      3779136 / embedding (SixContact.J u : K)
  stable : ℝ
  comparison : |max 1 (euclideanHeight coordinates) - max 1 (stable + Real.log Real.pi)/2| ≤
    ThetaMetric.pazukiConstant *
      Real.log (min (max 1 (euclideanHeight coordinates)) (max 1 (stable + Real.log Real.pi)) + 2)
  reductionBound : stable ≤ vonKaenelBudget u

theorem coordinate_bound {K : Type} [Field K] [NumberField K] {u : ℚ}
    (hu : u ∉ contactSet) (f : Fibre K u) :
    ratHeight (SixContact.J u) ≤ 40*euclideanHeight f.coordinates := by
  have hn : (SixContact.J u : K) ≠ 0 := by exact_mod_cast (CoarseConic.unmarked_range hu).2.ne
  obtain ⟨hd,hj⟩ := IgusaRatio.quotient_of_absolute (z := f.coordinates ∘ evenIndices)
    hn f.evenProduct f.absoluteInvariant
  exact ratHeight_le_level_two_exact f.coordinates (SixContact.J u) hj hd

theorem fibre_bound {K : Type} [Field K] [NumberField K] {u : ℚ}
    (hu : u ∉ contactSet) (f : Fibre K u) :
    ratHeight (SixContact.J u) ≤ 40*(2:ℝ)^23 * max 1 (vonKaenelBudget u) := by
  have h := ThetaMetric.theta_le _ _ f.comparison
  have hmax : max 1 f.stable ≤ max 1 (vonKaenelBudget u) := max_le_max_left 1 f.reductionBound
  linarith [coordinate_bound hu f]

def HasThetaFibres : Prop := ∀ u : ℚ, u ∉ contactSet →
  ∃ (K : Type) (_ : Field K) (_ : NumberField K), Nonempty (Fibre K u)

theorem remaining_of_fibres (hf : HasThetaFibres) : RemainingComparisons := by
  intro u hu
  obtain ⟨K,_,_,⟨f⟩⟩ := hf u hu
  refine ⟨euclideanHeight f.coordinates, (coordinate_bound hu f).trans (by linarith), ?_⟩
  have h := ThetaMetric.theta_le _ _ f.comparison
  have hs : max 1 f.stable ≤ max 1 (vonKaenelBudget u) := max_le_max_left 1 f.reductionBound
  have h1 := le_max_left (1:ℝ) (vonKaenelBudget u)
  linarith

theorem frozen_of_fibres_and_rank (hf : HasThetaFibres) (hr : RouteK.Rank.CertifiedRankTYZClRk) :
    FrozenTarget :=
  frozen_of_remaining_and_class_rank (remaining_of_fibres hf) hr

end
end ZInQBlueprint.ThetaApplication
#print axioms ZInQBlueprint.ThetaApplication.coordinate_bound
#print axioms ZInQBlueprint.ThetaApplication.fibre_bound
#print axioms ZInQBlueprint.ThetaApplication.remaining_of_fibres
#print axioms ZInQBlueprint.ThetaApplication.frozen_of_fibres_and_rank

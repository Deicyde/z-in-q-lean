import RootHeight
import ZInQKernel.Hypotheses.Height

/-! Effective height comparisons in the public normalization of PR #24. -/
namespace ZInQBlueprint.PublicRankJoin

/-- Three numerical consequences of geometry, on the same rational fibre. -/
def GeometricComparisons (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ ZInQ.contactSet → ∃ stable theta : ℝ,
    ZInQ.ratHeight (SixContact.J u) ≤ 40 * theta + 22 ∧
    theta ≤ (10000 * 2^24) * max 1 stable ∧
    max 1 stable ≤ max 1 (max (ZInQ.heightCcm : ℝ) (ZInQ.heightQ (ZInQ.heightD : ℝ)^17)) *
      (ZInQ.contactSupport S u : ℝ)^24

/-- The rational-root bound in the upstream height convention. -/
theorem root_height (u : ℚ) :
    ZInQ.ratHeight u ≤ ZInQ.ratHeight (SixContact.J u) + 50 :=
  SixContact.root_height u

theorem height_of_comparisons {S : Finset ℕ} (h : GeometricComparisons S)
    (u : ℚ) (hu : u ∉ ZInQ.contactSet) :
    ZInQ.ratHeight u ≤ ZInQ.heightH6 (ZInQ.heightD : ℝ) * (ZInQ.contactSupport S u : ℝ)^24 := by
  obtain ⟨stable, theta, hIgusa, hTheta, hConductor⟩ := h u hu
  have hOne : (1 : ℝ) ≤ max 1 stable := le_max_left _ _
  have hCoord : ZInQ.ratHeight u ≤ (10^13 : ℝ) * max 1 stable := by
    linarith only [root_height u, hIgusa, hTheta, hOne]
  exact six_contact_comparison _ _ _ _ hCoord hConductor

#print axioms root_height
#print axioms height_of_comparisons
end ZInQBlueprint.PublicRankJoin

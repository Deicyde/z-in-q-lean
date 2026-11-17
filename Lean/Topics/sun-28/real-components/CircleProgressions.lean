import HusemollerClassification

/-! A single finite list of representatives works simultaneously for all moduli. -/
namespace Sun28.RealComponents
open Sun28.RealCharts Sun28.RealProjection Sun28.CyclicOrbit Sun28.RealRatio
open scoped Sun28.RealCharts
noncomputable section
local instance : CompactSpace RealPair := compact_pair
local instance : T2Space RealPair := hausdorff_pair
local instance : IsTopologicalAddGroup RealPair := topological_pair

/-- The bound on representatives precedes the signed offset. The representative
for that offset in turn precedes the modulus. -/
theorem uniform_representatives (published : PublishedProposition72) :
    ∃ q : ℕ, 0<q ∧ ∀ h₀ : ℤ, ∃ i : Fin q, ∀ L : ℕ, 0<L →
      ∃ y : DiagonalClosure, L • y =
        (((i.val:ℤ)+1) • generator diagonalGenerator) - h₀ • generator diagonalGenerator := by
  let a := of_open_component diagonalGenerator (openComponent_of_published published)
  refine ⟨a.q,a.positive,fun h₀ => ?_⟩
  obtain ⟨i,hi⟩ := a.representative h₀
  exact ⟨i,fun L hL => a.divide L hL _ hi⟩

end
end Sun28.RealComponents
#print axioms Sun28.RealComponents.uniform_representatives

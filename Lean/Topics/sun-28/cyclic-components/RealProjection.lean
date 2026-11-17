import CyclicComponent
import RealGroupLaw
import TorsionFamily
import ContactLocalSieve
import FiniteWitness

namespace Sun28.RealProjection
open Set Sun28.CyclicOrbit Sun28.RealCharts
open scoped Sun28.RealCharts
noncomputable section

local instance : CompactSpace RealPair := compact_pair
local instance : T2Space RealPair := hausdorff_pair
local instance : IsTopologicalAddGroup RealPair := topological_pair

/-- The only group to consider is the cyclic closure of the named diagonal point. -/
abbrev DiagonalClosure := orbitClosure diagonalGenerator

/-- Application of the classical closed subgroup theorem: the identity component
of this closed subgroup of the product of the two real elliptic curves is open. -/
def OpenComponent : Prop := IsOpen (connectedComponent (0 : DiagonalClosure))

theorem open_of_locally_connected [LocallyConnectedSpace DiagonalClosure] : OpenComponent :=
  isOpen_connectedComponent

/-- For the concrete diagonal elliptic orbit both parameter functions are constructed. -/
theorem fixed_projection (component : OpenComponent)
    (units : FiveMarkUnits.PublishedCorollary72) (height : MinimalConductors.ExactLeastHeight)
    (patterns : NormSieve.PrimeValuesWithResidues) (twists : PairedClasses.Residual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, Sun28.eval28 Concrete.fixedPolynomial x w = 0) ↔ ∃ k : ℤ, x=(k:ℚ) := by
  let a := of_open_component diagonalGenerator component
  let model := parameterModel_on_subgroup DiagonalClosure a (generator_value diagonalGenerator component)
  exact FiniteWitness.fixed_projection a model units height (NormSieve.pattern_iff.mpr patterns)
    (PairedClasses.simultaneous_of_residual twists) x

theorem integer_definition_28 (component : OpenComponent)
    (units : FiveMarkUnits.PublishedCorollary72) (height : MinimalConductors.ExactLeastHeight)
    (patterns : NormSieve.PrimeValuesWithResidues) (twists : PairedClasses.Residual) :
    IntegerDefinition28 := ⟨Concrete.fixedPolynomial,fixed_projection component units height patterns twists⟩

end
end Sun28.RealProjection
#print axioms Sun28.RealProjection.open_of_locally_connected
#print axioms Sun28.RealProjection.fixed_projection
#print axioms Sun28.RealProjection.integer_definition_28

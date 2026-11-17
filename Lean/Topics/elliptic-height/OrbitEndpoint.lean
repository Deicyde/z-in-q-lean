import NumeratorEndpoint
import IntegerOrbit

namespace EllipticHeight
open StructuralReduction ProjectionFibres ProjectionFibres.Actual HeightSpecialization
open QuadraticInt IndependentIndices IndependentIndices.Assembly

/-- Squared multiplicative heights of the selected orbit. Only the additions
and lower doubling inequalities through the specified index are used. -/
structure OrbitNumerators (n w : Nat) where
  W : Nat → Nat
  positive : ∀ i, 0<W i
  origin : W 0=1
  base : W 1=41^2
  selected : W n=w
  firstDouble : W 1^4≤W 2
  lower : ∀ j, j+2≤n → W (j+1)^4≤W (2*(j+1))
  pair : ∀ j, j+2≤n → W (2*(j+1))*W 2≤16*(W (j+2)*W j)^2

theorem OrbitNumerators.bound {n w : Nat} (o : OrbitNumerators n w) : (28^(n^2))^2≤w :=
  o.selected ▸ IntegerOrbit.physical_growth o.W n o.positive o.origin o.base o.firstDouble o.lower o.pair

/-- The full 80-coordinate implication from finite integer norm calculations
at one root, the previously stated local comparisons and the integer fibres. -/
theorem circuit_defines_of_orbit (marked : Bool) (integerFibres : ∀ n : Nat, circuitImage false (n:Rat))
    (selection : ∀ T : Rat, 0≤2*T+1 → T≠0 → circuitImage false T →
      ∃ y : Fin 80→Rat, y 0=T ∧ Binding.V y 9813=0 ∧ ∃ g : NumeratorData (decoded y),
        Nonempty (OrbitNumerators (label g.labels g.factor.row).natAbs (norm g.factor.a).natAbs) ∧
        ScalarCondition (decoded y) g.labels.n₂) :
    ∀ T, circuitImage marked T ↔ InputRestriction.IsInteger T := by
  apply circuit_defines_of_one_numerator marked 28 (by decide) integerFibres
  intro T side nz represented
  obtain ⟨y,hy,hz,g,⟨o⟩,scalar⟩:=selection T side nz represented
  exact ⟨y,hy,hz,g,o.bound,scalar⟩

end EllipticHeight
#print axioms EllipticHeight.OrbitNumerators.bound
#print axioms EllipticHeight.circuit_defines_of_orbit

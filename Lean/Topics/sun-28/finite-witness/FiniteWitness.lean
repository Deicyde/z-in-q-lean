import FiniteSelectionProof
import IntegralPlace
import SieveComparison

namespace Sun28.FiniteWitness
open ZInQ Sun28.Ordinary Sun28.Forward Sun28.FixedPreparation Sun28.PreparedPoles Sun28.RealRatio
open Sun28.ContactFactors ManuscriptV15.Arithmetic
noncomputable section

theorem finite_selection (sieve : ContactSieve.PrimePatterns) : FiniteSelection := by
  apply selection_of_integral_tests sieve
  intro p prime fixed place lie w M q h β n rep hh
  let _ : Fact p.Prime := ⟨prime⟩
  let _ : place.asIdeal.LiesOver (basePrime p prime).asIdeal := lie
  exact OrdinaryIntegrality.ordinaryAt_integral fixed place rep β (dvd_refl _) hh (fun _ => rfl)

theorem finite_selection_of_gaussian (gauss : GaussianTuples) : FiniteSelection :=
  finite_selection (ContactSieve.of_gaussianTuples gauss)

/-- The fixed integer polynomial with 28 rational witnesses, with the restricted
prime pattern and the paired-twist assertion in its archived manuscript form. -/
theorem fixed_projection {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalAddGroup G] (orbit : Orbit G) (model : ParameterModel orbit)
    (units : FiveMarkUnits.PublishedCorollary72) (height : MinimalConductors.ExactLeastHeight)
    (sieve : ContactSieve.PrimePatterns) (twists : ManuscriptV15.Arithmetic.SimultaneousTwists) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, Sun28.eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ k : ℤ,x=(k:ℚ) :=
  projection_from_selection orbit model units height (finite_selection sieve) twists x

theorem integer_definition_28 {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalAddGroup G] (orbit : Orbit G) (model : ParameterModel orbit)
    (units : FiveMarkUnits.PublishedCorollary72) (height : MinimalConductors.ExactLeastHeight)
    (sieve : ContactSieve.PrimePatterns) (twists : ManuscriptV15.Arithmetic.SimultaneousTwists) :
    Sun28.IntegerDefinition28 :=
  ⟨Concrete.fixedPolynomial,fixed_projection orbit model units height sieve twists⟩

end
end Sun28.FiniteWitness
#print axioms Sun28.FiniteWitness.finite_selection
#print axioms Sun28.FiniteWitness.finite_selection_of_gaussian
#print axioms Sun28.FiniteWitness.fixed_projection
#print axioms Sun28.FiniteWitness.integer_definition_28

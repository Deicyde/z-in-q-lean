import CatalogueLevel28
import ParameterLocus

namespace ZInQBlueprint.WildLevel
open Sun28 Sun28.ScalarDepth Sun28.ScalarRankZero Sun28.ConicCovers Sun28.FiveMarkUnits
open Sun28.HeightFibres.Sharp Sun28.RelativeContacts
noncomputable section
set_option maxRecDepth 12000

/-- The independent inverse route keeps the parameter r and the input x on
the same conic cover. At integral x the forward route may use either multiplier. -/
theorem polynomial_of_conic_parameters (realCurves : RealComponents.PublishedProposition72)
    (quadric : ConeCount.PublishedQuadricCount) (units : PublishedCorollary72)
    (pell : HeightBudget.PublishedAllPell) (classes : HeightExtension.PublishedClassRegulator)
    (disc : QuadraticCharacterDiscriminants) (descent : TwoIsogenyRank) (reduction : OddGoodReduction)
    (param : ParameterExceptionalScalarBound) (ord : OrdinaryBound)
    (moments : PrimeValues.FirstMomentInputs) (choice : MultiplierChoice.ChoiceResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ,eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ k : ℤ,x=(k:ℚ) := by
  constructor
  · intro zero
    by_contra nonint
    obtain ⟨A,η,cert⟩ := (Concrete.polynomial_iff_certificate _).1 zero
    apply nonint
    apply Sun28.ScalarDepth.integral A x η cert _ (scalar_after_arithmetic units pell classes disc
      (scalar_of_parameter_exceptions descent reduction param) A x η nonint cert)
    by_cases test : ordinaryTest A η
    · exact indices_of_matches A x η cert test.1 test.2.1 test.2.2
    · exact ord A x η nonint cert test
  · rintro ⟨k,rfl⟩
    exact MultiplierChoice.integer_root realCurves (PrimeValues.surplus_of_moments moments
      (ConeSieve.row_of_congruences (ConeCount.upper_sieve quadric))) choice k

end
end ZInQBlueprint.WildLevel
#print axioms ZInQBlueprint.WildLevel.polynomial_of_conic_parameters

import InputDensity
import WeightedProjection
import OneMatchedScale
import FactorBound

namespace Sun28.ScalarDepth
open ZInQ ZInQ.Mult Height Sun28.Ordinary Sun28.Forward Sun28.WitnessIndices Sun28.FixedPreparation
open Sun28.WitnessHeight Sun28.ScalarLucas Sun28.ScalarHeight Sun28.FiveMarkUnits Sun28.IndexHeights
open Sun28.FactorHeights Sun28.HeightFibres Sun28.HeightFibres.Sharp Sun28.MinimalConductors Sun28.RelativeContacts
noncomputable section

/-- One matched pair in the first nonconstant row suffices at the indicated denominator cost. -/
def firstRowTest (A : Fin 9 → AffineInput) (η : ℚ) : Prop :=
  Matched (pointScale (nineAffine A).doubles fixedMultiplier 1) η ∧
    singleBudget (rootProduct (nineAffine A).doubles fixedMultiplier) η ≤
      ordinary*(unionRadical oldCutoff (slope (nineAffine A).doubles η):ℝ)^24

/-- For concentrated inputs, the remaining conic cases have an explicit lower bound on the denominator. -/
def remainingLocus (x : ℚ) : Prop :=
  (¬∃ i, concentrated x i) ∨ elliptic 4 6 (4*x^2) ∨ elliptic 64 439 (64*x^2) ∨
    (conics x 2 1 1 ∧ allowance x < 2*Real.log 1199+4*Real.log x.den+4) ∨
    (conics x 14 (-35) 7 ∧ allowance x < 2*Real.log 35+2*Real.log x.den+4)

/-- Only actual scalar exceptions that occur in certificates at nonintegral inputs need a bound. -/
def ExceptionalScalarBound : Prop :=
  ∀ (A : Fin 9 → AffineInput) (x η : ℚ), ¬(∃ k : ℤ, x=(k:ℚ)) →
    PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers → HardInput x →
    remainingLocus x →
    x ∈ exceptionalInputs (max x.num.natAbs x.den) → logHeight₁ (beta x) ≤ allowance x

def UnmatchedOrdinaryBound : Prop :=
  ∀ (A : Fin 9 → AffineInput) (x η : ℚ), ¬(∃ k : ℤ, x=(k:ℚ)) →
    PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers → ¬ordinaryTest A η → ¬firstRowTest A η → OrdinaryIndices A η

theorem scalar_of_exceptions (points : ExceptionalScalarBound) : ScalarBound := by
  intro A x η nonint cert hard _
  by_contra! fail
  have actual : remainingLocus x := by
    by_cases conc : ∃ i, concentrated x i
    · have nz : x≠0 := fun eq => nonint ⟨0,by simpa using eq⟩
      rcases concentrated_alternatives nz conc with a|b|c|d
      · exact Or.inr (Or.inl a)
      · exact Or.inr (Or.inr (Or.inl b))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c,fail.trans_le (positive_height c)⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨d,fail.trans_le (negative_height d)⟩)))
    · exact Or.inl conc
  apply not_le_of_gt fail
  by_cases old : logHeight₁ (beta x) ≤ glazerConstant24*(radical x:ℝ)^24
  · exact old.trans ((original_fits x).trans (previous_allowance x))
  · exact points A x η nonint cert hard actual (Finset.mem_filter.mpr
      ⟨(mem_box x _).mpr le_rfl,lt_of_not_ge old⟩)

/-- Both directions for the literal polynomial. Scalar and ordinary hypotheses apply precisely
to the inputs remaining after the explicit tests. -/
theorem projection_of_exceptions (realCurves : RealComponents.PublishedProposition72)
    (quadric : ConeCount.PublishedQuadricCount) (units : PublishedCorollary72)
    (allPell : HeightBudget.PublishedAllPell) (classes : HeightExtension.PublishedClassRegulator)
    (disc : QuadraticCharacterDiscriminants) (scalar : ExceptionalScalarBound) (ord : UnmatchedOrdinaryBound)
    (moments : PrimeValues.FirstMomentInputs) (points : GlobalDescent.DescentResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ, x=(z:ℚ) := by
  apply fixed_projection realCurves quadric units allPell classes disc (scalar_of_exceptions scalar) _ moments points
  intro A y η nonint cert both
  by_cases first : firstRowTest A η
  · exact indices_of_one_match A y η cert first.1 first.2
  · exact ord A y η nonint cert both first

end
end Sun28.ScalarDepth
#print axioms Sun28.ScalarDepth.scalar_of_exceptions
#print axioms Sun28.ScalarDepth.projection_of_exceptions

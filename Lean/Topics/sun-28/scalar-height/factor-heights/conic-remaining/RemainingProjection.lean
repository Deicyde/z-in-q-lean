import RemainingClass

namespace Sun28.ConicRemaining
open Height ZInQ ZInQ.Mult Sun28.ConicArithmetic Sun28.ScalarHeight Sun28.Ordinary Sun28.ConicCovers
open Sun28.ScalarRankZero Sun28.ScalarDepth Sun28.Forward Sun28.WitnessHeight
open Sun28.FixedPreparation Sun28.ScalarLucas Sun28.WitnessIndices Sun28.IndexHeights Sun28.FactorHeights
noncomputable section
attribute [local irreducible] Sun28.Ordinary.glazerConstant24 Sun28.FixedPreparation.fixedMultiplier Sun28.ScalarDepth.floor Sun28.ScalarDepth.allowance
set_option maxRecDepth 1000
set_option maxHeartbeats 100000

/-- No positive parameter at any scalar, independently of its height or the certificate. -/
theorem no_positive_parameter (sel:PositiveSelmerSelection) (rank:ShortCurveBound) (x:ℚ) :
    ¬positiveParameter x := by
  intro positive
  obtain ⟨s,y,rng,sq,quad,third,yn,curve,_mark⟩:=positive_point positive
  have cl:=positive_selected sel rng sq quad third yn curve
  obtain ⟨r,rs⟩:=sq
  obtain ⟨z,az⟩:=quad
  exact negative42_excluded rank rng rs az cl

def negativeLocus (x:ℚ) : Prop :=
  (¬∃i,concentrated x i) ∨
    (negativeParameter x ∧ allowance x<2*Real.log 35+2*Real.log x.den+4 ∧ largePoint false x)

theorem remove_positive (sel:PositiveSelmerSelection) (rank:ShortCurveBound) {x:ℚ}
    (inputs:largeLocus x) : negativeLocus x := by
  rcases inputs with nc|⟨pos,_⟩|neg
  · exact Or.inl nc
  · exact (no_positive_parameter sel rank x pos).elim
  · exact Or.inr neg

def NegativeExceptionalScalarBound : Prop :=
  ∀ (A:Fin 9→AffineInput) (x η:ℚ), ¬(∃k:ℤ,x=(k:ℚ)) →
    PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers → HardInput x → negativeLocus x →
    x∈exceptionalInputs (max x.num.natAbs x.den) → logHeight₁ (beta x)≤allowance x

theorem scalar_of_negative_exceptions (descent:TwoIsogenyRank) (reduction:OddGoodReduction)
    (sel:PositiveSelmerSelection) (rank:ShortCurveBound) (est:NegativeExceptionalScalarBound) : ScalarBound := by
  apply scalar_of_quotient_exceptions descent reduction
  intro A x η ni cert hard locus box
  exact est A x η ni cert hard (remove_positive sel rank locus) box

end
end Sun28.ConicRemaining
#print axioms Sun28.ConicRemaining.no_positive_parameter
#print axioms Sun28.ConicRemaining.remove_positive
#print axioms Sun28.ConicRemaining.scalar_of_negative_exceptions

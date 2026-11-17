import ScalarSeparation
import PublishedDeep

namespace Sun28.ScalarLucas
open Height Sun28.Ordinary Sun28.FixedPreparation Sun28.WitnessIndices Sun28.WitnessHeight
open ZInQ Sun28.Forward Sun28.ScalarHeight Sun28.FiveMarkUnits Sun28.MinimalConductors
open Sun28.HeightFibres Sun28.HeightFibres.Sharp
noncomputable section

/-- The logarithm of the reduced scalar denominator is enough in the integral Pell estimate. -/
def denominatorEstimate (x : ℚ) : ℝ :=
  let T : ℝ := (cutoffProduct:ℝ)*radical x
  2^175*T^2*(ell T)^7 + 2^165*T*(ell T)^4 *
    (Real.log (((beta x).den:ℕ):ℝ)+32)

theorem scalar_denominator_estimate (pell : PublishedPell312) (regulator : Regulator35)
    (disc : QuadraticCharacterDiscriminants) (x : ℚ) :
    logHeight₁ (beta x) ≤ denominatorEstimate x := by
  let b := beta x
  have support : oddProduct b.num b.den = radical x := by
    unfold oddProduct oddSupport radical
    rw [scalar_support_exact]
  have T : (heightRadical b.num b.den:ℝ)=(cutoffProduct:ℝ)*radical x := by
    rw [heightRadical,Nat.cast_mul,support]
  have h := centered_estimate pell regulator (conductor_from_characters disc) (beta_off_forms x) 0
  change pairLogHeight b.num b.den ≤
    2^175*(heightRadical b.num b.den:ℝ)^2*(ell (heightRadical b.num b.den))^7 +
    2^165*(heightRadical b.num b.den:ℝ)*(ell (heightRadical b.num b.den))^4*
    (Real.log (b.den:ℝ)+32) at h
  rw [T] at h
  rw [logHeight_reduced_pair]
  exact h

/-- The unsolved scalar height need only be supplied above both published numerical bounds. -/
def ScalarRemainder : Prop :=
  ∀ (A : Fin 9 → AffineInput) (x η : ℚ), ¬(∃ k : ℤ,x=(k:ℚ)) →
    PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers →
    scalarAllowance x < denominatorEstimate x →
    scalarAllowance x < vonKanelBound (best (beta x).num (beta x).den) →
    logHeight₁ (beta x) ≤ scalarAllowance x

theorem scalar_after_tests (units : PublishedCorollary72) (pell : PublishedPell312)
    (regulator : Regulator35) (disc : QuadraticCharacterDiscriminants)
    (rest : ScalarRemainder) (A : Fin 9 → AffineInput) (x η : ℚ) (nonint : ¬(∃ k : ℤ,x=(k:ℚ)))
    (accepted : PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers) : logHeight₁ (beta x) ≤ scalarAllowance x := by
  rcases le_or_gt (denominatorEstimate x) (scalarAllowance x) with yes|no
  · exact (scalar_denominator_estimate pell regulator disc x).trans yes
  rcases le_or_gt (vonKanelBound (best (beta x).num (beta x).den)) (scalarAllowance x) with yes|bad
  · rw [logHeight_reduced_pair]
    exact (attained_height units (beta_primitive x) (beta_off_forms x)).trans yes
  exact rest A x η nonint accepted no bad

end
end Sun28.ScalarLucas
#print axioms Sun28.ScalarLucas.scalar_denominator_estimate
#print axioms Sun28.ScalarLucas.scalar_after_tests

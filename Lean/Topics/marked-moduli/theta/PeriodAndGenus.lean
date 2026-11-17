import SexticThetaHeight
import FibreAndTrace
import TYZRepresentative

namespace ZInQBlueprint
open TYZ.Specialization

/-- The Hilbert fields, modular images, lifts and coefficients supply the recursive
genus point. Field and period assertions here concern only squarefree indices. -/
theorem frozen_of_sextic_periods_and_cm_traces
    (hp : SexticThetaHeight.HasSexticPeriods) (S : CMTraces)
    (L : ℕ → ℤ) (eps : ℕ → ℕ → GaussianUnit)
    (preserve : ∀ n, Squarefree n → n%8=5 ∨ n%8=6 →
      ∀ σ ∈ S.lifts n, ∀ x ∈ S.extended n, σ x ∈ S.extended n)
    (seven : ∀ n, Squarefree n → n%8=7 → S.trace n ∈ pointsOver (radicalField n))
    (ht : ∀ d (hd : d%8=5), Squarefree d → ZInQ.RouteK.Rank5b.T5bCl d = 1 →
      FieldInputs (S.recursion L eps) S.extended d hd) : ZInQ.FrozenTarget := by
  apply frozen_of_theta_fibres_and_odd_traces (SexticThetaHeight.thetaFibres_of_periods hp)
  intro d hd hs hOdd
  have hF : TraceFields (S.recursion L eps) S.extended :=
    ⟨fun n hsq hn => S.trace_mem n (preserve n hsq hn), seven⟩
  exact ⟨traceData_of_fieldInputs hF hs (ht d hd hs hOdd)⟩

end ZInQBlueprint
#print axioms ZInQBlueprint.frozen_of_sextic_periods_and_cm_traces

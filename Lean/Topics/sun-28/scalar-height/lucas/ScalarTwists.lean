import ScalarAssembly
import ScalarPrimeSupport
import PythagoreanInput

namespace Sun28.ScalarLucas
open ZInQ Height Sun28.Forward Sun28.Ordinary Sun28.FixedPreparation Sun28.WitnessIndices
open Sun28.WitnessHeight Sun28.ScalarHeight Sun28.FiveMarkUnits Sun28.IndexHeights
open Sun28.HeightFibres Sun28.HeightFibres.Sharp Sun28.MinimalConductors
noncomputable section

/-- A scalar point left after the squareclass exclusions and the numerical tests. -/
structure OpenScalarPoint (x : ℚ) (d : ℤ) (y : ℚ) : Prop where
  squarefree : Squarefree d
  live : y≠0
  curve : octic x=(d:ℚ)*y^2
  classes : d≠1 ∧ d≠ -1 ∧ d≠13
  inert : ¬ (Odd d ∧ d%3=1 ∧ ∀ p : ℕ, p.Prime → p∣d.natAbs →
    2<p ∧ ¬IsSquare (-1:ZMod p) ∧ ¬IsSquare (-6:ZMod p))
  splitting : ∀ p : ℕ, p.Prime → 2 < p → p∣d.natAbs →
    IsSquare (-6:ZMod p) ∨ IsSquare (-1:ZMod p) ∨ IsSquare (1199:ZMod p) ∨ IsSquare (-439:ZMod p)
  numerator : ∀ u c : ℤ, ¬ ScalarPencil.NumeratorTest x u c
  denominator : scalarAllowance x < denominatorEstimate x
  units : scalarAllowance x < vonKanelBound (best (beta x).num (beta x).den)
  conic : IsSquare (x^2+1) → ((ScalarPencil.totalRadical x:ℝ)^24) < numberLog x.num

/-- State the remaining arithmetic on a point of the octic in its signed squarefree twist. -/
def RemainingPointHeight : Prop :=
  ∀ (A : Fin 9 → AffineInput) (x η : ℚ), ¬(∃ k : ℤ,x=(k:ℚ)) →
    PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers →
    ∀ (d : ℤ) (y : ℚ), OpenScalarPoint x d y → logHeight₁ (beta x) ≤ scalarAllowance x

theorem scalar_of_remaining_points (bound : RemainingPointHeight) : RemainingScalar := by
  intro A x η ni cert num den units
  classical
  have nz : x≠0 := fun e => ni ⟨0,by simpa using e⟩
  by_cases h : IsSquare (x^2+1) ∧ numberLog x.num≤(ScalarPencil.totalRadical x:ℝ)^24
  · exact (ScalarPencil.pythagorean_sector nz h.1 h.2).trans (original_fits x)
  · obtain ⟨squarefree,y,live,curve⟩ := octic_twist x
    exact bound A x η ni cert (scalarClass x) y
      ⟨squarefree,live,curve,ScalarQuotients.excluded_classes x,
        fun h => ScalarQuotients.inert_twists_excluded squarefree h.1 h.2.1 h.2.2 live curve,
        fun _ pp odd pd => ScalarQuotients.splitting_at_prime squarefree live curve pp odd pd,
        num,den,units,fun square => lt_of_not_ge (fun small => h ⟨square,small⟩)⟩

theorem fixed_projection (realCurves : RealComponents.PublishedProposition72)
    (quadric : ConeCount.PublishedQuadricCount) (units : PublishedCorollary72)
    (allPell : HeightBudget.PublishedAllPell) (classes : HeightExtension.PublishedClassRegulator)
    (disc : QuadraticCharacterDiscriminants) (scalar : RemainingPointHeight) (ordinaryTests : RemainingOrdinary)
    (moments : PrimeValues.FirstMomentInputs) (points : GlobalDescent.DescentResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ, x=(z:ℚ) :=
  index_projection realCurves quadric units allPell classes disc (scalar_of_remaining_points scalar)
    ordinaryTests moments points x

end
end Sun28.ScalarLucas
#print axioms Sun28.ScalarLucas.scalar_of_remaining_points
#print axioms Sun28.ScalarLucas.fixed_projection

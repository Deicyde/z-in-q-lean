import PointwiseHeight
import NormSector
import PencilRowContact
import OrdinaryDivisors
import FiniteCharts

namespace Sun28.ScalarDepth
open ZInQ Height Sun28.Ordinary Sun28.Forward Sun28.WitnessIndices Sun28.FixedPreparation
open Sun28.WitnessHeight Sun28.ScalarLucas Sun28.ScalarHeight Sun28.FiveMarkUnits Sun28.IndexHeights
open Sun28.HeightFibres Sun28.HeightFibres.Sharp Sun28.MinimalConductors Sun28.PointPencils
open Sun28.RelativeContacts Sun28.FactorHeights
noncomputable section
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

def newCircleTest (x : ℚ) : Prop :=
  ∃ d w u v p c, Circle x d w u v p c ∧ Real.log (circleCap x d p c) ≤ allowance x

def newRowTest (x : ℚ) : Prop :=
  ∃ (i : Fin 4) (u v : ℤ), scalarRow i u v≠0 ∧ det u v x.num x.den≠0 ∧
    IsSquare (scalarRow i u v*scalarRow i x.num x.den) ∧
    2*Real.log (scaledCap i u v x)+4 ≤ allowance x

/-- Hypotheses left on the scalar certificate before its primes are assigned to the four rows. -/
structure HardInput (x : ℚ) : Prop where
  norm : ¬ Squarefree (x.num.natAbs^2+x.den^2)
  circle : ¬ newCircleTest x
  row : ¬ newRowTest x
  denominator : allowance x < denominatorEstimate x
  units : allowance x < vonKanelBound (best (beta x).num (beta x).den)
  oldPoint : ∃ d y, OpenScalarPoint x d y

/-- If the large prime support is concentrated in one row, the unresolved inputs lie on four explicit loci. -/
def specialLocus (x : ℚ) : Prop :=
  elliptic 4 6 (4*x^2) ∨ elliptic 64 439 (64*x^2) ∨
    ∃ Y : ℚ, Y≠0 ∧ (sextic x=2*Y^2 ∨ sextic x=(-70)*Y^2)

def ScalarBound : Prop :=
  ∀ (A : Fin 9 → AffineInput) (x η : ℚ), ¬(∃ k : ℤ, x=(k:ℚ)) →
    PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers → HardInput x →
    ((¬∃ i, concentrated x i) ∨ specialLocus x) →
    logHeight₁ (beta x) ≤ allowance x

theorem scalar_after_arithmetic (units : PublishedCorollary72)
    (allPell : HeightBudget.PublishedAllPell) (classes : HeightExtension.PublishedClassRegulator)
    (disc : QuadraticCharacterDiscriminants) (residual : ScalarBound) (A : Fin 9 → AffineInput) (x η : ℚ)
    (nonint : ¬∃ k : ℤ,x=(k:ℚ))
    (cert : PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator smallMultipliers smallMultipliers) :
    logHeight₁ (beta x) ≤ allowance x := by
  classical
  by_contra! fail
  have oldFail : scalarAllowance x < logHeight₁ (beta x) := lt_of_le_of_lt (previous_allowance x) fail
  have den := scalar_denominator_estimate (HeightBudget.integral_of_all allPell)
    (HeightExtension.ordinary_regulator classes) disc x
  have unit := attained_height units (beta_primitive x) (beta_off_forms x)
  rw [←logHeight_reduced_pair] at unit
  have noNorm := fun H => (not_le_of_gt oldFail) (squarefree_norm x H)
  have noCircle : ¬newCircleTest x := by
    rintro ⟨d,w,u,v,p,c,h,sm⟩
    exact (not_le_of_gt fail) ((centre_height x h).trans sm)
  have noRow : ¬newRowTest x := by
    rintro ⟨i,u,v,nz,away,square,sm⟩
    exact (not_le_of_gt fail) ((height_from_row x i nz away square).trans sm)
  have nonzero : x≠0 := fun eq => nonint ⟨0,by simpa using eq⟩
  obtain ⟨sf,y,live,curve⟩ := octic_twist x
  have existsPoint : ∃ d y, OpenScalarPoint x d y := by
    refine ⟨scalarClass x,y,sf,live,curve,ScalarQuotients.excluded_classes x,
      fun h => ScalarQuotients.inert_twists_excluded sf h.1 h.2.1 h.2.2 live curve,
      fun _ pp odd pd => ScalarQuotients.splitting_at_prime sf live curve pp odd pd,?_,
      lt_of_lt_of_le oldFail den,lt_of_lt_of_le oldFail unit,?_⟩
    · intro u c test
      exact (not_le_of_gt oldFail) ((ScalarPencil.of_numerator_split allPell classes disc nonzero test).trans (original_fits x))
    · intro square
      by_contra! small
      exact (not_le_of_gt oldFail) ((ScalarPencil.pythagorean_sector nonzero square small).trans (original_fits x))
  have locus : (¬∃ i, concentrated x i) ∨ specialLocus x := by
    by_cases h : ∃ i, concentrated x i
    · right
      rcases concentrated_alternatives nonzero h with e|e|c
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (two_sextics c))
    · exact Or.inl h
  exact (not_le_of_gt fail) (residual A x η nonint cert
    ⟨noNorm,noCircle,noRow,lt_of_lt_of_le fail den,lt_of_lt_of_le fail unit,existsPoint⟩ locus)

def ordinaryTest (A : Fin 9 → AffineInput) (η : ℚ) : Prop :=
  let s := pointScale (nineAffine A).doubles fixedMultiplier
  Matched (s 1) η ∧ Matched (s 2) η ∧ denominatorBudget s η≤
    ordinary*(unionRadical oldCutoff (slope (nineAffine A).doubles η):ℝ)^24

def OrdinaryBound : Prop :=
  ∀ (A : Fin 9 → AffineInput) (x η : ℚ), ¬(∃ k : ℤ, x=(k:ℚ)) →
    PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers → ¬ordinaryTest A η → OrdinaryIndices A η

theorem fixed_projection (realCurves : RealComponents.PublishedProposition72)
    (quadric : ConeCount.PublishedQuadricCount) (units : PublishedCorollary72)
    (allPell : HeightBudget.PublishedAllPell) (classes : HeightExtension.PublishedClassRegulator)
    (disc : QuadraticCharacterDiscriminants) (scalar : ScalarBound) (ord : OrdinaryBound)
    (moments : PrimeValues.FirstMomentInputs) (points : GlobalDescent.DescentResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ, x=(z:ℚ) := by
  constructor
  · rintro h
    classical
    by_contra nonint
    obtain ⟨A,η,cert⟩ := (Concrete.polynomial_iff_certificate _).1 h
    apply nonint
    apply integral A x η cert _ (scalar_after_arithmetic units allPell classes disc scalar A x η nonint cert)
    by_cases check : ordinaryTest A η
    · exact indices_of_matches A x η cert check.1 check.2.1 check.2.2
    · exact ord A x η nonint cert check
  · rintro ⟨k,rfl⟩
    exact fibre_of_integer realCurves quadric moments (GlobalDescent.sections_iff_descent.mpr points) k

end
end Sun28.ScalarDepth
#print axioms Sun28.ScalarDepth.scalar_after_arithmetic
#print axioms Sun28.ScalarDepth.fixed_projection

import RowApplication
import Extension
import SurfaceProjection

namespace Sun28.MediumSieve
open Sun28.SinglePrime Sun28.ContactSieve Sun28.Ordinary Sun28.HeightFibres Sun28.HeightFibres.Sharp
open Sun28.HeightExtension
noncomputable section

/-- An alternative verification path via a single uniform unweighted upper bound per medium prime. -/
structure PrimeBounds (A : Fin 3→ℚ) (d : ℕ) (H Y : ℝ) (T : Finset ℕ) (κ : ℕ) : Prop where
  estimates : ∃ (K : ℕ) (σ C : ℝ),2810≤K ∧ exceptionalBound A d≤K ∧
    (∀ p∈T,p≤K) ∧ (∀ p∈κ.primeFactors,p≤K) ∧ 0<σ ∧ 0≤C ∧
    ∀ L : ℕ,K≤L → CountThreshold A d H Y T κ K L σ ∧ ∃ J,PrimeRow A d H Y T κ L J C

def PrimeInputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4→ℤ),AdmissibleRoots X c q n →
    ∀ (d κ : ℕ) (T : Finset ℕ),0<d → 0<κ → (∀ p∈T,p.Prime) → 2∈T →
      ∀ H Y : ℝ,PrimeBounds (Sun28.RealPoleBounds.fixedScale n) d H Y T κ

theorem log_of_prime (input : PrimeInputs) : LogInputs := by
  intro X c q n roots d κ T dp kp primes two H Y
  obtain ⟨K,σ,C,big,gaps,inT,inAux,pos,non,all⟩:=(input X c q n roots d κ T dp kp primes two H Y).estimates
  refine ⟨K,σ,C,big,gaps,inT,inAux,pos,non,?_⟩
  intro L kl
  obtain ⟨finite,J,rows⟩:=all L kl
  exact ⟨finite,J,one_prime_transfer (by omega) non rows⟩

/-- The fixed 28-witness polynomial with the three residual arithmetic assertions. -/
theorem reduced_projection (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (integral : PublishedPell312)
    (finitePell : PublishedFinitePell) (classes : PublishedClassRegulator)
    (characters : QuadraticCharacterDiscriminants) (height : LargeAndDense)
    (counts : LogInputs) (points : TwistExtension.Residual) (x : ℚ) :
    (∃ w : Fin 28→ℚ,eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ,x=(z:ℚ) := by
  have original := (original_iff_large_and_dense units integral finitePell classes characters).mpr height
  exact TwistExtension.fixed_projection realCurves units (FiveDescent.glazer_iff_twist.mp original)
    (log_positive_surplus counts) points x

theorem reduced_integer_definition (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (integral : PublishedPell312)
    (finitePell : PublishedFinitePell) (classes : PublishedClassRegulator)
    (characters : QuadraticCharacterDiscriminants) (height : LargeAndDense)
    (counts : LogInputs) (points : TwistExtension.Residual) : IntegerDefinition28 :=
  ⟨Concrete.fixedPolynomial,reduced_projection realCurves units integral finitePell classes characters height counts points⟩
end
end Sun28.MediumSieve
#print axioms Sun28.MediumSieve.log_of_prime
#print axioms Sun28.MediumSieve.reduced_projection
#print axioms Sun28.MediumSieve.reduced_integer_definition

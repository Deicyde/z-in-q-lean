import CutoffTransfer
import SieveProjection

namespace Sun28.SinglePrime
open Finset Filter Topology Sun28.WeightedSelection Sun28.ContactSieve Sun28.NormSieve
noncomputable section

/-- The base cutoff includes all the exceptional primes. The constant and base set
are fixed before the final cutoff. At each cutoff the main and tail use the same boxes. -/
structure SinglePrimeBounds (A : Fin 3→ℚ) (d : ℕ) (H Y : ℝ) (T : Finset ℕ) (κ : ℕ) : Prop where
  estimates : ∃ (K : ℕ) (σ C : ℝ),2810≤K ∧ (∀ p∈T,p≤K) ∧ (∀ p∈κ.primeFactors,p≤K) ∧
    0<σ ∧ 0≤C ∧ ∀ L : ℕ,K≤L → ∃ boxes : CountingBoxes A d H Y,
      CountsAt A d H Y T κ K L boxes σ ∧
      ∀ ε : ℝ,0<ε → ∀ᶠ b in atTop,
        removedMass T κ L (boxes.records b) ≤(C/(L:ℝ)+ε)*area boxes b

theorem counting_bounds {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ} {T : Finset ℕ} {κ : ℕ}
    (inputs : SinglePrimeBounds A d H Y T κ) : CountingBounds A d H Y T κ := by
  obtain ⟨K,σ,C,big,inT,inAux,pos,non,all⟩:=inputs.estimates
  refine ⟨σ/4,C,by positivity,non,K,?_⟩
  intro L kl _
  obtain ⟨boxes,counts,tail⟩:=all L kl
  refine ⟨boxes,?_⟩
  intro ε ep
  exact eventually_atTop.mp ((main_eventually counts pos big kl inT inAux).and (tail ε ep))

def SinglePrimeInputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4→ℤ),AdmissibleRoots X c q n →
    ∀ (d κ : ℕ) (T : Finset ℕ),0<d → 0<κ → (∀ p∈T,p.Prime) → 2∈T →
      ∀ H Y : ℝ,SinglePrimeBounds (Sun28.RealPoleBounds.fixedScale n) d H Y T κ

theorem analytic_counts (h : SinglePrimeInputs) : AnalyticCounts :=
  fun X c q n roots d κ T dp kp primes two H Y =>
    counting_bounds (h X c q n roots d κ T dp kp primes two H Y)

theorem prime_values (h : SinglePrimeInputs) : PrimeValuesWithResidues :=
  prime_values_of_counts (analytic_counts h)

theorem fixed_projection (geometry : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72)
    (height : FiveDescent.TwistHeight Sun28.Ordinary.glazerConstant24)
    (counts : SinglePrimeInputs) (twists : PairedClasses.Residual) (x : ℚ) :
    (∃ w : Fin 28→ℚ,eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ,x=(z:ℚ) :=
  SieveProjection.fixed_projection geometry units height
    (prime_values_iff_surplus.mp (prime_values counts)) twists x

end
end Sun28.SinglePrime
#print axioms Sun28.SinglePrime.counting_bounds
#print axioms Sun28.SinglePrime.analytic_counts
#print axioms Sun28.SinglePrime.prime_values
#print axioms Sun28.SinglePrime.fixed_projection

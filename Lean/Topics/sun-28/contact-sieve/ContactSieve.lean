import GaussianSelection

namespace Sun28.ContactSieve
open ZInQ Sun28.Ordinary Sun28.FixedPreparation Sun28.Forward Sun28.RealPoleBounds
open Sun28.ContactFactors ManuscriptV15.Arithmetic

/-- Precisely the root data passed into the finite-place preparation. -/
structure AdmissibleRoots (X c q : ℤ) (n : Fin 4→ℤ) : Prop where
  positive : 0<c
  multiple : c=(fixedMultiplier:ℤ)*q
  beta : n 0=2*X^2+3
  shift : n 1=c+1
  odd : ∀ i,0<n i ∧ Odd (n i)
  lucas_eq : lucas (n 1) (n 2) (n 3)=0

/-- The orientation used in the point-count theorem. -/
structure NormRays (A : Fin 3→ℚ) {u v : ℕ} (h : PrimeValues A u v)
    (π : ↥(shifts A)→Gaussian) : Prop where
  norm : ∀ r,gaussianNorm (π r)=h.value r
  ray16 : ∀ r,gaussianCongruent 16 (π r) (9,0)
  ray7 : ∀ r,gaussianCongruent 7 (π r) (1,3)

/-- Mixed collisions include the diagonal. The first and second shifts can coincide. -/
def MixedAndLocal {ι : Type*} (π : ι→Gaussian) (T : Finset ℕ) (κ : ℕ) : Prop :=
  (∀ r s,∀ l : ℕ,l.Prime → l≠2 → l≠7 →
    ¬(l∣adjacentNorm (π r) true ∧ l∣adjacentNorm (π s) false)) ∧
  (∀ l∈T,l≠2 → l≠7 → ∀ r e,¬l∣adjacentNorm (π r) e) ∧
  (∀ l∈κ.primeFactors,l∉T → l≠2 → l≠7 → ∀ r,¬l∣adjacentNorm (π r) false)

/-- Prime input for exactly the shifts of the four integer roots in Sun's construction. -/
def PrimePatterns : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4→ℤ), AdmissibleRoots X c q n →
    ∀ (d κ : ℕ) (T : Finset ℕ), 0<d → 0<κ → (∀ l∈T,l.Prime) → 2∈T →
    ∀ H Y : ℝ, let A:=fixedScale n
      ∃ (u v : ℕ) (h : PrimeValues A u v) (π : ↥(shifts A)→Gaussian),
        0<v ∧ d∣v ∧ H<(Sun28.ContactFactors.slope A u v:ℝ) ∧ (∀ r∈shifts A,Y<(h.value r:ℝ)) ∧
        NormRays A h π ∧ MixedAndLocal π T κ

/-- Prime norm and the two orientation rays do not exclude a mixed self collision. -/
theorem diagonal_counterexample :
    let z : Gaussian:=(-55,-32)
    gaussianNorm z=4049 ∧ Nat.Prime 4049 ∧ gaussianCongruent 16 z (9,0) ∧
    gaussianCongruent 7 z (1,3) ∧ adjacentNorm z true=3940 ∧ adjacentNorm z false=4160 ∧
    (adjacentNorm z true).gcd (adjacentNorm z false)=20 := by
  refine ⟨by decide,by norm_num,by unfold gaussianCongruent; decide,by unfold gaussianCongruent; decide,by decide,by decide,by decide⟩

end Sun28.ContactSieve
#print axioms Sun28.ContactSieve.diagonal_counterexample

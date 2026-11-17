import DiscriminantHeight

/-! The finite part of the genus-two discriminant on the rational six-contact family. -/
namespace ZInQBlueprint.JacobianHeight
open ZInQ SixContactHP
noncomputable section

/-- The representatives of Baba–Granath, Proposition 3.6, with Liu's convention for J₈. -/
def j6 (j : ℚ) := 4*(j^3-2*j^2+1)
def j8 (j : ℚ) := (12*(j+1)*j6 j - (6*(j^2+j+1))^2)/4

private def iota (p : ℕ) : ℕ := if p=2 then 4 else if p=3 then 3 else 1

/-- Reciprocal of the absolute invariant inside the local logarithm of HP Theorem 4.5.
If a numerator J₆ or J₈ in that theorem vanishes, its logarithmic contribution is zero.
Lean's value of the valuation at zero implements this case here. -/
def inverseLocalInvariant (u : ℚ) (p : ℕ) : ℚ :=
  let j := SixContact.J u
  if p=2 then (j^3)^4 / (j8 j)^5 else if p=3 then (j^3)^3 / (j6 j)^5 else igusaPole j

def finiteTerm (K : Type) [Field K] [NumberField K] (u : ℚ) (p : ℕ) : ℝ :=
  degreeSum K p (((max (0 : ℤ) (padicValRat p (inverseLocalInvariant u p)) : ℝ) /
    (iota p : ℝ)) * Real.log p)

/-- A computable superset of the support, using rational primes only. -/
def finiteSupport (u : ℚ) : Finset ℕ :=
  {2,3} ∪ (SixContact.J u).den.primeFactors ∪ (igusaPole (SixContact.J u)).num.natAbs.primeFactors

theorem poles_subset (u : ℚ) : (SixContact.J u).den.primeFactors ⊆ finiteSupport u :=
  fun _ hp => Finset.mem_union_left _ (Finset.mem_union_right _ hp)

theorem finiteTerm_nonneg (K : Type) [Field K] [NumberField K] (u : ℚ) (p : ℕ) :
    0 ≤ finiteTerm K u p := by
  by_cases hp : p.Prime
  · rw [finiteTerm, degreeSum_eq K hp]
    have hl : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
    positivity
  · simp [finiteTerm, degreeSum, hp]

theorem finiteTerm_off_support (K : Type) [Field K] [NumberField K] (u : ℚ) {p : ℕ}
    (hp : p ∉ finiteSupport u) : finiteTerm K u p = 0 := by
  by_cases prime : p.Prime
  · have h2 : p ≠ 2 := by rintro rfl; exact hp (by simp [finiteSupport])
    have h3 : p ≠ 3 := by rintro rfl; exact hp (by simp [finiteSupport])
    let q := igusaPole (SixContact.J u)
    have hout : p ∉ q.num.natAbs.primeFactors := fun h => hp (Finset.mem_union_right _ h)
    suffices v : padicValRat p q ≤ 0 by
      have hi : inverseLocalInvariant u p = q := by simp [inverseLocalInvariant, h2, h3, q]
      have vr : (padicValRat p q : ℝ) ≤ 0 := by exact_mod_cast v
      rw [finiteTerm, degreeSum_eq K prime, hi]
      norm_num only [Int.cast_zero]
      rw [max_eq_left vr]
      simp
    by_cases zero : q=0
    · simp [zero]
    have nz := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr zero)
    have nd : ¬ p ∣ q.num.natAbs := fun hd => hout (Nat.mem_primeFactors.mpr ⟨prime,hd,nz⟩)
    rw [padicValRat_def, padicValInt, padicValNat.eq_zero_of_not_dvd nd]
    simp
  · simp [finiteTerm, degreeSum, prime]

theorem finiteTerm_at_pole (K : Type) [Field K] [NumberField K] {u : ℚ} (hu : u ∉ contactSet)
    {p : ℕ} (hp : p ∈ (SixContact.J u).den.primeFactors) :
    finiteTerm K u p = paperPoleTerm K u p := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ (by decide : (0 : ℚ) ∈ contactSet))
  have h := prime_den_large u hu0 hp
  simp [finiteTerm, inverseLocalInvariant, iota, show p ≠ 2 by omega, show p ≠ 3 by omega,
    paperPoleTerm, (paper_igusa_quotient hu).2, igusaPole]

/-- The finite terms are now fixed by the rational parameter at every prime. The remaining
applications identify both heights on the same Jacobian, with reduced periods at all embeddings. -/
structure PaperFibreHeights (K : Type) [Field K] [NumberField K] (u : ℚ) where
  stable : ℝ
  period : (K →ₐ[ℚ] ℂ) → ThetaPeriod.SiegelPeriod
  reduced : ∀ σ, InStrengDomain (period σ)
  evenNonzero : ∀ σ i, ThetaPeriod.thetaNull (period σ) (ThetaQuotient.evenIndices i) ≠ 0
  heightFormula : (Module.finrank ℚ K : ℝ) * (stable + Real.log Real.pi) =
    (∑ p ∈ finiteSupport u, finiteTerm K u p)/60 - (∑ σ, Real.log (peterssonFactor (period σ)))/10
  stableBound : stable ≤ HeightBudget.vonKaenelBudget u

def PaperFibreHeights.comparison {K : Type} [Field K] [NumberField K] {u : ℚ}
    (d : PaperFibreHeights K u) (hu : u ∉ contactSet) : DiscriminantComparison K u where
  hF := d.stable
  support := finiteSupport u
  term := finiteTerm K u
  period := d.period
  contains := poles_subset u
  nonnegative := fun p _ => finiteTerm_nonneg K u p
  poles := fun _ hp => (finiteTerm_at_pole K hu hp).ge
  reduced := d.reduced
  evenNonzero := d.evenNonzero
  formula := d.heightFormula
  stableBound := d.stableBound

/-- Conditional bounded theorem with the exact discriminant sum, including its two
exceptional residue characteristics. -/
theorem original_of_paper_fibre_heights (streng : StrengEstimates)
    (fibres : ∀ u : ℚ, u ∉ contactSet → ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Nonempty (PaperFibreHeights K u))
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget := by
  apply original_of_discriminant_comparison streng _ genus rank
  intro u hu
  obtain ⟨K,_,_,⟨d⟩⟩ := fibres u hu
  exact ⟨K, inferInstance, inferInstance, ⟨d.comparison hu⟩⟩

end
end ZInQBlueprint.JacobianHeight
#print axioms ZInQBlueprint.JacobianHeight.poles_subset
#print axioms ZInQBlueprint.JacobianHeight.finiteTerm_nonneg
#print axioms ZInQBlueprint.JacobianHeight.finiteTerm_off_support
#print axioms ZInQBlueprint.JacobianHeight.finiteTerm_at_pole
#print axioms ZInQBlueprint.JacobianHeight.PaperFibreHeights.comparison
#print axioms ZInQBlueprint.JacobianHeight.original_of_paper_fibre_heights

import HPIgusaPoles
import HPArchScalar

/-! At a rational pole, restriction of normalized absolute values makes the
logarithm constant over the entire fibre. The local degrees then sum to the
field degree without any Galois or splitting assumption. -/
namespace SixContactHP
open NumberField Finset ZInQ
noncomputable section
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

private def intPrime (p : ℕ) : Ideal ℤ := Ideal.span {(p:ℤ)}

private theorem intPrime_prime {p : ℕ} (hp : p.Prime) : (intPrime p).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero : (p:ℤ) ≠ 0)).mpr
    (Nat.prime_iff_prime_int.mp hp)

private theorem intPrime_maximal {p : ℕ} (hp : p.Prime) : (intPrime p).IsMaximal :=
  (intPrime_prime hp).isMaximal (by simpa [intPrime] using (show (p:ℤ) ≠ 0 by exact_mod_cast hp.ne_zero))

/-- Sum of the local degrees times a rational local logarithm at all ideals over p. -/
def degreeSum (p : ℕ) (b : ℝ) : ℝ :=
  if hp : p.Prime then
    let _ : (intPrime p).IsMaximal := intPrime_maximal hp
    ∑ w : (intPrime p).primesOver (𝓞 K),
      ((w.1.ramificationIdx ℤ * w.1.inertiaDeg ℤ : ℕ) : ℝ) * b
  else 0

theorem degreeSum_eq {p : ℕ} (hp : p.Prime) (b : ℝ) :
    degreeSum K p b = (Module.finrank ℚ K : ℝ)*b := by
  let _ : (intPrime p).IsMaximal := intPrime_maximal hp
  unfold degreeSum
  rw [dite_eq_left hp, ← Finset.sum_mul]
  congr 1
  exact_mod_cast (Ideal.sum_ramification_inertia_eq_finrank (intPrime p) (𝓞 K)).trans
    (RingOfIntegers.rank K)

/-- Contribution above the exact rational pole primes of a single input. -/
def poleSum (j : ℚ) : ℝ := ∑ p ∈ j.den.primeFactors,
  degreeSum K p ((max (0:ℤ) (padicValRat p (igusaPole j)):ℝ)*Real.log p)

theorem poleSum_eq (u : ℚ) (hu : u ≠ 0) :
    poleSum K (JHeight.Jmap u) = (Module.finrank ℚ K : ℝ)*(2*ratHeight (JHeight.Jmap u)) := by
  rw [←retained_eq u hu]
  unfold poleSum retained
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ hp => degreeSum_eq K (Nat.prime_of_mem_primeFactors hp) _)

/-- The nonpole summands in the stable-discriminant formula are nonnegative. -/
theorem finite_log_lower (u : ℚ) (hu : u ≠ 0) {discriminant : ℝ} {S : Finset ℕ}
    (terms : ℕ → ℝ) (contains : (JHeight.Jmap u).den.primeFactors ⊆ S)
    (nonnegative : ∀ p ∈ S, 0 ≤ terms p)
    (at_poles : ∀ p ∈ (JHeight.Jmap u).den.primeFactors,
      degreeSum K p ((max (0:ℤ) (padicValRat p (igusaPole (JHeight.Jmap u))):ℝ)*Real.log p)
        ≤ terms p)
    (discriminant_eq : ∑ p ∈ S, terms p = discriminant) :
    (Module.finrank ℚ K : ℝ)*(2*ratHeight (JHeight.Jmap u)) ≤ discriminant := by
  rw [← poleSum_eq K u hu, ←discriminant_eq]
  exact (Finset.sum_le_sum at_poles).trans
    (Finset.sum_le_sum_of_subset_of_nonneg contains (fun p hp _ => nonnegative p hp))

/-- The sum counts all field embeddings, hence both members of each complex pair. -/
theorem arch_log_upper (term : (K →ₐ[ℚ] ℂ) → ℝ)
    (positive : ∀ σ, 0 < term σ) (bound : ∀ σ, term σ ≤ archConstant) :
    ∑ σ, Real.log (term σ) ≤ (Module.finrank ℚ K : ℝ)*Real.log archConstant := by
  calc
    _ ≤ ∑ _σ : K →ₐ[ℚ] ℂ, Real.log archConstant := Finset.sum_le_sum
       (fun σ _ => Real.log_le_log (positive σ) (bound σ))
    _ = _ := by simp [AlgHom.card ℚ K ℂ]

/-- Arithmetic consequence of the finite and infinite parts in the published
formula, with the HP metric. -/
theorem j_height_of_place_formula (u : ℚ) {discriminant archimedean hHP : ℝ}
    (finite_lower : (Module.finrank ℚ K : ℝ)*(2*ratHeight (JHeight.Jmap u)) ≤ discriminant)
    (arch_upper : archimedean ≤ (Module.finrank ℚ K : ℝ)*Real.log archConstant)
    (formula : (Module.finrank ℚ K : ℝ)*hHP = discriminant/60-archimedean/10) :
    ratHeight (JHeight.Jmap u) ≤ 30*hHP+3*Real.log archConstant := by
  have pos : 0 < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos (R:=ℚ) (M:=K)
  apply (mul_le_mul_iff_right₀ pos).mp
  nlinarith

end
end SixContactHP

#print axioms SixContactHP.degreeSum_eq
#print axioms SixContactHP.poleSum_eq
#print axioms SixContactHP.finite_log_lower
#print axioms SixContactHP.arch_log_upper
#print axioms SixContactHP.j_height_of_place_formula


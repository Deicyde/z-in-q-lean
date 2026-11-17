import LowerInertiaTable
import QuaternionResidue
import Mathlib.Data.Nat.Factorization.Basic

namespace ZInQBlueprint.WildLevel
noncomputable section

/-- Prime-to-p realizations of the same primitive modular level. At a prime
outside the specified support the representation is unramified. At a prime
in the support its Artin exponent is read from the actual wild action. -/
structure ConductorRealizations (N R : ℕ) where
  positive : 0<N
  supported : ∀ p, p.Prime → ¬p∣R → N.factorization p=0
  at_prime : ∀ p, p.Prime → p∣R → ∃ F : WildFibre p,
    LowerInertia p (Nat.card F.image) (N.factorization p)

theorem local_exponents {N R : ℕ} (D : ConductorRealizations N R) {p : ℕ} (hp:p.Prime) :
    N.factorization p ≤ if p=2 then 12 else 2 := by
  by_cases support:p∣R
  · obtain ⟨F,data⟩:=D.at_prime p hp support
    have order:=wild_orders hp F
    by_cases h:p=2
    · subst p
      exact dyadic_conductor (by simpa using order) data
    · simp only [h,ite_false] at order ⊢
      rw [order] at data
      exact tame_conductor hp.two_le data
  · rw [D.supported p hp support];exact Nat.zero_le _

/-- One factor R² pays for two tame dimensions at every prime, including 2. -/
theorem primitive_level_dvd {N R : ℕ} (rp:0<R) (D : ConductorRealizations N R) :
    N ∣ 2^10*R^2 := by
  apply (Nat.factorization_prime_le_iff_dvd D.positive.ne' (by positivity)).mp
  intro p hp
  by_cases divides:p∣R
  · have cost := local_exponents D hp
    have contributes := (hp.dvd_iff_one_le_factorization rp.ne').mp divides
    rw [Nat.factorization_mul (by decide : 2^10≠0) (pow_ne_zero _ rp.ne'),Nat.factorization_pow,Nat.factorization_pow]
    by_cases h:p=2
    · subst p
      simp only [ite_true] at cost
      simp [Nat.prime_two.factorization_self]
      omega
    · simp only [h,ite_false] at cost
      simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]
      omega
  · exact (D.supported p hp divides).le.trans (Nat.zero_le _)

end
end ZInQBlueprint.WildLevel
#print axioms ZInQBlueprint.WildLevel.local_exponents
#print axioms ZInQBlueprint.WildLevel.primitive_level_dvd

import SourceTwists
import ZInQKernel.Multiplication.Completeness.SquareDen

/-! The ordinary pole has square reduced denominator even when cancellation occurs away
from every selected prime. -/
namespace Sun28.FinitePole
open Sun28.PreparedPoles Sun28.FixedPreparation
open scoped BigOperators

theorem valuation_prime_product {p : ℕ} [hp : Fact p.Prime] (S : Finset ℕ)
    (prime : ∀ q∈S, Nat.Prime q) :
    padicValRat p (∏ q∈S,(q:ℚ)) = if p∈S then 1 else 0 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert q S fresh ih =>
    have pp := prime q (Finset.mem_insert_self q S)
    have prefs (s : ℕ) (hs : s∈S) := prime s (Finset.mem_insert_of_mem hs)
    have live : (∏ s∈S,(s:ℚ))≠0 := Finset.prod_ne_zero_iff.mpr
      (fun s hs => by exact_mod_cast (prefs s hs).ne_zero)
    rw [Finset.prod_insert fresh,padicValRat.mul (by exact_mod_cast pp.ne_zero) live,ih prefs]
    by_cases e : p=q
    · subst q
      simp [padicValRat.self hp.out.one_lt,fresh]
    · have nd : ¬p∣q := fun h => e ((Nat.prime_dvd_prime_iff_eq hp.out pp).1 h)
      rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd nd]
      simp [e]

theorem ordinary_order (S : Finset ℕ) (prime : ∀ p∈S, Nat.Prime p) {q T R : ℚ}
    (q0 : q≠0) (T0 : T≠0) (fac : R=q^2*(∏ p∈S,(p:ℚ))) (p : ℕ) [Fact p.Prime] :
    padicValRat p (R/T^2)=2*(padicValRat p q-padicValRat p T)+(if p∈S then 1 else 0) := by
  have live : (∏ s∈S,(s:ℚ))≠0 := Finset.prod_ne_zero_iff.mpr
    (fun s hs => by exact_mod_cast (prime s hs).ne_zero)
  rw [fac,padicValRat.div (mul_ne_zero (pow_ne_zero _ q0) live) (pow_ne_zero _ T0),
    padicValRat.mul (pow_ne_zero _ q0) live,padicValRat.pow,padicValRat.pow,valuation_prime_product S prime]
  push_cast
  ring

/-- At primes of the support the necessary comparison is v(T)≤v(q).
At every other prime both signs of v(q)−v(T) are allowed. -/
theorem ordinary_square_den (S : Finset ℕ) (prime : ∀ p∈S, Nat.Prime p) {q T R : ℚ}
    (q0 : q≠0) (T0 : T≠0) (fac : R=q^2*(∏ p∈S,(p:ℚ)))
    (localOrder : ∀ p∈S, padicValRat p T≤padicValRat p q) : IsSquare (R/T^2).den := by
  apply ZInQ.Mult.isSquare_den_of_even
  intro p pp h
  let _ := Fact.mk pp
  have eqn := ordinary_order S prime q0 T0 fac p
  by_cases m : p∈S
  · rw [ite_eq_left m] at eqn
    have d := localOrder p m
    omega
  · rw [ite_eq_right m] at eqn
    exact ⟨padicValRat p q-padicValRat p T,by omega⟩

theorem ordinary_prepared (S : Finset ℕ) (prime : ∀ p∈S, Nat.Prime p) {q T R : ℚ}
    (q0 : q≠0) (T0 : T≠0) (fac : R=q^2*(∏ p∈S,(p:ℚ)))
    (units : ∀ p∈S, padicValRat p q=0 ∧ padicValRat p T=0)
    (interval : 0<R/T^2 ∧ R/T^2<1/2)
    (deep : ∀ p∈primes, 4≤padicValRat p (R/T^2)) : Prepared (R/T^2) :=
  ⟨ordinary_square_den S prime q0 T0 fac (fun p hp => le_of_eq ((units p hp).2.trans (units p hp).1.symm)),
    interval.1,interval.2,deep⟩

#print axioms valuation_prime_product
#print axioms ordinary_order
#print axioms ordinary_square_den
#print axioms ordinary_prepared
end Sun28.FinitePole

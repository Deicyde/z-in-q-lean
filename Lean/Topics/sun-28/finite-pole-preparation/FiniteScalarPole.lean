import FinitePoleValuations

/-! Sun's scalar pole at the fixed preparation constants, including support/denominator
cancellation and the valuation at every exceptional prime. -/
namespace Sun28.FinitePole
open Sun28.PreparedPoles Sun28.FixedPreparation Sun28.ScalarHeight

private theorem front_unit {p D a : ℕ} [Fact p.Prime] (hit : p∣D ∨ p∣a) :
    padicValRat p (1+(D:ℚ)*(a:ℚ)^2)=0 := by
  have dvd : p∣D*a^2 := hit.elim (fun h => dvd_mul_of_dvd_left h _) (fun h =>
    dvd_mul_of_dvd_right (dvd_pow h two_ne_zero) _)
  have prime := Fact.out (p:=p.Prime)
  have nd : ¬p∣1+D*a^2 := fun h => prime.not_dvd_one ((Nat.dvd_add_left dvd).mp h)
  have cast : (1:ℚ)+D*(a:ℚ)^2=((1+D*a^2:ℕ):ℚ) := by push_cast;ring
  rw [cast,padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd nd]
  rfl

/-- Exact signed scalar order. Opposite signs of W or nonzero scales make no difference. -/
theorem scalar_order (p : ℕ) [Fact p.Prime] {a D : ℕ} {r δ Γ W : ℚ}
    (rad : δ*r=(a:ℚ)) (apos : 0<a) (gn : Γ≠0) (wn : W≠0) :
    padicValRat p (signedValue r δ Γ D W)=padicValRat p (a:ℚ)+
      2*(padicValRat p Γ+padicValRat p W-padicValRat p (1+(D:ℚ)*(a:ℚ)^2)) := by
  have nz : (1:ℚ)+D*(a:ℚ)^2≠0 := by positivity
  have an : (a:ℚ)≠0 := by exact_mod_cast apos.ne'
  rw [signedValue,rad,padicValRat.mul (pow_ne_zero 2 (mul_ne_zero (div_ne_zero gn nz) wn)) an,
    padicValRat.pow,padicValRat.mul (div_ne_zero gn nz) wn,padicValRat.div gn nz]
  push_cast
  ring

/-- At odd-valuation prime divisors of a we need just nonnegative total order.
At all other primes the valuation may be negative and is then automatically even. -/
theorem scalar_square_den {a D : ℕ} {r δ Γ W : ℚ} (rad : δ*r=(a:ℚ))
    (apos : 0<a) (gn : Γ≠0) (wn : W≠0)
    (localOrder : ∀ p : ℕ, p.Prime → p∣a → Odd (padicValRat p (a:ℚ)) →
      0≤padicValRat p (a:ℚ)+2*(padicValRat p Γ+padicValRat p W)) :
    IsSquare (signedValue r δ Γ D W).den := by
  apply ZInQ.Mult.isSquare_den_of_even
  intro p pp bad
  let _ := Fact.mk pp
  have value := scalar_order p rad apos gn wn (D:=D)
  by_cases ev : Even (padicValRat p (a:ℚ))
  · obtain ⟨k,hk⟩:=ev
    exact ⟨k+(padicValRat p Γ+padicValRat p W-padicValRat p (1+(D:ℚ)*(a:ℚ)^2)), by omega⟩
  · have dvd : p∣a := by
      by_contra nd
      rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd nd] at ev
      exact ev (by simp)
    have good:=localOrder p pp dvd (Int.not_even_iff_odd.mp ev)
    rw [front_unit (Or.inr dvd),sub_zero] at value
    omega

theorem fixed_gamma_order (p : ℕ) [hp : Fact p.Prime] (member : p∈primes) :
    padicValRat p (gamma:ℚ)=2 := by
  have prime : ∀ q∈primes,Nat.Prime q := by decide
  have h:=valuation_prime_product (p:=p) primes prime
  rw [ite_eq_left member] at h
  have eqn : (∏ q∈primes,(q:ℚ))=(FixedPreparation.primorial:ℚ) := by rw [←prime_product,Nat.cast_prod]
  rw [eqn] at h
  change padicValRat p ((FixedPreparation.primorial^2:ℕ):ℚ)=2
  rw [Nat.cast_pow,padicValRat.pow,h]
  norm_num

/-- The local term is a unit on the union of the fixed and radicand primes.
All nine required depths then follow from the explicit gamma and denominator. -/
theorem scalar_prepared {r δ W : ℚ} {a : ℕ} (rad : δ*r=(a:ℚ)) (apos : 0<a)
    (wn : W≠0) (unit : ∀ p : ℕ, p.Prime → p∈primes ∨ p∣a → padicValRat p W=0)
    (interval : 0<signedValue r δ gamma denominator W ∧ signedValue r δ gamma denominator W<1/2) :
    Prepared (signedValue r δ gamma denominator W) := by
  have gn : (gamma:ℚ)≠0 := by exact_mod_cast gamma_positive.ne'
  refine ⟨scalar_square_den rad apos gn wn (fun p pp hit _ => ?_),interval.1,interval.2,?_⟩
  · rw [unit p pp (Or.inr hit),add_zero]
    have g:=zero_le_padicValRat_of_nat (p:=p) gamma
    have t:=zero_le_padicValRat_of_nat (p:=p) a
    omega
  · intro p mem
    have prime : ∀ q∈primes,Nat.Prime q := by decide
    let _ := Fact.mk (prime p mem)
    have divprim : p∣FixedPreparation.primorial := prime_product ▸ Finset.dvd_prod_of_mem (fun n:ℕ => n) mem
    have hit : p∣denominator := dvd_mul_of_dvd_right (dvd_pow divprim two_ne_zero) 126
    have value:=scalar_order p rad apos gn wn (D:=denominator)
    rw [fixed_gamma_order p mem,unit p (prime p mem) (Or.inl mem),
      front_unit (Or.inl hit),sub_zero,add_zero] at value
    have nonneg:=zero_le_padicValRat_of_nat (p:=p) a
    omega

#print axioms scalar_order
#print axioms scalar_square_den
#print axioms fixed_gamma_order
#print axioms scalar_prepared
end Sun28.FinitePole

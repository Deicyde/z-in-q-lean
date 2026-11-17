import ExceptionalDivisor
import GaussianSelection

/-! Evaluating at the common zero shift makes the slope numerator a unit at
each exceptional prime. The one prescribed divisor handles all three scales. -/
namespace Sun28.FiniteWitness
open ZInQ Sun28.Ordinary Sun28.Forward Sun28.FixedPreparation Sun28.WitnessIndices
open Sun28.ContactFactors Sun28.Exceptional Sun28.RealPoleBounds Sun28.ScalarHeight
open IsDedekindDomain NumberField
open scoped NumberField
noncomputable section

theorem numerator_unit {A : Fin 3→ℚ} {u v : ℕ} (values : PrimeValues A u v)
    (large : ∀ d∈shifts A,65<values.value d) {p : ℕ} (fixed : p∈primes) :
    u.Prime ∧ padicValRat p (u:ℚ)=0 := by
  have hs : (0:ℚ)∈shifts A := by simpa using shift_mem A 0 (a:=0) (by simp [marks])
  have eq : values.value 0=u := by
    have e := values.rational_equation hs
    simp only [zero_mul,add_zero] at e
    exact_mod_cast e
  have prime : ∀ q∈primes,Nat.Prime q := by decide
  have small : ∀ q∈primes,q≤23 := by decide
  have up : u.Prime := eq ▸ values.prime 0 hs
  have big : 65<u := eq ▸ large 0 hs
  have nd : ¬p∣u := fun e => (show p≠u by have := small p fixed; omega)
    ((Nat.prime_dvd_prime_iff_eq (prime p fixed) up).mp e)
  exact ⟨up,by rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd nd]; rfl⟩

abbrev basePrime (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,hp⟩

theorem fixed_depths {A : Fin 3→ℚ} {u v : ℕ} (values : PrimeValues A u v)
    (alive : ∀ j,A j≠0) (vp : 0<v) (large : ∀ d∈shifts A,65<values.value d)
    (dvd : requiredDivisor A∣v) (w : NinePoints) (M : ℕ) (b : ℤ) (β : ℚ)
    (intAt : ∀ p : ℕ, ∀ _hp : p∈primes, ∀ prime : p.Prime,
      ∀ place : HeightOneSpectrum (𝓞 K0), place.asIdeal.LiesOver (basePrime p prime).asIdeal →
      IntegralAtBoth place (ordinaryAt w M b β)) :
    ∀ j, let t:=argument A u v j
      let T:=ordinaryTraceAt w M b β (A j) t
      ∀ p∈primes,4≤padicValRat p (detector (A j) t/T^2) := by
  intro j t T p hp
  have prime : ∀ q∈primes,Nat.Prime q := by decide
  have pp:=prime p hp
  let _ : Fact p.Prime:=⟨pp⟩
  let q:=basePrime p pp
  obtain ⟨P,maximal,lie⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S:=𝓞 K0) q.asIdeal
  let place : HeightOneSpectrum (𝓞 K0) := ⟨P,maximal.isPrime,Ideal.ne_bot_of_mem_primesOver q.ne_bot ⟨maximal.isPrime,lie⟩⟩
  let _ : place.asIdeal.LiesOver q.asIdeal:=lie
  let W:=dilation A*v
  have Wp : 0<W := Nat.mul_pos (dilation_positive A) vp
  have divW : requiredDivisor A∣W := dvd.trans (dvd_mul_left _ _)
  obtain ⟨up,unit⟩ := numerator_unit values large hp
  obtain ⟨_,_,_,_,_,_,_,_,_,deep⟩ := ordinary_depth_at_prime hp place w M b β (A j) (u:ℚ) (W:ℚ) t
    (alive j) (by exact_mod_cast up.ne_zero) (by exact_mod_cast Wp.ne') rfl unit
    (large_of_dvd A Wp.ne' divW hp j) (intAt p hp pp place lie)
  exact deep

end
end Sun28.FiniteWitness
#print axioms Sun28.FiniteWitness.numerator_unit
#print axioms Sun28.FiniteWitness.fixed_depths

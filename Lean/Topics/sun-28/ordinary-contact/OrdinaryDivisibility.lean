import OrdinaryAnchors
import PrimeTrace
import Mathlib.RingTheory.Coprime.Lemmas

/-! Rational descent and multiplication over the distinct contact primes. -/
open Sun28.ScalarTrace NumberField IsDedekindDomain
namespace Sun28.Ordinary

variable {K : Type*} [Field K] [NumberField K]

/-- With the top-valued convention the conclusion remains true for q=0. -/
theorem numerator_power {p k : ℕ} [Fact p.Prime] {q : ℚ}
    (hq : q≠0 → (k:ℤ) ≤ padicValRat p q) : (p:ℤ)^k ∣ q.num := by
  rcases eq_or_ne q 0 with rfl|hn
  · simp
  apply (padicValInt_dvd_iff k q.num).mpr
  right
  have H := hq hn
  rw [padicValRat_def] at H
  omega

theorem rational_outputs {p : ℕ} [Fact p.Prime]
    (v : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver v.asIdeal] (hp : (Rat.HeightOneSpectrum.primesEquiv v).1=p)
    (unram : w.asIdeal.ramificationIdx (𝓞 ℚ)=1)
    {Δ : ℤ} {β : ℚ} {n : ℤ}
    (hd : (64:WithTop ℤ) ≤ discreteOrder (w.valuation K) (Δ:K))
    (hb : (16:WithTop ℤ) ≤ discreteOrder (w.valuation K) (algebraMap ℚ K β-(n:K))) :
    (p:ℤ)^64 ∣ Δ ∧ (p:ℤ)^16 ∣ (β-n).num := by
  have base {q : ℚ} (nq : q≠0) : discreteOrder (w.valuation K) (algebraMap ℚ K q) =
      ((padicValRat p q:ℤ):WithTop ℤ) := by
    simpa [hp,unram] using prime_order_rat v w nq
  constructor
  · have dn := numerator_power (p:=p) (k:=64) (q:=(Δ:ℚ)) (fun h => by
      have D : (64:WithTop ℤ) ≤ discreteOrder (w.valuation K) (algebraMap ℚ K (Δ:ℚ)) := by simpa using hd
      rw [base h] at D
      exact WithTop.coe_le_coe.mp D)
    simpa using dn
  · apply numerator_power
    intro nq
    have b : (16:WithTop ℤ) ≤ discreteOrder (w.valuation K) (algebraMap ℚ K (β-n)) := by simpa using hb
    rw [base nq] at b
    exact WithTop.coe_le_coe.mp b

theorem product_prime_powers {P : Finset ℕ} {k : ℕ} {z : ℤ}
    (prime : ∀ p ∈ P, p.Prime) (one : ∀ p ∈ P, (p:ℤ)^k ∣ z) :
    ((∏ p ∈ P, (p:ℤ))^k) ∣ z := by
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_coprime _ one
  intro p hp q hq neq
  apply IsCoprime.pow
  rw [Int.isCoprime_iff_gcd_eq_one]
  simpa using (Nat.coprime_primes (prime p hp) (prime q hq)).mpr neq

/-- Each of the three detectors has its own product. Their supports may overlap. -/
theorem three_contact_products (P : Fin 3 → Finset ℕ) {Δ : ℤ} {q : ℚ}
    (prime : ∀ j p, p ∈ P j → p.Prime)
    (localTests : ∀ j p, p ∈ P j → (p:ℤ)^64 ∣ Δ ∧ (p:ℤ)^16 ∣ q.num) :
    ∀ j, (∏ p ∈ P j, (p:ℤ))^64 ∣ Δ ∧
      (∏ p ∈ P j, p)^16 ∣ q.num.natAbs := by
  intro j
  refine ⟨product_prime_powers (prime j) (fun p h => (localTests j p h).1),?_⟩
  have h := product_prime_powers (prime j) (fun p hp => (localTests j p hp).2)
  rw [← Nat.cast_prod] at h
  have hnat := Int.natAbs_dvd_natAbs.mpr h
  simpa only [Int.natAbs_pow,Int.natAbs_natCast] using hnat

end Sun28.Ordinary
#print axioms Sun28.Ordinary.numerator_power
#print axioms Sun28.Ordinary.rational_outputs
#print axioms Sun28.Ordinary.product_prime_powers
#print axioms Sun28.Ordinary.three_contact_products

import WeightedIndex
import ScalarTwists

namespace Sun28.ScalarDepth
open NumberField IsDedekindDomain Sun28.Scalar Sun28.ScalarHeight Sun28.Ordinary
open Sun28.WitnessHeight Sun28.ScalarLucas Sun28.FixedPreparation
open scoped NumberField
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

def contactValue (x : ℚ) := scalarRadicand (beta x)

/-- All positive odd valuations seen by the scalar tree above the formal-chart cutoff. -/
def primes (x : ℚ) : Finset ℕ :=
  (contactValue x).num.natAbs.primeFactors.filter
    fun p => 65 < p ∧ 0 < padicValRat p (contactValue x) ∧ Odd (padicValRat p (contactValue x))

theorem mem_primes {x : ℚ} {p : ℕ} :
    p ∈ primes x ↔ p.Prime ∧ 65 < p ∧ 0 < padicValRat p (contactValue x) ∧ Odd (padicValRat p (contactValue x)) := by
  rw [primes,Finset.mem_filter,Nat.mem_primeFactors]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · rintro ⟨hp,large,pos,odd⟩
    have n : 0 < padicValNat p (contactValue x).num.natAbs := by
      rw [padicValRat_def] at pos
      change 0 < (padicValNat p (contactValue x).num.natAbs : ℤ)-_ at pos
      omega
    have nz : (contactValue x).num.natAbs ≠ 0 := by rintro e; simp [e] at n
    exact ⟨⟨hp,dvd_of_one_le_padicValNat n,nz⟩,large,pos,odd⟩

def exponent (x : ℚ) (p : ℕ) := 47*(padicValRat p (contactValue x)).toNat+1
def modulus (x : ℚ) : ℕ := ∏ p ∈ primes x, p^(exponent x p)

theorem modulus_pos (x : ℚ) : 0 < modulus x := Finset.prod_pos
  fun _ mem => pow_pos (mem_primes.mp mem).1.pos _

private theorem units_at {p : ℕ} [hp : Fact p.Prime] (large : 65 < p) :
    padicValRat p (gamma:ℚ)=0 ∧ ∀ μ∈smallMultipliers, padicValRat p μ=0 := by
  have nd (q : ℕ) (small : q ≤ 65) (pos : 0 < q) : ¬p∣q :=
    fun h => by have := Nat.le_of_dvd pos h;omega
  constructor
  · have h : ¬ p∣2*3*5*7*11*13*17*19*23 := by
      simp only [hp.out.dvd_mul,nd 2 (by decide) (by decide),nd 3 (by decide) (by decide),
        nd 5 (by decide) (by decide),nd 7 (by decide) (by decide),nd 11 (by decide) (by decide),
        nd 13 (by decide) (by decide),nd 17 (by decide) (by decide),nd 19 (by decide) (by decide),
        nd 23 (by decide) (by decide),or_self,not_false_eq_true]
    have no : ¬ p ∣ gamma := fun d => h (hp.out.dvd_of_dvd_pow (show p∣Sun28.FixedPreparation.primorial^2 from d))
    rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd no];rfl
  · intro μ h
    apply support_unit
    intro hmem
    have pin : p ∈ preparationPrimes smallMultipliers :=
      Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨μ,h,hmem⟩)
    rw [preparation_primes] at pin
    simp only [Sun28.FixedPreparation.primes,Finset.mem_insert,Finset.mem_singleton] at pin
    omega

theorem modulus_dvd {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]
    {ρ : K} (root : ρ^2=2) {h s : ℤ} (hh : h≠0) (x : ℚ)
    (tree : TreeCertificate root h s (contactValue x) gamma denominator smallMultipliers) :
    (modulus x : ℤ) ∣ s-1 := by
  unfold modulus
  push_cast
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq neq
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa using (Nat.coprime_primes (mem_primes.mp hp).1 (mem_primes.mp hq).1).mpr neq
  · intro p mem
    obtain ⟨pr,large,pos,odd⟩ := mem_primes.mp mem
    let _ : Fact p.Prime := ⟨pr⟩
    let v := (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,pr⟩
    obtain ⟨P,maximal,lie⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S:=𝓞 K) v.asIdeal
    let w : HeightOneSpectrum (𝓞 K) := ⟨P,maximal.isPrime,Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨maximal.isPrime,lie⟩⟩
    let _ : w.asIdeal.LiesOver v.asIdeal := lie
    obtain ⟨gu,mult⟩ := units_at (p:=p) large
    exact weighted_order_at_prime large w root (ShortFormal.ordinaryFormalChart p w) hh
      denominator smallMultipliers pos odd (by exact_mod_cast gamma_positive.ne') gu mult tree

theorem radical_power_dvd (x : ℚ) : (radical x)^48 ∣ modulus x := by
  have subset : scalarPrimes x ⊆ primes x := by
    intro p hp
    rw [←scalar_support_exact] at hp
    obtain ⟨prime,out,_⟩ := mem_oldContactPrimes.mp hp
    let _ : Fact p.Prime := ⟨prime⟩
    have high : 76176 < p := by
      by_contra! le
      exact out (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),prime⟩)
    exact mem_primes.mpr ⟨prime,by omega,old_scalar_contact high x _ hp⟩
  unfold radical Sun28.FiveMarkUnits.primeProduct
  rw [← Finset.prod_pow]
  apply dvd_trans (Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p^48) subset)
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  have positive := (mem_primes.mp hp).2.2.1
  exact pow_dvd_pow p (show 48 ≤ exponent x p by dsimp [exponent];omega)

end
end Sun28.ScalarDepth
#print axioms Sun28.ScalarDepth.mem_primes
#print axioms Sun28.ScalarDepth.modulus_pos
#print axioms Sun28.ScalarDepth.modulus_dvd
#print axioms Sun28.ScalarDepth.radical_power_dvd

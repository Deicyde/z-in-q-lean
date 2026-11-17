import IntegralReference

/-! The minimum of the attainable integral discriminant orders and the global
product of those minima. The reference equation controls finite support. -/
namespace ZInQBlueprint.MinimalDiscriminant
open Polynomial IsDedekindDomain NumberField UniqueFactorizationMonoid WithZero
noncomputable section
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

def Attained (f : ℚ[X]) (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) : Prop :=
  ∃ E : IntegralEquation (completedVal w) f, completedVal w E.discriminant = exp (-(n:ℤ))

private theorem at_reference {f : ℚ[X]} {z : ℤ} (hz : z ≠ 0) (w : HeightOneSpectrum (𝓞 K))
    (ref : (integralReference (completedVal w) f).discriminant = (z:w.adicCompletion K)) :
    Attained f w ((normalizedFactors (Ideal.span {(z : 𝓞 K)})).count w.asIdeal) := by
  refine ⟨integralReference (completedVal w) f,?_⟩
  have hn : (z : 𝓞 K) ≠ 0 := by exact_mod_cast hz
  have hi := Ideal.span_singleton_eq_bot.not.mpr hn
  have comp (k : K) : completedVal w (algebraMap K (w.adicCompletion K) k) = w.valuation K k :=
    w.valuedAdicCompletion_eq_valuation' k
  rw [ref]
  have cf : completedVal w (z:w.adicCompletion K) = w.valuation K (z:K) := by
    simpa only [map_intCast] using comp (z:K)
  rw [cf]
  have val : w.valuation K (z:K) = w.intValuation (z : 𝓞 K) := by
    simpa only [map_intCast] using w.valuation_of_algebraMap (K:=K) (z:𝓞 K)
  rw [val,w.intValuation_eq_exp_neg_multiplicity hn,w.count_normalizedFactors_eq_multiplicity hi]

private theorem some_order (f : ℚ[X]) (nz : f.discr ≠ 0) (w : HeightOneSpectrum (𝓞 K)) :
    ∃ n, Attained f w n := by
  obtain ⟨z,hz,h⟩ := reference_integer f nz
  exact ⟨_,at_reference hz w (h _ _)⟩

/-- Minimum among integral discriminant orders. For actual genus-two
Weierstrass equations the discriminant is integral, also above 2. -/
def localOrder (f : ℚ[X]) (nz : f.discr ≠ 0) (w : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Nat.find (some_order f nz w)

theorem localOrder_attained (f : ℚ[X]) (nz : f.discr ≠ 0) (w : HeightOneSpectrum (𝓞 K)) :
    Attained f w (localOrder f nz w) := Nat.find_spec (some_order f nz w)

theorem localOrder_le (f : ℚ[X]) (nz : f.discr ≠ 0) (w : HeightOneSpectrum (𝓞 K))
    {n : ℕ} (h : Attained f w n) : localOrder f nz w ≤ n := Nat.find_min' _ h

private def orderAtIdeal (f : ℚ[X]) (nz : f.discr ≠ 0) (P : Ideal (𝓞 K)) : ℕ :=
  if h : Prime P then localOrder f nz ⟨P,Ideal.isPrime_of_prime h,h.ne_zero⟩ else 0

private theorem orderOnPrime (f : ℚ[X]) (nz : f.discr ≠ 0) (w : HeightOneSpectrum (𝓞 K)) :
    orderAtIdeal f nz w.asIdeal = localOrder f nz w := by
  have hp : Prime w.asIdeal := (Ideal.prime_iff_isPrime (by exact w.ne_bot)).mpr w.isPrime
  simp [orderAtIdeal,hp]

private theorem local_ideal_product {f : ℚ[X]} (nz : f.discr ≠ 0) {z : ℤ} (hz : z ≠ 0)
    (ref : ∀ w : HeightOneSpectrum (𝓞 K), (integralReference (completedVal w) f).discriminant = (z:w.adicCompletion K)) :
    ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ ∀ w : HeightOneSpectrum (𝓞 K),
      (normalizedFactors I).count w.asIdeal = localOrder f nz w := by
  classical
  let S := (normalizedFactors (Ideal.span {(z : 𝓞 K)})).toFinset
  let factors : Multiset (Ideal (𝓞 K)) := ∑ P ∈ S, Multiset.replicate (orderAtIdeal f nz P) P
  have primes : ∀ Q ∈ factors, Prime Q := by
    intro Q h
    obtain ⟨P,hP,hQ⟩ := Multiset.mem_sum.mp h
    have eq : Q = P := (Multiset.mem_replicate.mp hQ).2
    subst Q
    exact prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)
  have nonzero : factors.prod ≠ 0 := by
    intro h
    exact (primes 0 (Multiset.prod_eq_zero_iff.mp h)).ne_zero rfl
  refine ⟨factors.prod,nonzero,?_⟩
  intro w
  rw [normalizedFactors_prod_of_prime primes]
  change (∑ P ∈ S, Multiset.replicate (orderAtIdeal f nz P) P).count w.asIdeal = _
  rw [Multiset.count_sum']
  by_cases mem : w.asIdeal ∈ S
  · rw [Finset.sum_eq_single w.asIdeal]
    · simp [orderOnPrime]
    · intro P _ hP
      simp [Multiset.count_replicate,hP]
    · exact fun h => (h mem).elim
  · have missing : w.asIdeal ∉ normalizedFactors (Ideal.span {(z : 𝓞 K)}) :=
      fun h => mem (Multiset.mem_toFinset.mpr h)
    have small := localOrder_le f nz w (at_reference hz w (ref w))
    rw [Multiset.count_eq_zero.mpr missing] at small
    rw [Nat.eq_zero_of_le_zero small]
    apply Finset.sum_eq_zero
    intro P hP
    have hne : w.asIdeal ≠ P := fun e => mem (e ▸ hP)
    simp [Multiset.count_replicate,Ne.symm hne]

theorem exists_minimal_ideal (f : ℚ[X]) (nz : f.discr ≠ 0) :
    ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ ∀ w : HeightOneSpectrum (𝓞 K),
      (normalizedFactors I).count w.asIdeal = localOrder f nz w := by
  obtain ⟨z,hz,h⟩ := reference_integer f nz
  exact local_ideal_product nz hz (fun w => h _ _)

/-- The unique integral ideal with the local minimal exponents. -/
def minimalIdeal (f : ℚ[X]) (nz : f.discr ≠ 0) : Ideal (𝓞 K) :=
  Classical.choose (exists_minimal_ideal (K:=K) f nz)

theorem minimalIdeal_spec (f : ℚ[X]) (nz : f.discr ≠ 0) :
    minimalIdeal (K:=K) f nz ≠ ⊥ ∧ ∀ w : HeightOneSpectrum (𝓞 K),
      (normalizedFactors (minimalIdeal f nz)).count w.asIdeal = localOrder f nz w :=
  Classical.choose_spec (exists_minimal_ideal (K:=K) f nz)

theorem minimalIdeal_represented (f : ℚ[X]) (nz : f.discr ≠ 0) :
    RepresentedAtPlaces f (minimalIdeal (K:=K) f nz) := by
  intro w
  rw [(minimalIdeal_spec f nz).2 w]
  exact localOrder_attained f nz w

theorem signed_disc_ne {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    (BinaryCover.paper ℚ u false).discr ≠ 0 := by
  let f := BinaryCover.paper ℚ u false
  have frac := (JacobianHeight.paper_igusa_quotient hu).2
  have hj : SixContact.J u ≠ 0 := (CoarseConic.unmarked_range hu).2.ne
  have plus : SixContact.J u+1 ≠ 0 := by linarith [(CoarseConic.unmarked_range hu).1]
  have pos : (SixContact.J u)^3 / (12*(SixContact.J u+1))^5 ≠ 0 :=
    div_ne_zero (pow_ne_zero _ hj) (pow_ne_zero _ (mul_ne_zero (by norm_num) plus))
  intro h
  exact pos (frac.symm.trans (by simp [JacobianHeight.igusaJ10,h]))

/-- Uniform on every number field, with the minimal discriminant built from
integral equations in its own completions. -/
theorem signed_minimal_divisibility {u : ℚ} (hu : u ∉ ZInQ.contactSet) (K : Type) [Field K] [NumberField K] :
    (Ideal.span {((SixContact.J u).den : 𝓞 K)})^2 ∣
      minimalIdeal (K:=K) (BinaryCover.paper ℚ u false) (signed_disc_ne hu) :=
  denominator_dvd hu _ (minimalIdeal_spec _ _).1 (minimalIdeal_represented _ _)

end
end ZInQBlueprint.MinimalDiscriminant
#print axioms ZInQBlueprint.MinimalDiscriminant.localOrder_attained
#print axioms ZInQBlueprint.MinimalDiscriminant.localOrder_le
#print axioms ZInQBlueprint.MinimalDiscriminant.exists_minimal_ideal
#print axioms ZInQBlueprint.MinimalDiscriminant.minimalIdeal_spec
#print axioms ZInQBlueprint.MinimalDiscriminant.minimalIdeal_represented
#print axioms ZInQBlueprint.MinimalDiscriminant.signed_minimal_divisibility

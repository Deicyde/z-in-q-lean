import ForwardSoundness
import ScalarMultipliers

/-! Concrete preparation data on the original five-contact cutoff. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
namespace Sun28.FixedPreparation
open ZInQ Sun28.Forward Sun28.Ordinary Sun28.ScalarHeight Sun28.WitnessIndices
noncomputable section

def primes : Finset ℕ := {2,3,5,7,11,13,17,19,23}
def primorial : ℕ := 223092870
def gamma : ℕ := primorial^2
def denominator : ℕ := 126*gamma
def anchor : ℤ := (Nat.factorial 576 : ℕ)

theorem multiplier_count : smallMultipliers.card=64 := by decide +revert

private theorem int_support (n : ℤ) : support (n:ℚ)=n.natAbs.primeFactors := by simp [support]

private theorem primorial_factors : primorial.primeFactors=primes := by
  have fac : primorial=2*3*5*7*11*13*17*19*23 := by decide
  have all : (2:ℕ).Prime ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7 ∧ Nat.Prime 11 ∧ Nat.Prime 13 ∧ Nat.Prime 17 ∧ Nat.Prime 19 ∧ Nat.Prime 23 := by decide
  rcases all with ⟨p2,p3,p5,p7,p11,p13,p17,p19,p23⟩
  rw [fac]
  simp (disch := decide) only [Nat.primeFactors_mul,p2.primeFactors,p3.primeFactors,
    p5.primeFactors,p7.primeFactors,p11.primeFactors,p13.primeFactors,p17.primeFactors,p19.primeFactors,p23.primeFactors]
  decide

theorem preparation_primes : preparationPrimes smallMultipliers=primes := by
  apply Finset.Subset.antisymm
  · intro p hp
    rcases Finset.mem_union.mp hp with p23|u
    · simp only [Finset.mem_insert,Finset.mem_singleton] at p23
      rcases p23 with rfl|rfl <;> decide
    · obtain ⟨μ,hm,hp⟩ := Finset.mem_biUnion.mp u
      obtain ⟨⟨n,a,b,i⟩,_,rfl⟩ := Finset.mem_image.mp hm
      rw [int_support] at hp
      have factor : ∀ (n a b : Bool) (i : Fin 8), (shift n a b i).natAbs ∣ primorial := by decide
      rw [←primorial_factors]
      exact Nat.primeFactors_mono (factor n a b i) (by decide) hp
  · intro p hp
    have mult : ∀ p∈primes, (p:ℚ)∈smallMultipliers := by decide
    have prime : ∀ p∈primes, Nat.Prime p := by decide
    refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p,mult p hp,?_⟩)
    have e : support (p:ℚ)=p.primeFactors := by simp [support]
    rw [e,(prime p hp).primeFactors]
    simp

theorem prime_product : (∏ p ∈ primes,p)=primorial := by decide +revert

theorem gamma_formula : preparationGamma smallMultipliers 2=gamma := by
  rw [preparationGamma,preparation_primes,prime_product,gamma]

theorem gamma_positive : 0<gamma := by norm_num [gamma,primorial]

theorem anchor_nonzero : anchor≠0 := by
  exact Int.ofNat_ne_zero.mpr (Nat.factorial_ne_zero 576)

private theorem prime_small {p : ℕ} (hp : p.Prime) (bound : p≤76176) : p∈oldCutoff := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp⟩

private theorem anchor_support : anchor.natAbs.primeFactors ⊆ oldCutoff := by
  intro p h
  obtain ⟨prime,dvd,_⟩ := Nat.mem_primeFactors.mp h
  change p∣Nat.factorial 576 at dvd
  exact prime_small prime (le_trans (prime.dvd_factorial.mp dvd) (by decide : 576≤76176))

theorem fixed_cutoff : commonCutoff anchor (gamma:ℚ) smallMultipliers smallMultipliers=oldCutoff := by
  have gam := preparationGamma_support _ 2 small_support
  rw [gamma_formula] at gam
  have many : smallMultipliers.biUnion support ⊆ oldCutoff := by
    intro p mem
    obtain ⟨μ,hm,hp⟩ := Finset.mem_biUnion.mp mem
    exact small_support μ hm hp
  have sep : separation.primeFactors ⊆ oldCutoff := by
    intro p hp
    obtain ⟨prime,dvd,-⟩ := Nat.mem_primeFactors.mp hp
    rw [separation_arithmetic.1] at dvd
    simp only [prime.dvd_mul] at dvd
    have bound (n : ℕ) (d : p∣n) (pos : 0<n) (b : n≤76176) : p∈oldCutoff :=
      prime_small prime ((Nat.le_of_dvd pos d).trans b)
    rcases dvd with ((((((((d|d)|d)|d)|d)|d)|d)|d)|d) <;> exact bound _ d (by decide) (by decide)
  unfold commonCutoff exceptional
  apply Finset.Subset.antisymm
  · exact Finset.union_subset (Finset.union_subset (Finset.union_subset (fun _ h => h) gam) many)
      (Finset.union_subset many (Finset.union_subset anchor_support sep))
  · intro p hp
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hp))

end
end Sun28.FixedPreparation
#print axioms Sun28.FixedPreparation.multiplier_count
#print axioms Sun28.FixedPreparation.preparation_primes
#print axioms Sun28.FixedPreparation.prime_product
#print axioms Sun28.FixedPreparation.gamma_formula
#print axioms Sun28.FixedPreparation.gamma_positive
#print axioms Sun28.FixedPreparation.anchor_nonzero
#print axioms Sun28.FixedPreparation.fixed_cutoff

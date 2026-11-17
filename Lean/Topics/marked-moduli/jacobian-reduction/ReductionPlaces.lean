import HeightBudget
import SignedKernel
import GlobalTwist

/-! The prime set in the height inequality and the three local equations. -/
namespace ZInQBlueprint.ReductionPlaces
open ZInQ IsDiscreteValuationRing RationalClusters

def poleInteger (u : ℚ) : ℤ := ResidualFactors.poleForm u.num (u.den : ℤ)

theorem pole_pos (u : ℚ) : 0 < poleInteger u := by
  have hb : 0 < (u.den : ℤ) := by exact_mod_cast u.den_pos
  have h : 7 * poleInteger u = (7 * u.num + 150 * (u.den : ℤ))^2 + 2700 * (u.den : ℤ)^2 := by
    unfold poleInteger ResidualFactors.poleForm
    ring
  have hs := sq_nonneg (7 * u.num + 150 * (u.den : ℤ))
  have ht := sq_pos_of_pos hb
  omega

theorem contact_ne_zero {u : ℚ} (hu : u ∉ contactSet) : GlobalTwist.contactInteger u ≠ 0 := by
  change OddSupport.integerValue u ≠ 0
  have h : (OddSupport.integerValue u : ℚ) ≠ 0 := by
    rw [OddSupport.binary_identity]
    exact mul_ne_zero (Mult.contactPoly_ne_zero hu) (pow_ne_zero _ (by exact_mod_cast u.den_nz))
  exact_mod_cast h

variable {p : ℕ} [hp : Fact p.Prime]

/-- Homogenizing the sextic adds six times the order of the denominator.
This preserves parity even when the rational order is negative. -/
theorem contact_order (u : ℚ) (hu : u ∉ contactSet) :
    (((GlobalTwist.contactInteger u).natAbs.factorization p : ℕ) : ℤ) =
      padicValRat p (Mult.contactPoly u) + 6 * padicValRat p (u.den : ℚ) := by
  have hd : (u.den : ℚ) ≠ 0 := by exact_mod_cast u.den_nz
  have h := congrArg (padicValRat p) (OddSupport.binary_identity u)
  rw [padicValRat.of_int, padicValInt, ← Nat.factorization_def _ hp.out,
    padicValRat.mul (Mult.contactPoly_ne_zero hu) (pow_ne_zero _ hd), padicValRat.pow] at h
  change (((OddSupport.integerValue u).natAbs.factorization p : ℕ) : ℤ) = _
  simpa using h

/-- Away from 2, 3 and 5 the variable part of the conductor detects exactly
the odd orders of the integral contact product outside the chosen set. -/
theorem dvd_contactSupport_iff {S : Finset ℕ} {u : ℚ} (hu : u ∉ contactSet) (h5 : 5 < p) :
    p ∣ contactSupport S u ↔ p ∉ S ∧ Odd ((GlobalTwist.contactInteger u).natAbs.factorization p) := by
  rw [Mult.prime_dvd_contactSupport_iff' hu hp.out, ← OddSupport.odd_poly_iff hu h5]
  apply and_congr_right
  intro _
  have h := contact_order (p := p) u hu
  rw [Int.odd_iff, Nat.odd_iff]
  omega

theorem conductor_iff {S : Finset ℕ} {u : ℚ} (hu : u ∉ contactSet) (h5 : 5 < p) :
    p ∈ HeightBudget.conductorPrimes S u ↔
      p ∈ S ∨ Odd ((GlobalTwist.contactInteger u).natAbs.factorization p) := by
  classical
  rw [HeightBudget.conductorPrimes, Finset.mem_union, Nat.mem_primeFactors,
    dvd_contactSupport_iff hu h5]
  have hpos := (contactSupport_pos S u).ne'
  simp only [hp.out, true_and]
  tauto

theorem pole_valuation (u : ℚ) :
    addVal ℤ_[p] (G p u) = ((poleInteger u).natAbs.factorization p : ℕ∞) := by
  have hz := pole_pos u
  have hcast : ((poleInteger u).natAbs : ℤ_[p]) = G p u := by
    have he : ((poleInteger u).natAbs : ℤ) = poleInteger u := by
      rw [Int.natCast_natAbs, abs_of_pos hz]
    have hh := congrArg (fun z : ℤ => (z : ℤ_[p])) he
    simpa [poleInteger, G, ResidualFactors.poleForm] using hh
  rw [← hcast]
  exact GlobalTwist.nat_valuation p _ (by simpa using hz.ne')

/-- The ordinary, even-contact and pole alternatives have disjoint valuation
pairs. In both exceptional alternatives the depth is strictly positive. -/
def LocalCases (p : ℕ) [Fact p.Prime] (u : ℚ) : Prop :=
  (IsUnit (F p u) ∧ IsUnit (G p u)) ∨
  (∃ k : ℕ, 0 < k ∧ addVal ℤ_[p] (F p u) = ((2*k : ℕ) : ℕ∞) ∧ IsUnit (G p u)) ∨
  (∃ g : ℕ, 0 < g ∧ IsUnit (F p u) ∧ addVal ℤ_[p] (G p u) = (g : ℕ∞))

theorem localCases_iff_even {u : ℚ} (hu : u ∉ contactSet) (h11 : 11 ≤ p) :
    LocalCases p u ↔ Even ((GlobalTwist.contactInteger u).natAbs.factorization p) := by
  let n := (GlobalTwist.contactInteger u).natAbs.factorization p
  let g := (poleInteger u).natAbs.factorization p
  have hf : addVal ℤ_[p] (F p u) = (n : ℕ∞) := GlobalTwist.contact_valuation p u (contact_ne_zero hu)
  have hg : addVal ℤ_[p] (G p u) = (g : ℕ∞) := pole_valuation u
  have zeroF (unit : IsUnit (F p u)) : n = 0 :=
    ENat.natCast_inj.mp (hf.symm.trans (addVal_eq_zero_iff.mpr unit))
  constructor
  · rintro (⟨unit, _⟩ | ⟨k, _, hk, _⟩ | ⟨g', _, unit, _⟩)
    · change Even n
      rw [zeroF unit]
      exact ⟨0, rfl⟩
    · exact ⟨k, by have h := ENat.natCast_inj.mp (hf.symm.trans hk); change n = k + k; omega⟩
    · change Even n
      rw [zeroF unit]
      exact ⟨0, rfl⟩
  · rintro ⟨k, hk⟩
    change n = k + k at hk
    by_cases zero : k = 0
    · have hn : n = 0 := by omega
      have unit : IsUnit (F p u) := addVal_eq_zero_iff.mp (by simpa [hn] using hf)
      by_cases gz : g = 0
      · exact Or.inl ⟨unit, addVal_eq_zero_iff.mp (by simpa [gz] using hg)⟩
      · exact Or.inr (Or.inr ⟨g, Nat.pos_of_ne_zero gz, unit, hg⟩)
    · have hv : addVal ℤ_[p] (F p u) = ((2*k : ℕ) : ℕ∞) := hf.trans (by rw [hk, two_mul])
      exact Or.inr (Or.inl ⟨k, Nat.pos_of_ne_zero zero, hv,
        (PadicParameters.even_contact_data h11 _ _ (PadicParameters.rational_primitive u)
          k (Nat.pos_of_ne_zero zero) hv).1⟩)

theorem outside_conductor {u : ℚ} (hu : u ∉ contactSet)
    (hs : p ∉ HeightBudget.conductorPrimes Mult.S_mul u) : 17 ≤ p ∧ LocalCases p u := by
  have hS : p ∉ Mult.S_mul := fun h => hs (Finset.mem_union_left _ h)
  have h324 := (Mult.not_mem_S_mul hp.out hS).1
  have he := mt (conductor_iff (p := p) hu (by omega)).mpr hs
  exact ⟨by omega, (localCases_iff_even hu (by omega)).mpr (Nat.not_odd_iff_even.mp (fun h => he (Or.inr h)))⟩

end ZInQBlueprint.ReductionPlaces
#print axioms ZInQBlueprint.ReductionPlaces.pole_pos
#print axioms ZInQBlueprint.ReductionPlaces.contact_ne_zero
#print axioms ZInQBlueprint.ReductionPlaces.contact_order
#print axioms ZInQBlueprint.ReductionPlaces.dvd_contactSupport_iff
#print axioms ZInQBlueprint.ReductionPlaces.conductor_iff
#print axioms ZInQBlueprint.ReductionPlaces.pole_valuation
#print axioms ZInQBlueprint.ReductionPlaces.localCases_iff_even
#print axioms ZInQBlueprint.ReductionPlaces.outside_conductor

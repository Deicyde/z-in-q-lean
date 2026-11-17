import FactorialCost
import OrientedPrimes

namespace Sun28.FinitePattern
open Finset ManuscriptV15.Arithmetic Sun28.ContactSieve Sun28.ContactFactors
open Sun28.NormSieve Sun28.MixedSieve Sun28.WeightedSelection Sun28.SinglePrime
open scoped Classical
noncomputable section

/-- The base requires both signs; above the base the plus sign suffices at every position. -/
def clean (K L : ℕ) (z : Gaussian) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 7 → p ≤ L →
    (¬ p ∣ adjacentNorm z true) ∧ (p ≤ K → ¬ p ∣ adjacentNorm z false)

/-- One and the same subset of the rational primes, for use at every polynomial shift. -/
def commonPrime (K L n : ℕ) : Prop :=
  n.Prime ∧ ∃ z : Gaussian, gaussianNorm z = n ∧ gaussianCongruent 16 z (9,0) ∧
    gaussianCongruent 7 z (1,3) ∧ clean K L z

theorem common_iff_clean {A : Fin 3 → ℚ} {d K L : ℕ} {H Y : ℝ}
    (a : Record A d H Y) (i : ↥(shifts A)) :
    commonPrime K L (a.values.value i) ↔ clean K L (a.gaussian i) := by
  let hp := a.values.prime i i.property
  constructor
  · rintro ⟨_,z,hn,h16,h7,hc⟩
    exact (oriented_unique hp hn (a.rays.norm i) h16 (a.rays.ray16 i) h7 (a.rays.ray7 i)) ▸ hc
  · intro h
    exact ⟨hp,a.gaussian i,a.rays.norm i,a.rays.ray16 i,a.rays.ray7 i,h⟩

theorem clean_below {A : Fin 3 → ℚ} {d K L κ : ℕ} {H Y : ℝ} {T : Finset ℕ}
    (a : Record A d H Y) (hT : ∀ p ∈ T, p ≤ K) (hκ : ∀ p ∈ κ.primeFactors, p ≤ K)
    (h : ∀ i : ↥(shifts A), commonPrime K L (a.values.value i)) : below a T κ L := by
  intro p prime odd seven le
  let _ : Fact p.Prime := ⟨prime⟩
  have good (i : ↥(shifts A)) := ((common_iff_clean a i).mp (h i)) p prime odd seven le
  refine ⟨fun i _ _ x => (good i).1 ((forbidden_iff odd _ _).mp x.1),
    fun _ i _ x => (good i).1 ((diagonal_iff odd _).mpr x).1, ?_, ?_⟩
  · intro mem i e hit
    cases e
    · exact (good i).2 (hT p mem) ((forbidden_iff odd _ _).mp hit)
    · exact (good i).1 ((forbidden_iff odd _ _).mp hit)
  · intro mem _ i hit
    exact (good i).2 (hκ p mem) ((forbidden_iff odd _ _).mp hit)

/-- The exact local one-colour density dominates the factor used in the factorial product. -/
theorem one_fibre {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) {t : ZMod p} (nz : t ≠ 0) :
    atom p ≤ ((bad p t true)ᶜ.card : ℝ) / (Fintype.card (Circle p t) : ℝ) := by
  have lo := circle_card_lower (by omega : p ≠ 2) nz
  have bd := bad_card (by omega : p ≠ 2) t true
  have b : ((bad p t true).card : ℝ) ≤ 2 := by exact_mod_cast bd
  have n : (p : ℝ) - 1 ≤ (Fintype.card (Circle p t) : ℝ) := by
    apply sub_le_iff_le_add.mpr
    exact_mod_cast (show p ≤ Fintype.card (Circle p t) + 1 by omega)
  have m : (7 : ℝ) ≤ p := by exact_mod_cast hp
  have x : 0 < (p : ℝ) - 1 := by linarith
  have y : 0 < (Fintype.card (Circle p t) : ℝ) := by linarith
  rw [Finset.card_compl, Nat.cast_sub (card_le_univ _), atom]
  apply (le_div_iff₀ y).mpr
  rw [sub_mul,one_mul,div_mul_eq_mul_div]
  have sub := mul_le_mul_of_nonneg_right b x.le
  have chief : (bad p t true).card * ((p : ℝ) - 1) ≤ 2 * Fintype.card (Circle p t) := by
    nlinarith only [sub,n]
  have h : ((bad p t true).card : ℝ) ≤ 2 * (Fintype.card (Circle p t) : ℝ) / ((p : ℝ) - 1) :=
    (le_div_iff₀ x).mpr chief
  linarith

/-- The paper forbids both signs at new primes. That smaller common ray set
still supplies the exact finite lower bound this application needs. -/
theorem paper_fibre {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) {t : ZMod p} (nz : t ≠ 0) :
    1 - 4 / ((p : ℝ) - 1) ≤ (((bad p t true ∪ bad p t false)ᶜ.card : ℝ) /
      (Fintype.card (Circle p t) : ℝ)) := by
  have lo := circle_card_lower (by omega : p ≠ 2) nz
  have bd := Finset.card_union_le (bad p t true) (bad p t false)
  have h := bad_card (by omega : p ≠ 2) t true
  have h' := bad_card (by omega : p ≠ 2) t false
  have b : ((bad p t true ∪ bad p t false).card : ℝ) ≤ 4 := by exact_mod_cast (by omega : (bad p t true ∪ bad p t false).card ≤ 4)
  have n : (p : ℝ) - 1 ≤ (Fintype.card (Circle p t) : ℝ) := by
    apply sub_le_iff_le_add.mpr
    exact_mod_cast (show p ≤ Fintype.card (Circle p t) + 1 by omega)
  have m : (7 : ℝ) ≤ p := by exact_mod_cast hp
  have x : 0 < (p : ℝ) - 1 := by linarith
  have y : 0 < (Fintype.card (Circle p t) : ℝ) := by linarith
  rw [Finset.card_compl, Nat.cast_sub (card_le_univ _)]
  apply (le_div_iff₀ y).mpr
  rw [sub_mul,one_mul,div_mul_eq_mul_div]
  have sub := mul_le_mul_of_nonneg_right b x.le
  have chief : ((bad p t true ∪ bad p t false).card : ℝ) * ((p : ℝ) - 1) ≤ 4 * Fintype.card (Circle p t) := by
    nlinarith only [sub,n]
  linarith only [(le_div_iff₀ x).mpr chief]

theorem one_fibre_product {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hp : 7 ≤ p) (t : ι → ZMod p) (nz : ∀ i,t i ≠ 0) :
    (atom p)^(Fintype.card ι) ≤ boxMass t (fun i => (bad p (t i) true)ᶜ) := by
  have large : (7:ℝ) ≤ p := by exact_mod_cast hp
  have pos : 0 ≤ atom p := by
    unfold atom
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  rw [box_product,←Finset.card_univ,←Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => pos) (fun i _ => one_fibre hp (nz i))

end
end Sun28.FinitePattern
#print axioms Sun28.FinitePattern.common_iff_clean
#print axioms Sun28.FinitePattern.clean_below
#print axioms Sun28.FinitePattern.one_fibre
#print axioms Sun28.FinitePattern.paper_fibre
#print axioms Sun28.FinitePattern.one_fibre_product

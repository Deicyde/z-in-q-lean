import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.NumberTheory.NumberField.ExistsRamified
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.Data.Finite.Perm
import Mathlib.Tactic

open scoped NumberField
open Polynomial

noncomputable section

namespace ZInQBlueprint.FibreInertia

/-- The splitting field of a rational polynomial of degree at most n has degree
dividing n!, including when the polynomial has repeated factors. -/
theorem degree_dvd_factorial (f : ℚ[X]) {n : ℕ} (hf : f.natDegree ≤ n) :
    Module.finrank ℚ f.SplittingField ∣ n.factorial := by
  classical
  let : IsGalois ℚ f.SplittingField := ⟨⟩
  let K := f.SplittingField
  let : Fact ((f.map (algebraMap ℚ K)).Splits) := ⟨SplittingField.splits f⟩
  have inj := Subgroup.card_dvd_of_injective (Gal.galActionHom f K) (Gal.galActionHom_injective f K)
  rw [Nat.card_perm] at inj
  change Nat.card Gal(f.SplittingField/ℚ) ∣ (Nat.card (f.rootSet K)).factorial at inj
  rw [IsGalois.card_aut_eq_finrank, Nat.card_coe_set_eq] at inj
  exact inj.trans (Nat.factorial_dvd_factorial ((f.ncard_rootSet_le K).trans hf))

theorem fibre_degree_bound (f : ℚ[X]) (h : f.natDegree ≤ 324) :
    IsGalois ℚ f.SplittingField ∧ Module.finrank ℚ f.SplittingField ≤ Nat.factorial 324 :=
  ⟨⟨⟩, Nat.le_of_dvd (Nat.factorial_pos _) (degree_dvd_factorial f h)⟩

variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

/-- A specialization embedding into a group of order dividing 144 gives the sharper
degree bound in the normalizer-cover argument. -/
theorem degree_dvd_144 {Γ : Type*} [Group Γ] (ι : Gal(K/ℚ) →* Γ) (hi : Function.Injective ι)
    (hΓ : Nat.card Γ ∣ 144) : Module.finrank ℚ K ∣ 144 := by
  rw [← IsGalois.card_aut_eq_finrank ℚ K]
  exact (Subgroup.card_dvd_of_injective ι hi).trans hΓ

local instance : MulSemiringAction Gal(K/ℚ) (𝓞 K) :=
  IsIntegralClosure.MulSemiringAction ℤ ℚ K (𝓞 K)

local instance : IsGaloisGroup Gal(K/ℚ) ℤ (𝓞 K) :=
  IsGaloisGroup.of_isFractionRing Gal(K/ℚ) ℤ (𝓞 K) ℚ K

/-- The inertia subgroup of the arithmetic fibre, acting on its ring of integers. -/
def inertia (P : Ideal (𝓞 K)) : Subgroup Gal(K/ℚ) := P.inertia Gal(K/ℚ)

/-- Its cardinal is the ramification index, including for nonprincipal primes upstairs. -/
theorem card_inertia (q : Ideal ℤ) [q.IsPrime] (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver q] :
    Nat.card (inertia K P) = P.ramificationIdx ℤ := by
  exact (Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(K/ℚ)) q P).trans
    (Ideal.ramificationIdxIn_eq_ramificationIdx q P Gal(K/ℚ))

theorem unramified_iff_card (q : Ideal ℤ) [q.IsPrime] (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver q] :
    Algebra.IsUnramifiedAt ℤ P ↔ Nat.card (inertia K P) = 1 := by
  rw [card_inertia K q P, Ideal.ramificationIdx_eq_one_iff]

end ZInQBlueprint.FibreInertia

#print axioms ZInQBlueprint.FibreInertia.degree_dvd_factorial
#print axioms ZInQBlueprint.FibreInertia.fibre_degree_bound
#print axioms ZInQBlueprint.FibreInertia.card_inertia
#print axioms ZInQBlueprint.FibreInertia.unramified_iff_card

#print axioms ZInQBlueprint.FibreInertia.degree_dvd_144

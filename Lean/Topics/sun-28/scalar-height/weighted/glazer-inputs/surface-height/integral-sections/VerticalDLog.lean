import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Tactic

/-! A logarithmic derivative along a reduced vertical component. -/
namespace ZInQBlueprint.IntegralSections

variable {V K : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]

/-- An integral relative derivation has integral logarithmic derivative even at poles. -/
theorem log_derivative_integral (p : ℕ) (uniformizer : Irreducible (p : V))
    (D : Derivation ℤ K K)
    (preserves : ∀ v : V, D (algebraMap V K v) ∈ (algebraMap V K).range)
    (x : K) (hx : x ≠ 0) : D x / x ∈ (algebraMap V K).range := by
  obtain ⟨n,u,hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    uniformizer hx
  rw [Units.smul_def, Algebra.smul_def] at hu
  have up : algebraMap V K (u : V) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 u.ne_zero
  have pp : algebraMap V K (p : V) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 uniformizer.ne_zero
  obtain ⟨w,hw⟩ := preserves (u : V)
  refine ⟨w * (↑u⁻¹ : V), ?_⟩
  have ui : algebraMap V K (↑u⁻¹ : V) = (algebraMap V K (u : V))⁻¹ := by
    exact (eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp))
  have dp : D (algebraMap V K (p : V) ^ n) = 0 := by
    rw [D.leibniz_zpow, map_natCast, D.map_natCast, smul_zero, zsmul_zero]
  rw [hu, D.leibniz, dp, smul_zero, zero_add, smul_eq_mul, map_mul, hw, ui]
  field_simp [up, zpow_ne_zero n pp]

/-- Each logarithmic Kähler differential belongs to the image of the integral lattice. -/
theorem log_kaehler_integral (p : ℕ) (uniformizer : Irreducible (p : V))
    (x : K) (hx : x ≠ 0) :
    ∃ w : KaehlerDifferential ℤ V, KaehlerDifferential.map ℤ ℤ V K w =
      x⁻¹ • KaehlerDifferential.D ℤ K x := by
  obtain ⟨n,u,hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    uniformizer hx
  rw [Units.smul_def, Algebra.smul_def] at hu
  have pp : algebraMap V K (p : V) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 uniformizer.ne_zero
  have ui : algebraMap V K (↑u⁻¹ : V) = (algebraMap V K (u : V))⁻¹ := by
    exact (eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp))
  refine ⟨(↑u⁻¹ : V) • KaehlerDifferential.D ℤ V (u : V), ?_⟩
  have dp : KaehlerDifferential.D ℤ K (algebraMap V K (p : V) ^ n) = 0 := by
    rw [Derivation.leibniz_zpow, map_natCast, Derivation.map_natCast, smul_zero, zsmul_zero]
  rw [hu, Derivation.leibniz, dp, smul_zero, zero_add, map_smul, KaehlerDifferential.map_D,
    ← algebraMap_smul K (↑u⁻¹ : V), ui, smul_smul, mul_inv_rev]
  congr 1
  field_simp [zpow_ne_zero n pp]

end ZInQBlueprint.IntegralSections
#print axioms ZInQBlueprint.IntegralSections.log_derivative_integral
#print axioms ZInQBlueprint.IntegralSections.log_kaehler_integral

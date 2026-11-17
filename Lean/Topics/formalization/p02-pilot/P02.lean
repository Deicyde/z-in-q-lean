import Theorems.Thm_QuadraticForm_exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real
import Mathlib

namespace QuarticP02

/-- The finite hypotheses in the literal coordinates of P02, at the same places
and with the same canonical algebra maps as the imported theorem. -/
def FiniteLocal (t : ℚ) : Prop :=
  ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
    ∃ x y z : v.adicCompletion ℚ,
      x ^ 2 + 6 * y ^ 2 - 2 * z ^ 2 =
        algebraMap ℚ (v.adicCompletion ℚ) (3 * t ^ 2 - 2)

theorem target_ne_zero (t : ℚ) : 3 * t ^ 2 - 2 ≠ 0 := by
  intro h
  have hn : ¬ IsSquare ((2 : ℚ) / 3) := by norm_num
  apply hn
  refine ⟨t, ?_⟩
  nlinarith [h]

/-- This identity uses the given rational ring map throughout. It avoids
identifying a completion's possibly non-definitional rational algebra instances. -/
private theorem toPure {R : Type*} [CommRing R] (f : ℚ →+* R)
    (k : ℚ) (x y z : R) (h : x ^ 2 + 6 * y ^ 2 - 2 * z ^ 2 = f k) :
    -f ((1 : ℚ) / 3) * x ^ 2 - f 2 * y ^ 2 + f ((1 : ℚ) / 3) * f 2 * z ^ 2 =
      f (-(1 / 3) * k) := by
  have hthree : (3 : R) * f (1 / 3) = 1 := by
    have hq : (3 : ℚ) * (1 / 3) = 1 := by norm_num
    simpa only [map_mul, map_ofNat, map_one] using congrArg f hq
  rw [map_mul, map_neg, ← h]
  simp only [map_ofNat]
  linear_combination (2 * y ^ 2) * hthree

private theorem realRep (k : ℝ) : ∃ x y z : ℝ, x ^ 2 + 6 * y ^ 2 - 2 * z ^ 2 = k := by
  by_cases hk : 0 ≤ k
  · exact ⟨Real.sqrt k, 0, 0, by simp [Real.sq_sqrt hk]⟩
  · have hneg : 0 ≤ -k / 2 := by linarith
    refine ⟨0, 0, Real.sqrt (-k / 2), ?_⟩
    rw [Real.sq_sqrt hneg]
    ring

/-- P02 in normalized coordinates. The real place and the nonzero target
are discharged here; the finite-place representations are the only input. -/
theorem normalized (t : ℚ) (hv : FiniteLocal t) :
    ∃ x y z : ℚ, x ^ 2 + 6 * y ^ 2 - 2 * z ^ 2 = 3 * t ^ 2 - 2 := by
  let k : ℚ := 3 * t ^ 2 - 2
  have hk : k ≠ 0 := target_ne_zero t
  obtain ⟨x, y, z, hp⟩ :=
    QuadraticForm.exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real
      (1 / 3) 2 (by norm_num) (by norm_num) (-(1 / 3) * k)
      (mul_ne_zero (by norm_num) hk)
      (fun v => by
        obtain ⟨x, y, z, h⟩ := hv v
        exact ⟨x, y, z, toPure (algebraMap ℚ (v.adicCompletion ℚ)) k x y z h⟩)
      (by
        obtain ⟨x, y, z, h⟩ := realRep (algebraMap ℚ ℝ k)
        exact ⟨x, y, z, toPure (algebraMap ℚ ℝ) k x y z h⟩)
  refine ⟨x, y, z, ?_⟩
  change x ^ 2 + 6 * y ^ 2 - 2 * z ^ 2 = k
  linear_combination (-3 : ℚ) * hp

/-- Restores the original unscaled ternary equation, for every nonzero scale. -/
theorem physical (scale f₀ f₁ : ℚ) (hs : scale ≠ 0)
    (hv : FiniteLocal ((f₀ ^ 2 + f₀ * f₁ - f₁ ^ 2) / scale)) :
    ∃ u v w : ℚ, u ^ 2 + 6 * v ^ 2 - 2 * w ^ 2 =
      3 * (f₀ ^ 2 + f₀ * f₁ - f₁ ^ 2) ^ 2 - 2 * scale ^ 2 := by
  obtain ⟨x, y, z, h⟩ := normalized _ hv
  refine ⟨scale * x, scale * y, scale * z, ?_⟩
  calc
    _ = scale ^ 2 * (x ^ 2 + 6 * y ^ 2 - 2 * z ^ 2) := by ring
    _ = _ := by rw [h]; field_simp [hs] <;> ring

/-- The actual G=4096 coefficient, with both rational components still free. -/
theorem literal4096 (f₀ f₁ : ℚ)
    (hv : FiniteLocal ((f₀ ^ 2 + f₀ * f₁ - f₁ ^ 2) / (3 : ℚ) ^ 4096)) :
    ∃ u v w : ℚ, u ^ 2 + 6 * v ^ 2 - 2 * w ^ 2 =
      3 * (f₀ ^ 2 + f₀ * f₁ - f₁ ^ 2) ^ 2 - 2 * ((3 : ℚ) ^ 4096) ^ 2 :=
  physical ((3 : ℚ) ^ 4096) f₀ f₁ (pow_ne_zero _ (by norm_num)) hv

end QuarticP02

#print axioms P2MW.S_QuadraticForm_exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real.solution
#print axioms QuadraticForm.exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real
#print axioms QuarticP02.target_ne_zero
#print axioms QuarticP02.normalized
#print axioms QuarticP02.physical
#print axioms QuarticP02.literal4096

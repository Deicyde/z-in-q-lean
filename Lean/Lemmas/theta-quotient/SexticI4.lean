import DirectCharts

/-! The weight-four Igusa–Clebsch invariant in ordinary binary coefficients.
The normalization is I₄ = −720 A² + 6750 B with normalized transvectants
A = (f,f)₆, q = (f,f)₄ and B = (q,q)₄. Coefficients are in ascending
order of the power of x in f(x,1), without binomial multipliers. -/
namespace ZInQBlueprint.SexticInvariants
open Polynomial ZInQBlueprint.DirectCharts
noncomputable section

def sexticA (a : ℕ → ℚ) : ℚ :=
  (120*a 0*a 6 - 20*a 1*a 5 + 8*a 2*a 4 - 3*(a 3)^2)/60

def quarticB (q₀ q₁ q₂ q₃ q₄ : ℚ) : ℚ := 2*q₀*q₄ - q₁*q₃/2 + q₂^2/6

def sexticB (a : ℕ → ℚ) : ℚ :=
  quarticB
    ((10*a 0*a 4-5*a 1*a 3+2*(a 2)^2)/75)
    (2*(25*a 0*a 5-5*a 1*a 4+a 2*a 3)/75)
    ((50*a 0*a 6-2*a 2*a 4+(a 3)^2)/25)
    (2*(25*a 1*a 6-5*a 2*a 5+a 3*a 4)/75)
    ((10*a 2*a 6-5*a 3*a 5+2*(a 4)^2)/75)

def igusaI4 (f : ℚ[X]) : ℚ := -720*(sexticA f.coeff)^2 + 6750*sexticB f.coeff

theorem igusaI4_C_mul (s : ℚ) (f : ℚ[X]) : igusaI4 (C s * f) = s^4*igusaI4 f := by
  simp only [igusaI4, sexticA, sexticB, quarticB, coeff_C_mul]
  ring

private theorem monic_coeff (t : ℚ) (n : ℕ) :
    (monicSextic t).coeff n =
      (if n=6 then 1 else 0) + (if n=5 then 9-t else 0) +
      (if n=4 then 27-9*t else 0) + (if n=3 then t^2-32*t+27 else 0) +
      (if n=2 then 6*t^2-54*t else 0) + (if n=1 then 12*t^2-36*t else 0) +
      (if n=0 then 8*t^2 else 0) := by
  rw [monic_coeffs]
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C]

private theorem coefficients (t : ℚ) :
    (monicSextic t).coeff 0 = 8*t^2 ∧ (monicSextic t).coeff 1 = 12*t^2-36*t ∧
    (monicSextic t).coeff 2 = 6*t^2-54*t ∧ (monicSextic t).coeff 3 = t^2-32*t+27 ∧
    (monicSextic t).coeff 4 = 27-9*t ∧ (monicSextic t).coeff 5 = 9-t ∧
    (monicSextic t).coeff 6 = 1 := by
  norm_num [monic_coeff]

private theorem familyA (t : ℚ) :
    sexticA (monicSextic t).coeff = -(t^2-8*t+27)*(t^2+8*t+27)/20 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := coefficients t
  rw [sexticA,h0,h1,h2,h3,h4,h5,h6]; ring

private theorem familyB (t : ℚ) :
    sexticB (monicSextic t).coeff =
      (t^8-100*t^6-2762*t^4-72900*t^2+531441)/3750 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := coefficients t
  rw [sexticB,h0,h1,h2,h3,h4,h5,h6,quarticB]; ring

theorem igusaI4_monic (t : ℚ) :
    igusaI4 (monicSextic t) = -144*t^2*(t^2+27)^2 := by
  rw [igusaI4,familyA,familyB]; ring

theorem igusaI4_family (s t : ℚ) :
    igusaI4 (C s * monicSextic t) = -144*s^4*t^2*(t^2+27)^2 := by
  rw [igusaI4_C_mul, igusaI4_monic]; ring

end
end ZInQBlueprint.SexticInvariants
#print axioms ZInQBlueprint.SexticInvariants.igusaI4_C_mul
#print axioms ZInQBlueprint.SexticInvariants.igusaI4_monic
#print axioms ZInQBlueprint.SexticInvariants.igusaI4_family

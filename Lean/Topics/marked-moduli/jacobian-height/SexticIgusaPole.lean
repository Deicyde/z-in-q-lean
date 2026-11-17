import FixedBranch

/-! Liu's degree-two and degree-ten Igusa invariants on the actual rational paper curve. -/
namespace ZInQBlueprint.JacobianHeight
open Polynomial DirectCharts SexticInvariants SexticIgusaChart SexticThetaHeight BinaryCover
noncomputable section

/-- Liu, §2, p. 139, on a degree-six equation. The factor −15 converts the
normalized sixth transvectant to J₂ with the coefficients in ordinary powers. -/
def igusaJ2 (f : ℚ[X]) : ℚ := -15 * sexticA f.coeff

/-- Liu, §2, p. 140, on the degree-six chart. -/
def igusaJ10 (f : ℚ[X]) : ℚ := f.discr / 4096

theorem liu_quadratic (f : ℚ[X]) : igusaJ2 f =
    (-120*f.coeff 0*f.coeff 6 + 20*f.coeff 1*f.coeff 5 - 8*f.coeff 2*f.coeff 4 + 3*(f.coeff 3)^2)/4 := by
  unfold igusaJ2 sexticA
  ring

theorem igusaJ2_family (s t : ℚ) :
    igusaJ2 (C s * monicSextic t) = 3*s^2*((t^2+27)^2-64*t^2)/4 := by
  rw [liu_quadratic, monic_coeffs]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num
  ring

/-- The absolute invariant used at all primes p > 3, computed directly from the sextic
coefficients. The calculation also proves that its denominator J₂ does not vanish. -/
theorem sextic_igusa_quotient {u : ℚ} (hu : u ∉ ZInQ.contactSet) (s : ℚ) (hs : s ≠ 0) :
    let f := C s * monicSextic (parameter u)
    igusaJ2 f ≠ 0 ∧ igusaJ10 f / (igusaJ2 f)^5 =
      (SixContact.J u)^3 / (12*(SixContact.J u + 1))^5 := by
  let t := parameter u
  have ht : t^2+27 ≠ 0 := by nlinarith [sq_nonneg t]
  have hJ := (unmarked (δ := 1) hu one_ne_zero).2.2.2
  change SixContact.J u = -64*t^2/(t^2+27)^2 at hJ
  have he : (SixContact.J u + 1)*(t^2+27)^2 = (t^2+27)^2 - 64*t^2 := by
    rw [hJ]
    field_simp [ht]
    ring
  have hn : SixContact.J u + 1 ≠ 0 := by linarith [(CoarseConic.unmarked_range hu).1]
  have h2 : igusaJ2 (C s * monicSextic t) = 3*s^2*(SixContact.J u+1)*(t^2+27)^2/4 := by
    rw [igusaJ2_family, ← he]; ring
  change igusaJ2 (C s * monicSextic t) ≠ 0 ∧ _
  constructor
  · rw [h2]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hs)) hn) (pow_ne_zero 2 ht)) (by norm_num)
  · change (C s * monicSextic t).discr / 4096 / (igusaJ2 (C s * monicSextic t))^5 = _
    rw [h2, discr_family _ _ hs]
    conv_rhs => rw [show (SixContact.J u)^3 = (-64*t^2/(t^2+27)^2)^3 from congrArg (· ^ 3) hJ]
    field_simp [hs, hn, ht]
    ring

/-- Exact absolute invariant of the chosen good-reduction twist on its named rational chart. -/
theorem paper_igusa_quotient {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    let f := paper ℚ u false
    igusaJ2 f ≠ 0 ∧ igusaJ10 f / (igusaJ2 f)^5 =
      (SixContact.J u)^3 / (12*(SixContact.J u + 1))^5 := by
  have hd : (GlobalTwist.delta u : ℚ) ≠ 0 := by exact_mod_cast (GlobalTwist.delta_pos u).ne'
  have hs := (unmarked hu hd).2.1
  dsimp only
  rw [paper_affine_eq_sextic hu, sextic, ← map_pow, ← mul_assoc, ← C_mul]
  exact sextic_igusa_quotient hu _ (mul_ne_zero (pow_ne_zero 2 (CurveChart.yScale_ne hu)) hs)

end
end ZInQBlueprint.JacobianHeight
#print axioms ZInQBlueprint.JacobianHeight.liu_quadratic
#print axioms ZInQBlueprint.JacobianHeight.igusaJ2_family
#print axioms ZInQBlueprint.JacobianHeight.sextic_igusa_quotient
#print axioms ZInQBlueprint.JacobianHeight.paper_igusa_quotient

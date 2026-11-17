import QualitativeHeight
import ZInQKernel.Hypotheses.JHeight

/-! The rational moduli function for the Picard sextic factors through the
degree-twelve coordinate used in the six-contact estimate. -/

namespace ZOverQ.Qualitative.Picard

open ZInQ ZInQ.QualitativeHeight

variable {K : Type*} [Field K] [CharZero K]

def coefficients (U V : K) : Fin 7 → K :=
  ![8*U, -24*U, 12*U, 8*U+8*V, -6*V, -6*V, -V]

omit [CharZero K] in
theorem sextic_eq (U V x : K) :
    (∑ i : Fin 7, coefficients U V i * x^(i : ℕ)) =
      (x^2 + 2*x - 2) * (4*U*(2*x - 1) - V*x^3*(x+4)) := by
  simp [Fin.sum_univ_succ, coefficients]
  ring

/-- The sixth transvectant of the binary sextic with itself in the
ordinary coefficient convention, with the common binomial normalization. -/
def secondInvariant (a : Fin 7 → K) : K :=
  2*a 0*a 6 - a 1*a 5/3 + 2*a 2*a 4/15 - (a 3)^2/20

theorem secondInvariant_eq (U V : K) :
    secondInvariant (coefficients U V) = -16*(U^2 + 25*U*V + V^2)/5 := by
  simp [secondInvariant, coefficients]
  ring

/-- The value of the sextic discriminant computed in the accompanying Magma program. -/
def discriminantValue (U V : K) : K := -(2:K)^22 * 3^6 * U^2 * V^2 * (U-V)^6

def ratio (U V : K) : K := (secondInvariant (coefficients U V))^5 / discriminantValue U V

private theorem ratio_factor (U V : K) (hU : U ≠ 0) (hV : V ≠ 0) (hD : U-V ≠ 0) :
    ratio U V = (((U-V)^2 / (U*V)) + 27)^5 / (9112500 * ((U-V)^2 / (U*V))^3) := by
  rw [ratio, secondInvariant_eq, discriminantValue]
  field_simp [hU, hV, hD]
  ring

omit [CharZero K] in
theorem sixth_difference (s ρ : K) (hρ : ρ^2 = -3) :
    (s+ρ)^6 - (s-ρ)^6 = 12*ρ*(s*(s-1)*(s+1)*(s-3)*(s+3)) := by
  linear_combination (40*s^3*ρ + 12*s*ρ*(ρ^2-3))*hρ

omit [CharZero K] in
theorem sixth_product (s ρ : K) (hρ : ρ^2 = -3) :
    (s+ρ)^6 * (s-ρ)^6 = (s^2+3)^6 := by
  rw [← mul_pow]
  congr 1
  linear_combination -hρ

private theorem norm_change {t : ℚ} (ht : t ≠ 0) :
    (picardParameter t)^2 + 3 = 4 * (7*t^2 + 300*t + 3600)/t^2 := by
  unfold picardParameter
  field_simp
  ring

theorem rational_shape {t : ℚ} (ht : t ≠ 0) :
    -432*(branchForm (picardParameter t) 1)^2 / ((picardParameter t)^2+3)^6 =
      (27/4)*JHeight.Jmap t := by
  have hb := branchForm_change ht 1
  simp only [mul_one] at hb
  rw [hb, norm_change ht, JHeight.Jmap, Mult.contactPoly]
  field_simp [ht, JHeight.G_ne_zero t]
  ring

/-- The moduli invariant of the sextic at the rational parameter `t`, as a
rational function of Glazer's coordinate. The equality is over any field of
characteristic zero containing a square root of `-3`. -/
theorem ratio_at (ρ : K) (hρ : ρ^2 = -3) {t : ℚ} (ht : t ∉ contactSet) :
    let s := (picardParameter t : K)
    ratio ((s+ρ)^6) ((s-ρ)^6) =
      (((JHeight.Jmap t + 4)^5 / (200000*(JHeight.Jmap t)^3) : ℚ) : K) := by
  dsimp only
  let s := (picardParameter t : K)
  let U := (s+ρ)^6
  let V := (s-ρ)^6
  have ht0 : t ≠ 0 := by intro h; apply ht; rw [h]; decide
  have hprod : U*V = (s^2+3)^6 := sixth_product _ _ hρ
  have hnq : (picardParameter t)^2 + 3 ≠ 0 := by positivity
  have hn : s^2+3 ≠ 0 := by
    have hh : (((picardParameter t)^2+3 : ℚ) : K) ≠ 0 := Rat.cast_ne_zero.mpr hnq
    push_cast at hh
    exact hh
  have huv : U*V ≠ 0 := hprod ▸ pow_ne_zero _ hn
  have hd : U-V = 12*ρ*((branchForm (picardParameter t) 1 : ℚ) : K) := by
    rw [show U-V = _ from sixth_difference s ρ hρ]
    simp [branchForm, s]
  have hshape : (U-V)^2/(U*V) = (27/4:K)*(JHeight.Jmap t : K) := by
    rw [hprod, hd]
    have hsq : (12*ρ*((branchForm (picardParameter t) 1 : ℚ) : K))^2 =
        -432*((branchForm (picardParameter t) 1 : ℚ) : K)^2 := by
      linear_combination 144*((branchForm (picardParameter t) 1 : ℚ) : K)^2*hρ
    rw [hsq]
    have hh := congrArg (fun x : ℚ => (x : K)) (rational_shape ht0)
    push_cast at hh
    exact hh
  have hjq : JHeight.Jmap t ≠ 0 := by
    change -57600 * (Mult.contactPoly t)^2 / _ ≠ 0
    exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (Mult.contactPoly_ne_zero ht)))
      (pow_ne_zero _ (JHeight.G_ne_zero t))
  have hj : (JHeight.Jmap t : K) ≠ 0 := by exact_mod_cast hjq
  have hD : U-V ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by decide), zero_div] at hshape
    exact (mul_ne_zero (by norm_num) hj) hshape.symm
  change ratio U V = _
  rw [ratio_factor _ _ (left_ne_zero_of_mul huv) (right_ne_zero_of_mul huv) hD, hshape]
  push_cast
  field_simp
  ring

end ZOverQ.Qualitative.Picard

#print axioms ZOverQ.Qualitative.Picard.sextic_eq
#print axioms ZOverQ.Qualitative.Picard.secondInvariant_eq
#print axioms ZOverQ.Qualitative.Picard.ratio_at

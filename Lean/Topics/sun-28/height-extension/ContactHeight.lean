import ScaledPencil
import NumericBound

namespace Sun28.HeightExtension
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightFibres Sun28.HeightFibres.Sharp Height ZInQ.RouteK
open private leftRow midRow from FivePencils
open private numberLog_le from PellSectors
noncomputable section
set_option maxRecDepth 8192
set_option exponentiation.threshold 1500

private theorem int_height {z:ℤ} (nz:z≠0) : logHeight₁ (z:ℚ)=numberLog z := by
  rw [Rat.logHeight₁_eq_log_max]
  change Real.log ((max z.natAbs 1:ℕ):ℝ)=Real.log (z.natAbs:ℝ)
  rw [max_eq_left (show 1≤z.natAbs from Int.natAbs_pos.mpr nz)]

private theorem height_div (x y : ℚ) : logHeight₁ (x/y)≤logHeight₁ x+logHeight₁ y := by
  simpa only [div_eq_mul_inv,logHeight₁_inv] using logHeight₁_mul_le x y⁻¹

private theorem det_log {i j:Fin 5} (diff:i≠j) : logHeight₁ ((det i j:ℤ):ℚ)≤32 := by
  rw [int_height (det_ne diff)]
  have fixed : ∀ i j : Fin 5,(det i j).natAbs≤2^32:=by decide
  have h:=numberLog_le (det_ne diff) (show ((det i j).natAbs:ℝ)≤2^32 by exact_mod_cast fixed i j)
  rw [Real.log_pow] at h
  norm_num at h
  linarith only [h,Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)]

/-- Bound the full primitive slope from the single rational Pell coordinate
using the actual ratio of the two rows. -/
theorem slope_from_coordinate {A B : ℤ} (cop:Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0)
    (i : Fin 5) (x : ℚ) (ratio : (oldForm (leftRow i) A B:ℚ)/(oldForm i A B:ℚ)=
        (kernel (leftRow i) A B:ℚ)/(kernel i A B:ℚ)*x^2) :
    pairLogHeight A B≤2*logHeight₁ x+2*Real.log (heightRadical A B:ℝ)+96 := by
  let l:=leftRow i
  let j:=midRow i
  have cat : ∀ i:Fin 5,leftRow i≠midRow i ∧ leftRow i≠i ∧ midRow i≠i:=by decide
  have ⟨lj,li,ji⟩:=cat i
  have base:=crossRatio_height l j i lj li ji cop off
  have nz (k : Fin 5):kernel k A B≠0:=(sqfInt_spec (off k)).1.ne_zero
  have coeff (k : Fin 5) : logHeight₁ ((kernel k A B:ℤ):ℚ)≤Real.log (heightRadical A B:ℝ):=by
    rw [int_height (nz k)];exact numberLog_le (nz k) (Nat.cast_le.mpr (kernel_bound off k))
  let c:ℚ:=(det i j:ℚ)/(det l j:ℚ)
  let d:ℚ:=(kernel l A B:ℚ)/(kernel i A B:ℚ)
  have frac : crossRatio l j i A B=c*(d*x^2) := by
    change (oldForm l A B:ℚ)/(oldForm i A B:ℚ)=d*x^2 at ratio
    rw [←ratio]
    unfold crossRatio c
    push_cast
    ring
  have den:=height_div (det i j:ℚ) (det l j:ℚ)
  change logHeight₁ c≤_ at den
  have dd:=height_div (kernel l A B:ℚ) (kernel i A B:ℚ)
  change logHeight₁ d≤_ at dd
  have qr:=logHeight₁_mul_le c (d*x^2)
  have xx:=logHeight₁_mul_le d (x^2)
  rw [logHeight₁_pow] at xx
  rw [frac] at base
  norm_num at xx
  linarith only [base,qr,xx,den,dd,coeff l,coeff i,det_log ji.symm,det_log lj]

end
end Sun28.HeightExtension
#print axioms Sun28.HeightExtension.slope_from_coordinate

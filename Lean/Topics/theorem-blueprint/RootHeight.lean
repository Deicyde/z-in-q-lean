import HeightSix
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Localization.Rat
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Rational roots of the six-contact fibre pencil. -/
namespace ZInQBlueprint.SixContact
open Polynomial

private noncomputable def denominatorPower : ℕ[X] := (7*X^2+300*X+3600)^6
private noncomputable def numeratorSquare : ℕ[X] := 57600*(X*(X+15)*(X+20)*(X+24)*(X+30)*(X+60))^2
/-- The integer equation of the fibre of J above the reduced fraction j. -/
private noncomputable def fibre (j : ℚ) : ℤ[X] :=
  C j.num * denominatorPower.map (Nat.castRingHom ℤ) + C (j.den:ℤ) * numeratorSquare.map (Nat.castRingHom ℤ)
private def rationalSize (x : ℚ) : ℕ := max x.num.natAbs x.den

private lemma coeff_le_eval_one (p : ℕ[X]) (k : ℕ) : p.coeff k ≤ p.eval 1 := by
  classical
  by_cases h : k ∈ p.support
  · rw [eval_eq_sum, sum_def]
    simp only [one_pow, mul_one]
    exact Finset.single_le_sum (f := p.coeff) (fun _ _ => Nat.zero_le _) h
  · simp [notMem_support_iff.mp h]

private lemma fibre_coeff (j : ℚ) (k : ℕ) : (fibre j).coeff k =
    j.num * (denominatorPower.coeff k : ℤ) + (j.den:ℤ) * (numeratorSquare.coeff k : ℤ) := by
  simp [fibre, coeff_map]

private lemma coefficient_sum :
    denominatorPower.eval 1 + numeratorSquare.eval 1 = 3571341665779557551449 := by
  norm_num [denominatorPower,numeratorSquare]

private lemma coeff_bound (j : ℚ) (k : ℕ) :
    ((fibre j).coeff k).natAbs ≤ rationalSize j * 2^72 := by
  rw [fibre_coeff]
  calc
    _ ≤ (j.num*(denominatorPower.coeff k:ℤ)).natAbs + ((j.den:ℤ)*(numeratorSquare.coeff k:ℤ)).natAbs :=
      Int.natAbs_add_le ..
    _ = j.num.natAbs * denominatorPower.coeff k + j.den * numeratorSquare.coeff k := by simp [Int.natAbs_mul]
    _ ≤ rationalSize j * denominatorPower.eval 1 + rationalSize j * numeratorSquare.eval 1 :=
      Nat.add_le_add (Nat.mul_le_mul (le_max_left ..) (coeff_le_eval_one denominatorPower k))
        (Nat.mul_le_mul (le_max_right ..) (coeff_le_eval_one numeratorSquare k))
    _ = rationalSize j * (denominatorPower.eval 1 + numeratorSquare.eval 1) := (Nat.mul_add ..).symm
    _ ≤ _ := Nat.mul_le_mul_left _ (by rw [coefficient_sum]; decide)

private lemma constant_nonzero {j : ℚ} (hj : j ≠ 0) : (fibre j).coeff 0 ≠ 0 := by
  rw [fibre_coeff, coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero]
  norm_num [denominatorPower,numeratorSquare,Rat.num_ne_zero.mpr hj]

private lemma is_root (u : ℚ) : aeval u (fibre (J u)) = 0 := by
  have hnum : ((J u).num : ℚ) = J u * (J u).den :=
    (div_eq_iff (by exact_mod_cast (J u).den_ne_zero)).mp (J u).num_div_den
  have ha : aeval u (denominatorPower.map (Nat.castRingHom ℤ)) = (G u)^6 := by norm_num [denominatorPower,G,map_ofNat]
  have hb : aeval u (numeratorSquare.map (Nat.castRingHom ℤ)) = 57600*(F u)^2 := by norm_num [numeratorSquare,F,map_ofNat]
  simp only [fibre, map_add, map_mul, aeval_C, ha, hb]
  change ((J u).num:ℚ) * G u ^ 6 + ((J u).den:ℚ)*(57600 * F u ^ 2) = 0
  rw [hnum]
  unfold J
  field_simp [(positive_denominator u).ne']
  ring

/-- Apply the rational root theorem to the actual leading coefficient. Its degree may drop. -/
private lemma size_bound_nonzero {u : ℚ} (hj : J u ≠ 0) :
    rationalSize u ≤ rationalSize (J u) * 2^72 := by
  let p := fibre (J u)
  have hc : p.coeff 0 ≠ 0 := constant_nonzero hj
  have hp : p ≠ 0 := by intro eqn; exact hc (by simp [eqn])
  have hr : aeval u p = 0 := is_root u
  have nu := (u.associated_num_den.1.dvd_iff_dvd_left).mp (num_dvd_of_is_root hr)
  have de := (u.associated_num_den.2.dvd_iff_dvd_left).mp (den_dvd_of_is_root hr)
  have hnum : u.num.natAbs ∣ (p.coeff 0).natAbs := Int.natAbs_dvd_natAbs.mpr nu
  have hden : u.den ∣ p.leadingCoeff.natAbs := by simpa using (Int.natAbs_dvd_natAbs.mpr de)
  apply max_le
  · exact (Nat.le_of_dvd (by omega : 0 < (p.coeff 0).natAbs) hnum).trans (coeff_bound _ 0)
  · have hl : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
    exact (Nat.le_of_dvd (by omega : 0 < p.leadingCoeff.natAbs) hden).trans (coeff_bound _ p.natDegree)

/-- Above j = 0 the six marks themselves are the only roots. -/
private lemma zero_branch {u : ℚ} (hj : J u = 0) : rationalSize u ≤ rationalSize (J u)*2^72 := by
  have hf : F u = 0 := by simpa [J,(positive_denominator u).ne'] using hj
  rw [hj]
  simp only [F, mul_eq_zero] at hf
  rcases hf with (((((h|h)|h)|h)|h)|h) <;>
    first | subst u; norm_num [rationalSize] | obtain rfl : u = _ := eq_neg_of_add_eq_zero_left h; norm_num [rationalSize]

/-- A logarithmic height bound at every rational fibre root, including the marked roots. -/
theorem root_height (u : ℚ) : ratHeight u ≤ ratHeight (J u) + 50 := by
  have size_pos (x : ℚ) : 0 < rationalSize x := lt_of_lt_of_le x.den_pos (le_max_right ..)
  have hsize : rationalSize u ≤ rationalSize (J u) * 2^72 := by
    by_cases hj : J u = 0
    · exact zero_branch hj
    · exact size_bound_nonzero hj
  have height_eq (x : ℚ) : ratHeight x = Real.log (rationalSize x) := by simp [ratHeight,rationalSize]
  rw [height_eq, height_eq]
  calc
    Real.log (rationalSize u) ≤ Real.log ((rationalSize (J u):ℝ)*2^72) :=
      Real.log_le_log (by exact_mod_cast size_pos u) (by exact_mod_cast hsize)
    _ = Real.log (rationalSize (J u)) + 72*Real.log 2 := by
      rw [Real.log_mul (by exact_mod_cast (size_pos (J u)).ne') (by norm_num), Real.log_pow]
      norm_num
    _ ≤ _ := by linarith [Real.log_two_lt_d9]

theorem fibre_root_bound (u : ℚ) : ratHeight u ≤ ratHeight (J u) + 74 := by
  linarith [root_height u]

/-- The six-contact estimate now needs only the three geometric height inequalities. -/
theorem contact_bound_of_heights {u : ℚ} {S : Finset ℕ} {B stable theta : ℝ}
    (igusa : ratHeight (J u) ≤ 40*theta + 22)
    (theta_bound : theta ≤ (10000*2^24)*max 1 stable)
    (conductor : max 1 stable ≤ B*(support S u : ℝ)^24) :
    ratHeight u ≤ (2*10^13*B)*(support S u : ℝ)^24 :=
  contact_bound ⟨stable, theta, fibre_root_bound u, igusa, theta_bound, conductor⟩

#print axioms contact_bound_of_heights
#print axioms root_height
#print axioms fibre_root_bound
end ZInQBlueprint.SixContact

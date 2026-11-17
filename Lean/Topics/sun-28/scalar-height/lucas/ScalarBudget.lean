import ScalarLucas

namespace Sun28.ScalarLucas
open Height Sun28.Ordinary Sun28.FixedPreparation Sun28.WitnessHeight Sun28.ScalarHeight Sun28.FiveMarkUnits
noncomputable section

def radical (x : ℚ) : ℕ := primeProduct (scalarPrimes x)
theorem radical_pos (x : ℚ) : 0 < radical x := by
  unfold radical primeProduct
  apply Finset.prod_pos
  intro p hp
  exact (Nat.mem_primeFactors.mp (Finset.mem_sdiff.mp hp).1).1.pos

def stepFloor (x : ℚ) : ℕ := fixedMultiplier.lcm ((radical x)^48)

/-- A scalar certificate forces c to be a multiple of this integer. -/
theorem stepFloor_dvd (x : ℚ) {n : Fin 4 → ℤ} {q : ℤ}
    (anchorEq : n 1-1=(fixedMultiplier:ℤ)*q)
    (support : (oldRadical oldCutoff (beta x):ℤ)^48 ∣ n 1-1) :
    stepFloor x ∣ scalarStep n := by
  have first : fixedMultiplier ∣ scalarStep n := by
    refine ⟨q.natAbs,?_⟩
    simp only [scalarStep,anchorEq,Int.natAbs_mul,Int.natAbs_natCast]
  have eqR : oldRadical oldCutoff (beta x)=radical x := by
    unfold oldRadical radical primeProduct
    rw [scalar_support_exact]
  have second := Int.natAbs_dvd_natAbs.mpr support
  rw [eqR] at second
  apply Nat.lcm_dvd first
  simpa only [Int.natAbs_pow,Int.natAbs_natCast,scalarStep] using second

theorem stepFloor_bounds (x : ℚ) :
    fixedMultiplier ≤ stepFloor x ∧ (radical x)^48 ≤ stepFloor x := by
  have pos := radical_pos x
  have nonzero : 0<stepFloor x  := by
    unfold stepFloor
    exact Nat.lcm_pos (lt_of_lt_of_le (by decide : 0<8) fixed_multiplier_spec.2.1) (pow_pos pos _)
  exact ⟨Nat.le_of_dvd nonzero (Nat.dvd_lcm_left ..),Nat.le_of_dvd nonzero (Nat.dvd_lcm_right ..)⟩

theorem fixed_reserve : 12 ≤ fixedMultiplier ∧ 8*|logConstant| < (fixedMultiplier:ℝ) ∧
    216*glazerConstant24^2 < (fixedMultiplier:ℝ) := by
  obtain ⟨h,k,j⟩ := multiplier_reserve ordinary logConstant glazerConstant24
  change 36*glazerConstant24^2*6 < (fixedMultiplier:ℝ) at j
  exact ⟨h,k,by linarith only [j]⟩

theorem log_one_of_floor {u : ℝ} (hu : 12 ≤ u) : 1 ≤ Real.log u := by
  have cmp := Real.log_le_log (by norm_num : 0<(4:ℝ)) (show (4:ℝ)≤u by linarith)
  have le := Real.log_two_gt_d9
  rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, Real.log_pow] at cmp
  norm_num at cmp
  linarith

/-- This is a sufficient upper bound on h(β). It is a function of x alone. -/
def scalarAllowance (x : ℚ) : ℝ := (stepFloor x:ℝ)*Real.log (stepFloor x:ℝ)/24

theorem allowance_comparison (x : ℚ) {c : ℕ} (floorLe : stepFloor x ≤ c) :
    logConstant + 3*scalarAllowance x < ((c:ℝ)/4)*Real.log (c:ℝ) := by
  have f := stepFloor_bounds x
  have fr := fixed_reserve
  have hu : (12:ℝ)≤(stepFloor x:ℝ) := by exact_mod_cast fr.1.trans f.1
  have v : (stepFloor x:ℝ) ≤ c := by exact_mod_cast floorLe
  have small := log_one_of_floor hu
  have pos : (0:ℝ)<stepFloor x := by linarith
  have monot := Real.log_le_log pos v
  have a : (stepFloor x:ℝ) ≤ (stepFloor x:ℝ)*Real.log (stepFloor x:ℝ) := by
    simpa using mul_le_mul_of_nonneg_left small pos.le
  have mul := mul_le_mul v monot (by linarith : 0≤Real.log (stepFloor x:ℝ)) (by positivity : 0≤(c:ℝ))
  have k := le_abs_self logConstant
  have f1 : (fixedMultiplier:ℝ) ≤ (stepFloor x:ℝ) := by exact_mod_cast f.1
  unfold scalarAllowance
  linarith only [fr.2.1,k,a,mul,f1]

/-- The former H_* R^24 bound always fits inside the new allowance. -/
theorem original_fits (x : ℚ) :
    glazerConstant24*(radical x:ℝ)^24 ≤ scalarAllowance x := by
  have f := stepFloor_bounds x
  have fr := fixed_reserve
  let L : ℝ := stepFloor x
  let S := glazerConstant24
  let u : ℝ := (radical x:ℝ)^24
  have f1 : (fixedMultiplier:ℝ) ≤ L := by dsimp only [L]; exact_mod_cast f.1
  have f2 : u^2 ≤ L := by
    dsimp [u,L]
    rw [←pow_mul]
    exact_mod_cast f.2
  have s2 : 144*S^2 ≤ L := by nlinarith only [fr.2.2,f1,sq_nonneg S]
  have twoSu : 24*S*u ≤ 2*L := by nlinarith only [sq_nonneg (12*S-u),s2,f2]
  have min12 : (12:ℝ) ≤ L := by dsimp only [L]; exact_mod_cast fr.1.trans f.1
  have logs : 2 ≤ Real.log L := by
    have cmp := Real.log_le_log (by norm_num : 0<(8:ℝ)) (show (8:ℝ)≤L by linarith)
    rw [show (8:ℝ)=(2:ℝ)^3 by norm_num,Real.log_pow] at cmp
    norm_num at cmp
    linarith [Real.log_two_gt_d9]
  have pl : (0:ℝ)≤L := by linarith
  have up := mul_le_mul_of_nonneg_left logs pl
  change S*u ≤ L*Real.log L/24
  linarith only [twoSu,up]

/-- A second, independent sufficient target with twice the exponent and a logarithmic factor. -/
theorem high_power_fits (x : ℚ) :
    2*(radical x:ℝ)^48*Real.log (radical x:ℝ) ≤ scalarAllowance x := by
  let r : ℝ := radical x
  let L : ℝ := stepFloor x
  have f := stepFloor_bounds x
  have rp : 1 ≤ r := by
    dsimp only [r]
    exact Nat.one_le_cast.mpr (radical_pos x)
  have pos : 0 < r := zero_lt_one.trans_le rp
  have bound : r^48 ≤ L := by dsimp only [r,L]; exact_mod_cast f.2
  have mono := mul_le_mul bound (Real.log_le_log (pow_pos pos 48) bound)
    (Real.log_nonneg (one_le_pow₀ rp)) (show 0≤L from (pow_pos pos 48).le.trans bound)
  rw [Real.log_pow] at mono
  norm_num1 at mono
  change 2*r^48*Real.log r ≤ L*Real.log L/24
  linarith only [mono]

end
end Sun28.ScalarLucas
#print axioms Sun28.ScalarLucas.radical_pos
#print axioms Sun28.ScalarLucas.stepFloor_dvd
#print axioms Sun28.ScalarLucas.stepFloor_bounds
#print axioms Sun28.ScalarLucas.fixed_reserve
#print axioms Sun28.ScalarLucas.log_one_of_floor
#print axioms Sun28.ScalarLucas.allowance_comparison
#print axioms Sun28.ScalarLucas.original_fits
#print axioms Sun28.ScalarLucas.high_power_fits

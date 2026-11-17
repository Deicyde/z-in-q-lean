import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Recover the original slope from the better integral pencil. -/
namespace ZInQBlueprint.IntegralSections
open Height
noncomputable section

/-- The ratio of the chosen sections at an off-mark rational slope. -/
def pencilRatio (s : ℚ) := 75*s/(32*s+343)

private theorem reduced_bound (y : ℚ) (n m : ℤ) (hm : m≠0)
    (rep : y=Rat.divInt n m) : max |y.num| (y.den:ℤ) ≤ max |n| |m| := by
  obtain ⟨c,hn,hd⟩ := Rat.num_den_mk hm rep
  have hc : c≠0 := by intro zero; simp [zero,hm] at hd
  have ab : 1 ≤ |c| := by have pos := abs_pos.mpr hc; omega
  have n' : |y.num|≤|n| := by
    rw [hn,abs_mul]
    simpa using mul_le_mul_of_nonneg_right ab (abs_nonneg y.num)
  have m' : (y.den:ℤ)≤|m| := by
    rw [hd,abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
    simpa using mul_le_mul_of_nonneg_right ab (Int.natCast_nonneg y.den)
  exact max_le_max n' m'

/-- The inverse pencil has integral adjugate with largest row sum 343. -/
theorem ratio_height (s : ℚ) (off : 32*s+343 ≠ 0) :
    logHeight₁ s ≤ logHeight₁ (pencilRatio s)+Real.log 343 := by
  let y:=pencilRatio s
  let u:=y.num
  let v:ℤ:=y.den
  have vn : v≠0 := by dsimp [v]; exact_mod_cast y.den_nz
  have cross : (u:ℚ)*(32*s+343)=75*s*(v:ℚ) := by
    apply (div_eq_div_iff (by exact_mod_cast vn) off).mp
    simpa only [u,v,Int.cast_natCast,y,pencilRatio] using Rat.num_div_den y
  have mn : 75*v-32*u≠0 := by
    intro h
    have hh : 75*(v:ℚ)-32*(u:ℚ)=0 := by exact_mod_cast h
    have un : (u:ℚ)=0 := by linear_combination (1/343:ℚ)*cross + (s/343)*hh
    have vz : (v:ℚ)=0 := by linarith only [hh,un]
    exact vn (by exact_mod_cast vz)
  have eqn : s=Rat.divInt (343*u) (75*v-32*u) := by
    rw [Rat.divInt_eq_div]
    apply (eq_div_iff (by exact_mod_cast mn)).2
    push_cast
    linear_combination -cross
  have h:=reduced_bound s (343*u) (75*v-32*u) mn eqn
  let H:=max |u| |v|
  have hu : |u|≤H:=le_max_left _ _
  have hv : |v|≤H:=le_max_right _ _
  have Hp : 0≤H:=(abs_nonneg u).trans hu
  have bounds : max |343*u| |75*v-32*u| ≤ 343*H := by
    apply max_le
    · rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℤ)≤343)];omega
    · have a:=abs_sub (75*v) (32*u)
      rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℤ)≤75),
        abs_of_nonneg (by norm_num : (0:ℤ)≤32)] at a
      omega
  have hi:=h.trans bounds
  have hpos (x : ℚ) : 0 < (max x.num.natAbs x.den:ℝ) := by
    exact lt_of_lt_of_le (by exact_mod_cast x.den_pos) (le_max_right _ _)
  have hr : (max s.num.natAbs s.den:ℝ) ≤ 343*(max y.num.natAbs y.den:ℝ) := by
    dsimp [H,u,v] at hi
    rw [abs_of_nonneg (Int.natCast_nonneg y.den)] at hi
    exact_mod_cast (show (max s.num.natAbs s.den:ℕ) ≤ 343*(max y.num.natAbs y.den:ℕ) from
      by exact_mod_cast (show (max s.num.natAbs s.den:ℤ) ≤ 343*(max y.num.natAbs y.den:ℤ) by
        simpa using hi))
  have logs:=Real.log_le_log (hpos s) hr
  rw [Real.log_mul (by norm_num) (hpos y).ne'] at logs
  rw [Rat.logHeight₁_eq_log_max,Rat.logHeight₁_eq_log_max]
  push_cast
  linarith only [logs]

theorem comparison_constant :
    2*Real.log Real.pi+Real.log 210+Real.log (8192*75)+Real.log 343 < 27 := by
  have ident : 2*Real.log Real.pi+Real.log 210+Real.log (8192*75)+Real.log 343 =
      Real.log (Real.pi^2*210*(8192*75)*343) := by
    conv_rhs => rw [Real.log_mul (by positivity) (by norm_num),Real.log_mul (by positivity) (by norm_num),
      Real.log_mul (by positivity) (by norm_num),Real.log_pow]
    norm_num
  rw [ident,Real.log_lt_iff_lt_exp (by positivity)]
  have pi := Real.pi_lt_d2
  have pib : Real.pi^2 ≤ (3.15:ℝ)^2 :=
    pow_le_pow_left₀ Real.pi_pos.le pi.le 2
  have exp := Real.exp_one_gt_d9
  have expb := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2.7)
    (by linarith only [exp] : (2.7:ℝ)≤Real.exp 1) 27
  rw [← Real.exp_nat_mul] at expb
  norm_num at expb ⊢
  linarith only [expb,pib]

/-- Input from the integral Shimura pencil evaluation, with its precise norm and height
normalizations; the preceding facts recover the original slope's comparison. -/
theorem height_from_pencil (s : ℚ) (off : 32*s+343 ≠ 0) (h : ℝ)
    (evaluation : logHeight₁ (pencilRatio s) ≤ 2*h+2*Real.log Real.pi+
      Real.log 210+Real.log (8192*75)) : logHeight₁ s < 2*h+27 := by
  linarith only [ratio_height s off,evaluation,comparison_constant]
end
end ZInQBlueprint.IntegralSections
#print axioms ZInQBlueprint.IntegralSections.ratio_height
#print axioms ZInQBlueprint.IntegralSections.comparison_constant
#print axioms ZInQBlueprint.IntegralSections.height_from_pencil

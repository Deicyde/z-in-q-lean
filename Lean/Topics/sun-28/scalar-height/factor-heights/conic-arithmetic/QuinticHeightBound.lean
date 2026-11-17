import OddModels
import ProjectiveHeight

open private proportional from ProjectiveHeight
namespace Sun28.ConicArithmetic
open Height Sun28.Ordinary
noncomputable section

private theorem lin (i j a b:ℤ) : |i*a+j*b|≤(|i|+|j|)*pairHeight a b := by
  calc
    _ ≤ |i*a|+|j*b| := abs_add_le _ _
    _ ≤ |i| *pairHeight a b+|j| *pairHeight a b := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left ..) (abs_nonneg i))
        (mul_le_mul_of_nonneg_left (le_max_right ..) (abs_nonneg j))
    _ = _ := (add_mul ..).symm

private theorem homogeneous_height (pos:Bool) (a b:ℤ) :
    pairHeight (num pos a b) (den pos a b) ≤ 31213*(pairHeight a b)^2 := by
  let H:=pairHeight a b
  have ha:0≤H:=(abs_nonneg a).trans (le_max_left ..)
  have hb:|b|≤H:=le_max_right ..
  have ab:|2*a-b|≤3*H:=by simpa [H,sub_eq_add_neg] using lin 2 (-1) a b
  have ab':|a-4*b|≤5*H:=by simpa [H,sub_eq_add_neg] using lin 1 (-4) a b
  have cd:|5*a+8*b|≤13*H:=by simpa [H] using lin 5 8 a b
  have cd':|5*a+b|≤6*H:=by simpa [H] using lin 5 1 a b
  have posnum:=pow_le_pow_left₀ (abs_nonneg _) ab 2
  have negden:=pow_le_pow_left₀ (abs_nonneg _) cd' 2
  have posden:=mul_le_mul ab' hb (abs_nonneg b) (by linarith:0≤5*H)
  have negnum:=mul_le_mul cd hb (abs_nonneg b) (by linarith:0≤13*H)
  change max _ _≤31213*H^2
  cases pos <;> apply max_le <;> simp only [num,den,Bool.false_eq_true,ite_false,ite_true,abs_mul,abs_pow]
  all_goals norm_num1
  · calc
      _ = 2401*(|5*a+8*b| *|b|) := by ring
      _ ≤ 2401*((13*H)*H) := mul_le_mul_of_nonneg_left negnum (by decide)
      _ = _ := by ring
  · calc
      _ ≤ 8*(6*H)^2 := mul_le_mul_of_nonneg_left negden (by decide)
      _ ≤ _ := by nlinarith only [sq_nonneg H]
  · calc
      _ ≤ 343*(3*H)^2 := mul_le_mul_of_nonneg_left posnum (by decide)
      _ ≤ _ := by nlinarith only [sq_nonneg H]
  · calc
      _ = 8*(|a-4*b| *|b|) := by ring
      _ ≤ 8*((5*H)*H) := mul_le_mul_of_nonneg_left posden (by decide)
      _ ≤ _ := by nlinarith only [sq_nonneg H]

private theorem den_num_cast (q:ℚ) : (q.num:ℚ)=q*(q.den:ℚ) := by
  exact (div_eq_iff (by exact_mod_cast q.den_nz)).mp (Rat.num_div_den q)

theorem marked_height (pos:Bool) (q s:ℚ)
    (mark:q*den pos s 1=num pos s 1) (finite:den pos s 1 ≠ 0) :
    logHeight₁ q ≤ 2*logHeight₁ s+Real.log 31213 := by
  let a:=s.num
  let b:ℤ:=s.den
  let N:=num pos a b
  let D:=den pos a b
  have bn:(b:ℚ)≠0:=by dsimp [b];exact_mod_cast s.den_nz
  have n:(N:ℚ)=num pos s 1*(b:ℚ)^2:=by
    cases pos <;> dsimp [N,num,a,b] <;> push_cast <;> rw [den_num_cast s] <;> ring
  have d:(D:ℚ)=den pos s 1*(b:ℚ)^2:=by
    cases pos <;> dsimp [D,den,a,b] <;> push_cast <;> rw [den_num_cast s] <;> ring
  have dn:D≠0:=by
    intro e
    have z:(D:ℚ)=0:=by exact_mod_cast e
    exact (mul_ne_zero finite (pow_ne_zero 2 bn)) (d.symm.trans z)
  have cross : q.num * D = (q.den:ℤ)* N := by
    have eq0:(q.num:ℚ)*(D:ℚ)=(q.den:ℚ)*(N:ℚ):=by
      rw [den_num_cast q,n,d];linear_combination (q.den:ℚ)*(b:ℚ)^2*mark
    exact_mod_cast eq0
  have cop : Int.gcd q.num (q.den:ℤ)=1 := by simpa [Int.gcd] using q.reduced.gcd_eq_one
  have major : pairHeight q.num q.den≤31213*(pairHeight a b)^2 :=
    (proportional cop cross (Or.inr dn)).trans (homogeneous_height pos a b)
  have hp (v:ℚ) : 0<(pairHeight v.num v.den:ℝ) := by
    exact_mod_cast pairHeight_pos v.num v.den (Or.inr (by exact_mod_cast v.den_nz))
  have c:(pairHeight q.num q.den:ℝ)≤31213*(pairHeight s.num s.den:ℝ)^2 := by exact_mod_cast major
  have logb:=Real.log_le_log (hp q) c
  rw [Real.log_mul (by norm_num: (31213:ℝ)≠0) ((pow_pos (hp s) 2).ne'),Real.log_pow] at logb
  rw [logHeight_reduced_pair q,logHeight_reduced_pair s];unfold pairLogHeight
  norm_num at logb
  exact logb.trans_eq (add_comm ..)

end
end Sun28.ConicArithmetic
#print axioms Sun28.ConicArithmetic.marked_height

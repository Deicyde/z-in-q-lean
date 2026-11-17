import RowWeight
import ConeScale

namespace Sun28.ConeCount
open Finset Filter Topology Sun28.ConeSieve Sun28.QuadricSieve
open Sun28.ContactFactors Sun28.WeightedSelection Sun28.SieveTail Sun28.SinglePrime Sun28.MediumSieve

noncomputable section

theorem cutoff_level (A : Fin 3→ℚ) : ∀ᶠ t : ℕ in atTop, logCutoff A t≤level t := by
  let m:=(shifts A).card+5
  let C:=envelope A+404
  have h:= (tendsto_pow_const_div_const_pow_of_one_lt m (by norm_num : (1:ℝ)<2)).const_mul ((C:ℝ)^m)
  rw [mul_zero] at h
  filter_upwards [h.eventually_lt_const (by norm_num : (0:ℝ)<1),eventually_ge_atTop (1:ℕ)] with t ht one
  have l : growthBound A t≤C*t := by
    dsimp [growthBound,growth,C];nlinarith only [Nat.mul_le_mul_left (envelope A) one,one]
  have lim : (C:ℝ)^m*(t:ℝ)^m < (2:ℝ)^t := by
    change (C:ℝ)^m*((t:ℝ)^m/(2:ℝ)^t)<1 at ht
    rw [←mul_div_assoc] at ht
    simpa using (div_lt_iff₀ (by positivity : 0<(2:ℝ)^t)).mp ht
  have integral : (C*t)^m≤2^t := by rw [mul_pow];exact_mod_cast lim.le
  exact (Nat.pow_le_pow_left l m).trans integral

theorem volume_on_row {j t : ℕ} (wide : j+1≤ side t) :
    ConeReal.width j*(side t:ℝ)^3 ≤ 2*((lengthAt t:ℝ)*rowWidth j (lengthAt t)) := by
  let W:=rowWidth j (lengthAt t)
  have width : W=side t/(j+1) := by dsimp [W,rowWidth,lengthAt];rw [Nat.sqrt_eq' _]
  have wb : 1≤W := by rw [width];exact (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using wide)
  have half : side t≤2*((j+1)*W) := by
    have h:=Nat.mod_add_div (side t) (j+1)
    have lt:=Nat.mod_lt (side t) (by omega : 0<j+1)
    have pos:=Nat.mul_le_mul_left (j+1) wb
    rw [←width] at h
    nlinarith only [h,lt,pos]
  have bound : (side t:ℝ)≤2*(((j:ℝ)+1)*W) := by exact_mod_cast half
  have hi:=mul_le_mul_of_nonneg_left bound (by positivity : 0≤(side t:ℝ)^2)
  change ((j:ℝ)+1)⁻¹*(side t:ℝ)^3≤2*((((side t)^2:ℕ):ℝ)*W)
  push_cast
  rw [inv_mul_eq_div,div_le_iff₀ (by positivity : 0<(j:ℝ)+1)]
  linarith only [hi]

theorem discrepancy_power {t p m : ℕ} (hp : p≤level t) (hm : m≤(level t)^2) :
    ((side t:ℝ)*(p:ℝ)*(m:ℝ))^(13/5:ℝ)≤(2:ℝ)^(559*t) := by
  have cap : ((side t:ℝ)*((p:ℝ)*m))^26≤((2:ℝ)^(528*t))^10 := by exact_mod_cast congruence_power hp hm
  apply le_trans ?_ (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show 528*t≤559*t by omega))
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (by positivity) _) (by positivity) (by decide : 10≠0)).mp
  rw [←Real.rpow_natCast _ 10,←Real.rpow_mul (by positivity),show (13/5:ℝ)*((10:ℕ):ℝ)=((26:ℕ):ℝ) by norm_num]
  simpa only [Real.rpow_natCast,mul_assoc] using cap

theorem log_scale {j : ℕ} : ∀ᶠ t : ℕ in atTop,j+1≤ side t := by
  filter_upwards [eventually_ge_atTop (j+1)] with t ht
  unfold side
  exact ht.trans ((Nat.lt_two_pow_self (n:=t)).le.trans (Nat.pow_le_pow_right (by decide) (by omega)))

theorem finite_estimates {ι : Type*} [Fintype ι] {P : ι→ℝ→Prop}
    (h : ∀ i,∃ c : ℝ,0≤c ∧ P i c) (mono : ∀ i a b, a≤b→P i a→P i b) :
    ∃ C : ℝ,0≤C ∧ ∀ i,P i C := by
  classical
  choose c pos valid using h
  refine ⟨∑ i,c i,sum_nonneg (fun i _=>pos i),?_⟩
  intro i
  exact mono i _ _ (single_le_sum (fun k _=>pos k) (mem_univ i)) (valid i)

end
end Sun28.ConeCount
#print axioms Sun28.ConeCount.cutoff_level
#print axioms Sun28.ConeCount.volume_on_row
#print axioms Sun28.ConeCount.discrepancy_power

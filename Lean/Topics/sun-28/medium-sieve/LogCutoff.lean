import MeanWindow
import MiddleRange

namespace Sun28.MediumSieve
open Sun28.SinglePrime Sun28.ContactFactors Sun28.WeightedSelection Filter Topology
noncomputable section

/-- Since t is proportional to log N, this is a fixed power of an affine function of log N. -/
def logCutoff (A : Fin 3→ℚ) (t : ℕ) := (growthBound A t)^((shifts A).card+5)

theorem cutoff_degree (A : Fin 3→ℚ) : (shifts A).card+5≤18 :=
  Nat.add_le_add_right (Sun28.GaussianSelection.shifts_card_le A) 5

theorem cutoff_grows (A : Fin 3→ℚ) : Tendsto (logCutoff A) atTop atTop := by
  apply tendsto_atTop.mpr; intro n
  filter_upwards [eventually_ge_atTop n] with t ht
  have lo : t≤growthBound A t := by dsimp [growthBound,growth];omega
  exact (ht.trans lo).trans (by
    apply Nat.le_self_pow (by omega : (shifts A).card+5≠0))

theorem cutoff_within (A : Fin 3→ℚ) : ∀ᶠ t : ℕ in atTop,logCutoff A t≤ side t := by
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
  exact ((Nat.pow_le_pow_left l m).trans integral).trans
    (Nat.pow_le_pow_right (by decide : 0<2) (show t≤200*t by omega))

theorem relative_error (A : Fin 3→ℚ) : Tendsto (fun t=>meanConstant A/(growthBound A t:ℝ)) atTop (𝓝 0) := by
  apply (tendsto_const_div_atTop_nhds_zero_nat (meanConstant A)).comp
  apply tendsto_atTop.mpr;intro n
  filter_upwards [eventually_ge_atTop n] with t ht
  dsimp [growthBound,growth];omega

theorem log_tail {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ} (T : Finset ℕ) (κ t W : ℕ)
    (w : W≤ side t) (two : 2≤ logCutoff A t) (within : logCutoff A t≤ side t)
    (hT : ∀ p∈T,p≤ logCutoff A t) (hκ : ∀ p∈κ.primeFactors,p≤ logCutoff A t) :
    removedMass T κ (logCutoff A t) (box (A:=A) (d:=d) (H:=H) (Y:=Y) (lengthAt t) W) ≤
    (meanConstant A/(growthBound A t:ℝ))*((lengthAt t:ℝ)*W) := by
  apply (mean_window T κ t W (logCutoff A t) w two within hT hκ).trans_eq
  congr 1
  change meanConstant A*(growthBound A t:ℝ)^((shifts A).card+4)/(((growthBound A t)^((shifts A).card+5):ℕ):ℝ)=_
  rw [Nat.cast_pow,show (shifts A).card+5=(shifts A).card+4+1 by omega,pow_succ]
  have zz : (growthBound A t:ℝ) ≠0 := by dsimp [growthBound];positivity
  field_simp
  ring
end
end Sun28.MediumSieve
#print axioms Sun28.MediumSieve.cutoff_degree
#print axioms Sun28.MediumSieve.cutoff_grows
#print axioms Sun28.MediumSieve.cutoff_within
#print axioms Sun28.MediumSieve.relative_error
#print axioms Sun28.MediumSieve.log_tail

import LargePair

namespace Sun28.SinglePrime
open Sun28.ContactFactors Sun28.WeightedSelection Filter Topology
open scoped Classical
noncomputable section

def errorFactor (A : Fin 3→ℚ) (t : ℕ) : ℝ :=
  ((shifts A).card^2:ℕ)*(32*(pairConstant A:ℝ)*(envelope A+1:ℕ)^2)*
    (growth (envelope A) t+1:ℕ)^((shifts A).card+2)/(2:ℝ)^t

theorem large_window {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ} (T : Finset ℕ) (κ t W : ℕ)
    (tp : 0<t) (w : W ≤ side t) (hT : ∀ p∈T,p≤ splitAt t) (hκ : ∀ p∈κ.primeFactors,p≤ splitAt t) :
    removedMass T κ (splitAt t) (box (A:=A) (d:=d) (H:=H) (Y:=Y) (lengthAt t) W) ≤
      errorFactor A t*((lengthAt t:ℝ)*W) := by
  let E:=envelope A
  let G:ℝ:=(growth E t+1:ℕ)
  let C:ℝ:=32*(pairConstant A:ℝ)*(E+1:ℕ)^2
  let k:=(shifts A).card
  let N:=lengthAt t
  let D:ℝ:=2^t
  have r : 2≤ splitAt t := (by simpa only [splitAt,pow_one] using (Nat.pow_le_pow_right (n:=2) (by decide) (show 1≤2*t by omega)))
  have head := numerical_tail (A:=A) (d:=d) (H:=H) (Y:=Y) N W (splitAt t) r T κ hT hκ
  have pos : 1≤N := by dsimp [N,lengthAt]; exact Nat.one_le_pow _ _ (side_pos _)
  have vs : W^2≤N := Nat.pow_le_pow_left w 2
  have vx:=Nat.mul_le_mul_left (maxCoefficient A) vs
  have bound : N+maxCoefficient A*W^2+1≤E*N := by
    dsimp [E,envelope];nlinarith only [vx,pos,Nat.zero_le (maxCoefficient A*N)]
  have log := (small_log E t _ bound).2
  have major : weightBound A N W≤G^k := by
    apply pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (Nat.le_add_left 1 _)))
    refine log.trans ?_
    dsimp [G];exact_mod_cast Nat.le_succ _
  have ic : (indices A W).card=W*k^2 := by
    simp [indices,k,pow_two]
  have su : ((∑ z∈indices A W,pairBound N z.1 (splitAt t) z.2.1 z.2.2 : ℚ):ℝ) ≤
      (W*k^2:ℕ)*(C*G^2*((N:ℝ)/D)) := by
    rw [Rat.cast_sum]
    calc _ ≤ ∑ _∈indices A W,C*G^2*((N:ℝ)/D) := by
           apply Finset.sum_le_sum
           intro z hz
           exact pair_power A t _ ((Finset.mem_Icc.mp (Finset.mem_product.mp hz).1).2.trans w) _ _
         _ = _ := by simp [ic]
  have wn : 0≤weightBound A N W := pow_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.le_add_left 1 _))) _
  apply head.trans
  calc _ ≤ weightBound A N W*((W*k^2:ℕ)*(C*G^2*((N:ℝ)/D))) := mul_le_mul_of_nonneg_left su wn
       _ ≤ G^k*((W*k^2:ℕ)*(C*G^2*((N:ℝ)/D))) := mul_le_mul_of_nonneg_right major (by dsimp [C,G,D];positivity)
       _ = _ := by unfold errorFactor;rw [pow_add];push_cast;dsimp [C,G,D,k,N,E];push_cast;ring

theorem error_tendsto (A : Fin 3→ℚ) : Tendsto (errorFactor A) atTop (𝓝 0) := by
  let E:=envelope A
  let k:=(shifts A).card+2
  let C:ℝ:= ((shifts A).card^2:ℕ)*(32*(pairConstant A:ℝ)*(E+1:ℕ)^2)
  have h:= (tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1:ℝ)<2)).const_mul (C*(E+404:ℕ)^k)
  rw [mul_zero] at h
  apply squeeze_zero' (Eventually.of_forall (fun t=>by dsimp [errorFactor];positivity)) _ h
  filter_upwards [eventually_ge_atTop (1:ℕ)] with t ht
  have n : growth E t+1≤(E+404)*t := by
    dsimp [growth];nlinarith only [Nat.mul_le_mul_left E ht,ht]
  have p := Nat.pow_le_pow_left n k
  have pr : ((growth E t+1:ℕ):ℝ)^k≤((E+404:ℕ):ℝ)^k*(t:ℝ)^k := by
    rw [←mul_pow];exact_mod_cast p
  change C*((growth E t+1:ℕ):ℝ)^k/(2:ℝ)^t ≤ (C*((E+404:ℕ):ℝ)^k)*((t:ℝ)^k/2^t)
  rw [←mul_div_assoc,mul_assoc C]
  gcongr

end
end Sun28.SinglePrime
#print axioms Sun28.SinglePrime.large_window
#print axioms Sun28.SinglePrime.error_tendsto

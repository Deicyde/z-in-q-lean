import MinimalSets

/-! The published conductor estimate with an explicit part of the original coefficient. -/
set_option maxRecDepth 6000
namespace Sun28.MinimalConductors
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Height

/-- This scale is half of 4608^6912 and is 2304 times the previous scale. -/
def scale : ℕ := 2304*4608^6911

theorem scale_twice : 2*scale=4608^6912 := by
  have algebra (n : ℕ) : 2*(2304*4608^n)=4608^(n+1) := by
    rw [pow_succ,←mul_assoc]
    change 4608*4608^n=4608^n*4608
    exact mul_comm _ _
  have h:=algebra 6911
  rw [show (6911+1:ℕ)=6912 by decide] at h
  unfold scale
  exact h

theorem positive_scale : 0<scale := Nat.mul_pos (by decide) (pow_pos (by decide : 0<(4608:ℕ)) _)

attribute [local irreducible] scale

theorem coefficient_bound {N O : ℕ} (npos : 0<N) (opos : 0<O)
    (conductor : N≤(scale*cutoffProduct*O)^23) :
    (3/2)*(128*(N:ℝ))*(Real.log (128*(N:ℝ)))^2+65+32 ≤ glazerConstant24*(O:ℝ)^24 := by
  let K:ℝ:=scale
  let B:ℝ:=cutoffProduct
  have id : 2*K=(4608:ℝ)^6912 := by
    have h:=congrArg (fun n : ℕ => (n:ℝ)) scale_twice
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using h
  have kb : 1≤K := by
    change (1:ℝ)≤(scale:ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 positive_scale.ne'
  have b : 1≤B := by
    change (1:ℝ)≤(cutoffProduct:ℝ)
    exact_mod_cast (show 1≤cutoffProduct from pos_cutoff)
  have o : 1≤(O:ℝ) := by exact_mod_cast opos
  have x : 1≤K*B*(O:ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le kb b) o
  have co : (N:ℝ)≤(K*B*(O:ℝ))^23 := by
    change (N:ℝ)≤((scale:ℝ)*(cutoffProduct:ℝ)*(O:ℝ))^23
    exact_mod_cast conductor
  have h := analytic_absorption (by exact_mod_cast npos : (1:ℝ)≤N) x co
  have margin : (192:ℝ)*53^2≤2^24 := by norm_num
  have a : ((192:ℝ)*53^2)*K^24≤2*(4608^165888+6^100) := calc
    _ ≤ (2:ℝ)^24*K^24 := mul_le_mul_of_nonneg_right margin (pow_nonneg (by linarith only [kb]) _)
    _ = (4608:ℝ)^165888 := by rw [←mul_pow,id,←pow_mul]
    _ ≤ _ := by
      have twice (U V : ℝ) (u : 0≤U) (v : 0≤V) : U≤2*(U+V) := by linarith
      exact twice _ _ (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
  have bO : 0≤(B*(O:ℝ))^24 := pow_nonneg (by positivity) _
  have c : (97:ℝ)≤128*(O:ℝ)^24 := by
    have h1 : 1≤(O:ℝ)^24 := one_le_pow₀ o
    linarith
  have ident (z k b o : ℝ) : z*(k*b*o)^24=(z*k^24)*(b*o)^24 := by ring
  calc
    _ ≤ (192*53^2)*(K*B*(O:ℝ))^24+97 := by linarith only [h]
    _ ≤ 2*(4608^165888+6^100)*(B*(O:ℝ))^24+128*(O:ℝ)^24 := by
      rw [ident]
      exact add_le_add (mul_le_mul_of_nonneg_right a bO) c
    _ = glazerConstant24*(O:ℝ)^24 := by
      have beq (S : Finset ℕ) : (primeProduct S:ℝ)=∏ p ∈ S,(p:ℝ) := by
        unfold primeProduct
        push_cast
        rfl
      have clean (C b o : ℝ) : C*(b*o)^24+128*o^24=(C*b^24+128)*o^24 := by ring
      change _ = (2*(4608^165888+6^100)*(∏ p ∈ oldCutoff,(p:ℝ))^24+128)*(O:ℝ)^24
      rw [←beq oldCutoff]
      exact clean _ _ _

end Sun28.MinimalConductors
#print axioms Sun28.MinimalConductors.scale_twice
#print axioms Sun28.MinimalConductors.positive_scale
#print axioms Sun28.MinimalConductors.coefficient_bound

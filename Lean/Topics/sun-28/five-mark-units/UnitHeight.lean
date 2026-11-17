import UnitSupport

/-! Explicit absorption of von Känel's conductor bound into Glazer's exponent 24. -/
namespace Sun28.FiveMarkUnits
open Sun28.Ordinary Height

/-- A small uniform loss for every real X≥1, including the logarithm of 128. -/
theorem analytic_absorption {N X : ℝ} (npos : 1≤N) (xpos : 1≤X) (conductor : N≤X^23) :
    (3/2)*(128*N)*(Real.log (128*N))^2+65 ≤ (192*53^2)*X^24+65 := by
  have xp : 0<X := by linarith
  have sqp : 0<Real.sqrt X := Real.sqrt_pos.mpr xp
  have one : 1≤Real.sqrt X := by simpa using Real.sqrt_le_sqrt xpos
  have hs : Real.sqrt X^2=X := Real.sq_sqrt xp.le
  have lx : Real.log X≤2*Real.sqrt X := by
    have e := Real.log_pow (Real.sqrt X) 2
    rw [hs] at e
    norm_num at e
    linarith only [e,Real.log_le_sub_one_of_pos sqp]
  have l128 : Real.log 128≤7 := by
    rw [show (128:ℝ)=2^7 by norm_num,Real.log_pow]
    norm_num
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]
  have upper := Real.log_le_log (by positivity : 0<128*N) (mul_le_mul_of_nonneg_left conductor (by norm_num : 0≤(128:ℝ)))
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ xp.ne'),Real.log_pow] at upper
  norm_num at upper
  have lmax : Real.log (128*N) ≤ 53*Real.sqrt X := by linarith only [upper,lx,l128,one]
  have lpos : 0≤Real.log (128*N) := Real.log_nonneg (by linarith)
  have lsq := pow_le_pow_left₀ lpos lmax 2
  rw [mul_pow,hs] at lsq
  have m := mul_le_mul conductor lsq (sq_nonneg _) (by positivity : 0≤X^23)
  linarith only [show N*Real.log (128*N)^2 ≤ 53^2*X^24 by convert m using 1; ring]

theorem explicit_five_bound {N O : ℕ} (npos : 0<N) (opos : 0<O)
    (conductor : N≤(cutoffProduct*O)^23) :
    (3/2)*(128*(N:ℝ))*(Real.log (128*(N:ℝ)))^2+65 ≤ glazerConstant24*(O:ℝ)^24 := by
  let B : ℝ := cutoffProduct
  have b : 1≤B := by
    change (1:ℝ)≤(cutoffProduct:ℝ)
    exact_mod_cast (show 1≤cutoffProduct from pos_cutoff)
  have o : 1≤(O:ℝ) := by exact_mod_cast opos
  have x : 1≤B*(O:ℝ) := one_le_mul_of_one_le_of_one_le b o
  have co : (N:ℝ)≤(B*(O:ℝ))^23 := by
    change (N:ℝ)≤((cutoffProduct:ℝ)*(O:ℝ))^23
    exact_mod_cast conductor
  have h := analytic_absorption (by exact_mod_cast npos : (1:ℝ)≤N) x co
  have h6 : (192:ℝ)*53^2 ≤ 2*(4608^165888+6^100) := by
    have le : (6:ℝ)^8≤6^100 := pow_le_pow_right₀ (by norm_num) (by decide)
    have pos : (0:ℝ)≤4608^165888 := pow_nonneg (by norm_num) _
    calc
      (192:ℝ)*53^2 ≤ 2*6^8 := by norm_num
      _ ≤ 2*6^100 := mul_le_mul_of_nonneg_left le (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left pos) (by norm_num)
  have l := mul_le_mul_of_nonneg_right h6 (by positivity : 0≤(B*(O:ℝ))^24)
  have c : (65:ℝ)≤128*(O:ℝ)^24 := by
    have h1 : 1≤(O:ℝ)^24 := one_le_pow₀ o
    linarith
  calc
    _ ≤ _ := h
    _ ≤ 2*(4608^165888+6^100)*(B*(O:ℝ))^24+128*(O:ℝ)^24 := add_le_add l c
    _ = glazerConstant24*(O:ℝ)^24 := by
      have beq (S : Finset ℕ) : (primeProduct S:ℝ)=∏ p ∈ S,(p:ℝ) := by
        unfold primeProduct
        push_cast
        rfl
      have clean (C b o : ℝ) : C*(b*o)^24+128*o^24=(C*b^24+128)*o^24 := by ring
      change _ = (2*(4608^165888+6^100)*(∏ p ∈ oldCutoff,(p:ℝ))^24+128)*(O:ℝ)^24
      rw [←beq oldCutoff]
      exact clean _ _ _

end Sun28.FiveMarkUnits
#print axioms Sun28.FiveMarkUnits.analytic_absorption
#print axioms Sun28.FiveMarkUnits.explicit_five_bound

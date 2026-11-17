import ScalarConicFamily

namespace Sun28.MultiplierChoice
open Sun28.FixedPreparation Sun28.ScalarHeight
open private C scaleK divisorK normalizer div_positive positive_K form_bound from ScalarConicFamily
noncomputable section
set_option maxRecDepth 8192

private theorem between_squares {a c : ℤ} (low : (a-1)^2 < c) (high : c < a^2)
    (positive : 0 < a) : ¬ IsSquare c := by
  rintro ⟨z,eq⟩
  have h : |z|^2 = c := by rw [sq_abs, sq, ←eq]
  rcases le_or_gt |z| (a - 1) with small|large
  · have : |z|^2 ≤ (a-1)^2 := by gcongr
    omega
  · have big : a ≤ |z| := by omega
    have : a^2 ≤ |z|^2 := by gcongr
    omega

/-- At every member the positive multiplier 15 fails the exact both-zero test.
The negative multiplier −5 has an explicit both-zero witness. -/
theorem strict_companion (n : ℕ) :
    ¬ DoubleRoot 15 (scalarPole n) ∧ DoubleRoot (-5) (scalarPole n) := by
  refine ⟨?_, negative_companion n⟩
  obtain ⟨bp,small⟩ := form_bound n
  have positive : 0 < 1 - scalarPole n / 15 := by linarith
  intro root
  rcases (double_root_iff (by norm_num) bp.ne' (by linarith)).mp root with square|neg
  · let d : ℤ := (base : ℤ) * (C : ℤ)^2
    let k : ℤ := scaleK n
    let j : ℤ := divisorK n
    have dp : 0 < d := by norm_num [d,C,base,gamma,FixedPreparation.primorial]
    have kp : 6*d + 1 ≤ k := by
      have e : k = 3*d*((n:ℤ)+2)+1 := by dsimp [k,d,scaleK]; ring
      nlinarith only [e,mul_nonneg dp.le (Int.natCast_nonneg n)]
    have jp : (j : ℚ) ≠ 0 := by simpa only [j,Int.cast_natCast] using (div_positive n).ne'
    have jdef : (j:ℚ) = (k:ℚ)^2 - 3*(d:ℚ) := by
      simpa only [j,k,d,Int.cast_natCast,Int.cast_mul,Int.cast_pow,mul_assoc] using normalizer n
    let v : ℤ := (k^2-5*d)^2 - 16*d^2
    have val : (v:ℚ) = (1-scalarPole n/15)*(j:ℚ)^2 := by
      change (v:ℚ) = (1-15*(base:ℚ)*(2*(C:ℚ)*(k:ℚ)/(j:ℚ))^2/15)*(j:ℚ)^2
      field_simp [jp]
      dsimp [v]; push_cast; rw [jdef]; dsimp [d]; push_cast; ring
    have s : IsSquare (v:ℚ) := by
      rw [val]
      exact square.mul (IsSquare.sq _)
    have lower : (k^2 - 5*d - 1)^2 < v := by
      have sqh : (6*d+1)^2 ≤ k^2 := by gcongr
      dsimp [v]; nlinarith only [sqh,dp,sq_nonneg d]
    have high : v < (k^2 - 5*d)^2 := by
      dsimp [v]; nlinarith only [sq_pos_of_pos dp]
    have apos : 0 < k^2 - 5*d := by
      have sqh : (6*d+1)^2 ≤ k^2 := by gcongr
      nlinarith only [sqh,dp,sq_nonneg d]
    exact between_squares lower high apos (Rat.isSquare_intCast_iff.mp s)
  · obtain ⟨y,eq⟩ := neg
    nlinarith only [positive,eq,sq_nonneg y]

/-- Distinct indices give distinct prepared scalar arguments. -/
theorem scalarPole_strictAnti : StrictAnti scalarPole := by
  intro m n h
  let t : ℚ := 3*(base:ℚ)*(C:ℚ)^2
  have tp : 0 < t := by norm_num [t,base,C,gamma,FixedPreparation.primorial]
  let k : ℕ → ℚ := fun i => scaleK i
  have kform (i:ℕ) : k i = t*((i:ℚ)+2)+1 := by dsimp [k,t,scaleK];push_cast;ring
  have klt : k m < k n := by
    rw [kform,kform];gcongr
  have kp (i:ℕ) : 0 < k i := by dsimp [k]; exact_mod_cast positive_K i
  have den (i:ℕ) : 0 < k i ^ 2 - t := by simpa only [normalizer,k,t] using div_positive i
  have fr : k n/(k n^2-t) < k m/(k m^2-t) := by
    rw [div_lt_div_iff₀ (den n) (den m)]
    have : 0 < (k n - k m)*(k m*k n + t) := mul_pos (sub_pos.mpr klt) (add_pos (mul_pos (kp m) (kp n)) tp)
    linarith only [show k m*(k n^2-t) - k n*(k m^2-t) = (k n-k m)*(k m*k n+t) by ring,this]
  have cc : 0 < 2*(C:ℚ) := by norm_num [C,gamma,FixedPreparation.primorial]
  have repr (i:ℕ) : scalarPole i = 15*(base:ℚ)*((2*(C:ℚ))*(k i/(k i^2-t)))^2 := by
    dsimp [scalarPole];rw [normalizer];dsimp [k,t];ring
  rw [repr,repr]
  have b : 0 < 15*(base:ℚ) := by norm_num [base]
  apply mul_lt_mul_of_pos_left _ b
  exact pow_lt_pow_left₀ (mul_lt_mul_of_pos_left fr cc) (mul_nonneg cc.le (div_nonneg (kp n).le (den n).le)) (by decide)
end
end Sun28.MultiplierChoice
#print axioms Sun28.MultiplierChoice.strict_companion
#print axioms Sun28.MultiplierChoice.scalarPole_strictAnti

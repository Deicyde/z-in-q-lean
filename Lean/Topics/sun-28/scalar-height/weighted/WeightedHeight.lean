import WeightedProduct

namespace Sun28.ScalarDepth
open ZInQ Height Sun28.Ordinary Sun28.Forward Sun28.ScalarHeight Sun28.ScalarLucas
open Sun28.FixedPreparation Sun28.WitnessIndices Sun28.WitnessHeight Sun28.IndexHeights
noncomputable section
attribute [local irreducible] glazerConstant24 stepFloor modulus radical
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

def floor (x : ℚ) : ℕ := fixedMultiplier.lcm (modulus x)
def allowance (x : ℚ) : ℝ := (floor x:ℝ)*Real.log (floor x:ℝ)/24

theorem previous_floor_dvd (x : ℚ) : stepFloor x ∣ floor x := by
  unfold stepFloor floor
  exact Nat.lcm_dvd (Nat.dvd_lcm_left ..) ((radical_power_dvd x).trans (Nat.dvd_lcm_right ..))

theorem floor_pos (x : ℚ) : 0 < floor x := Nat.lcm_pos
  (Nat.lt_of_lt_of_le (by decide : 0<12) fixed_reserve.1) (modulus_pos x)

theorem previous_allowance (x : ℚ) : scalarAllowance x ≤ allowance x := by
  have mono : (stepFloor x:ℝ)≤floor x := by exact_mod_cast Nat.le_of_dvd (floor_pos x) (previous_floor_dvd x)
  have one : 1≤(stepFloor x:ℝ) := by
    have n : 1 ≤ stepFloor x := (by decide : 1≤12).trans (fixed_reserve.1.trans (stepFloor_bounds x).1)
    exact Nat.one_le_cast.mpr n
  exact div_le_div_of_nonneg_right (mul_le_mul mono (Real.log_le_log (by linarith) mono)
    (Real.log_nonneg one) (by positivity)) (by norm_num)

theorem weighted_comparison (x : ℚ) {c : ℕ} (le : floor x≤c) :
    logConstant+3*allowance x < ((c:ℝ)/4)*Real.log (c:ℝ) := by
  have f : fixedMultiplier≤floor x := Nat.le_of_dvd (floor_pos x) (Nat.dvd_lcm_left ..)
  have F : (fixedMultiplier:ℝ)≤floor x := by exact_mod_cast f
  have hu : (12:ℝ)≤floor x := by exact_mod_cast fixed_reserve.1.trans f
  have v : (floor x:ℝ)≤c := by exact_mod_cast le
  have log := log_one_of_floor hu
  have pos : (0:ℝ)<floor x := by linarith
  have lin : (floor x:ℝ) ≤ (floor x:ℝ)*Real.log (floor x:ℝ) := by
    simpa using mul_le_mul_of_nonneg_left log pos.le
  have prod := mul_le_mul v (Real.log_le_log pos v) (by linarith : 0≤Real.log (floor x:ℝ))
    (by positivity : 0≤(c:ℝ))
  unfold allowance
  linarith only [fixed_reserve.2.1,le_abs_self logConstant,lin,prod,F]

/-- Both the local order calculation and the ordinary inequalities are applied to these very witnesses. -/
theorem integral (A : Fin 9 → AffineInput) (x η : ℚ)
    (accepted : PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers)
    (tests : OrdinaryIndices A η) (height : logHeight₁ (beta x) ≤ allowance x) :
    ∃ k : ℤ, x=(k:ℚ) := by
  have g : 0≤glazerConstant24 := by unfold glazerConstant24; positivity
  have o : 0≤ordinary := by unfold ordinary glazerConstant24; positivity
  obtain ⟨a,e,_⟩ := extract_indices A anchor (K:=logConstant) o g accepted.q_nonzero
    accepted.h_nonzero accepted.base_nonzero accepted.odd_N accepted.odd_T accepted.odd_Z
  apply Sun28.integral_input x (a.n 0)
  by_contra wrong
  obtain ⟨zero,upper⟩ := ordinary_index_outputs A x η accepted e tests wrong
  have tree := tree_of_points e _ _ _ _ accepted.scalar
  have md := modulus_dvd sqrt2_sq e.h_nonzero x tree
  have dv : modulus x ∣ scalarStep a.n := by simpa [scalarStep] using Int.natAbs_dvd_natAbs.mpr md
  have anchorDv : fixedMultiplier ∣ scalarStep a.n := by
    refine ⟨a.q.natAbs,?_⟩
    simp only [scalarStep,e.anchor,Int.natAbs_mul,Int.natAbs_natCast]
    rw [fixedMultiplier]
  have mc := (scalar_step_range fixed_multiplier_spec.2.1 a.n a.q e.q_nonzero e.anchor).1
  have big := fixed_reserve.1.trans mc
  have pos : 0 < scalarStep a.n := by omega
  have lower := lucas_coordinate_growth a.n e.z_nonzero big zero
  have sep := weighted_comparison x (Nat.le_of_dvd pos (Nat.lcm_dvd anchorDv dv))
  linarith only [lower,upper,sep,height]

end
end Sun28.ScalarDepth
#print axioms Sun28.ScalarDepth.previous_floor_dvd
#print axioms Sun28.ScalarDepth.floor_pos
#print axioms Sun28.ScalarDepth.previous_allowance
#print axioms Sun28.ScalarDepth.weighted_comparison
#print axioms Sun28.ScalarDepth.integral

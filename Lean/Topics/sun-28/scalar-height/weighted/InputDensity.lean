import ExceptionalCount

namespace Sun28.ScalarDepth
open Filter Topology
noncomputable section

private theorem length_bound {n : ℕ} (pos : 1≤n) : (2*n.sqrt+1)^2 ≤ 9*n := by
  have sp : 1≤n.sqrt := Nat.le_sqrt'.mpr (by simpa using pos)
  have h := Nat.pow_le_pow_left (show 2*n.sqrt+1≤3*n.sqrt by omega) 2
  calc
    _ ≤ (3*n.sqrt)^2 := h
    _ = 9*n.sqrt^2 := by ring
    _ ≤ 9*n := Nat.mul_le_mul_left _ (Nat.sqrt_le' n)

/-- A simpler effective upper bound with the full twenty-fourth-power test. -/
theorem count_linear {B K : ℕ} (b : 0<B) (k : 0<K)
    (threshold : 2*Real.log (B:ℝ)+4 ≤ ((K+1:ℕ):ℝ)^24) :
    (exceptionalInputs B).card ≤ 324*B*K := by
  have a := length_bound k
  have c := length_bound (n:=2*B) (by omega)
  have lim := Nat.mul_le_mul (Nat.mul_le_mul_left 2 a) c
  exact (exceptional_count threshold).trans (by convert lim using 1; ring)

/-- Vanishing density on the B-squared scale of primitive rational inputs. -/
theorem exceptional_density :
    Tendsto (fun B : ℕ => ((exceptionalInputs B).card:ℝ)/(B:ℝ)^2) atTop (𝓝 0) := by
  have loglim : Tendsto (fun B : ℕ => Real.log (B:ℝ)/(B:ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))
  have lim : Tendsto (fun B : ℕ => 648*(Real.log (B:ℝ)/(B:ℝ))+1620/(B:ℝ)) atTop (𝓝 0) := by
    simpa using (loglim.const_mul (648:ℝ)).add (tendsto_const_div_atTop_nhds_zero_nat (1620:ℝ))
  apply squeeze_zero' (Eventually.of_forall fun B => by positivity) _ lim
  filter_upwards [eventually_ge_atTop (1:ℕ)] with B bp
  let A := 2*Real.log (B:ℝ)+4
  let K := ⌈A⌉₊
  have lb := Real.log_nonneg (show (1:ℝ)≤B by exact_mod_cast bp)
  have ap : 1≤A := by dsimp [A];linarith
  have ka : A≤(K:ℝ) := Nat.le_ceil _
  have kp : 0<K := Nat.ceil_pos.mpr (zero_lt_one.trans_le ap)
  have plus : A≤((K+1:ℕ):ℝ) := by push_cast;linarith
  have large := pow_le_pow_right₀ (ap.trans plus) (show 1≤24 by decide)
  rw [pow_one] at large
  have count := count_linear (B:=B) (K:=K) bp kp (plus.trans large)
  have cs : ((exceptionalInputs B).card:ℝ)≤324*(B:ℝ)*(K:ℝ) := by exact_mod_cast count
  have cs2 : (K:ℝ) ≤ A+1 := (Nat.ceil_lt_add_one (show 0≤A by linarith)).le
  have rp : (0:ℝ)<B := by exact_mod_cast bp
  calc
    ((exceptionalInputs B).card:ℝ)/(B:ℝ)^2 ≤ (324*B*(A+1))/(B:ℝ)^2 :=
      div_le_div_of_nonneg_right (cs.trans (mul_le_mul_of_nonneg_left cs2 (by positivity))) (by positivity)
    _ = 648*(Real.log (B:ℝ)/(B:ℝ))+1620/(B:ℝ) := by dsimp [A];field_simp;ring

end
end Sun28.ScalarDepth
#print axioms Sun28.ScalarDepth.count_linear
#print axioms Sun28.ScalarDepth.exceptional_density

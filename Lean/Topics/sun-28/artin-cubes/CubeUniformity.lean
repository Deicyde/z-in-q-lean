import CubeProducts
import CenteredCube
import Mathlib.Analysis.SpecialFunctions.Log.Summable

namespace Sun28.ArtinCube
open Finset Sun28.SinglePrime Filter Topology
open scoped Classical
noncomputable section

/-- Explicit control of the complete normalized local product outside the base. -/
theorem local_product {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset (Finset ι))
    (v R q : ℕ) (b : (p : ℕ) → Finset ι → ZMod p) (large : 2≤v)
    (cap : 2*S.card ≤ v) (qn : 0<q) :
    |(∏ p ∈ places v R,localFactor S q b p)-1| ≤
      Real.exp ((2*(S.card:ℝ)^2*(4*Real.log 4)+2*S.card*Real.log q)/((v:ℝ)*Real.log v))-1 := by
  have h := (places v R).norm_prod_one_add_sub_one_le (fun p => localFactor S q b p-1)
  simp only [Real.norm_eq_abs,show ∀ x:ℝ,1+(x-1)=x from fun x => by ring] at h
  exact h.trans (sub_le_sub_right (Real.exp_le_exp.mpr (local_sum S v R q b large cap qn)) _)

/-- Uniformity for every choice of step and wrap constants with log(q)≤Cv.
Both the upper product cutoff and all the wrap constants may depend on v. -/
theorem product_tends_to_one {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset (Finset ι))
    (q R : ℕ → ℕ) (b : ℕ → (p : ℕ) → Finset ι → ZMod p) (C : ℝ)
    (qn : ∀ᶠ v : ℕ in atTop,0<q v) (bounded : ∀ᶠ v : ℕ in atTop,Real.log (q v:ℝ) ≤ C*v) :
    Tendsto (fun v => ∏ p ∈ places v (R v),localFactor S (q v) (b v) p) atTop (𝓝 1) := by
  let k : ℝ := S.card
  let A : ℝ := 2*k^2*(4*Real.log 4)
  have An : 0 ≤ A := by dsimp [A]; positivity
  have logup := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have inv := tendsto_inv_atTop_zero.comp logup
  have lim := inv.const_mul (A+2*k*C)
  rw [mul_zero] at lim
  apply Metric.tendsto_nhds.mpr
  intro ε he
  have exp := (Real.continuous_exp.continuousAt.tendsto.comp lim).sub_const 1
  rw [Real.exp_zero, sub_self] at exp
  filter_upwards [exp.eventually_lt_const he,qn,bounded,eventually_ge_atTop (max 2 (2*S.card))] with v small qp size lower
  have vv := (le_max_left 2 (2*S.card)).trans lower
  have pos : 0<(v:ℝ) := by exact_mod_cast (show 0<v by omega)
  have one : 1≤(v:ℝ) := by exact_mod_cast (show 1≤v by omega)
  have logp := Real.log_pos (by exact_mod_cast (show 1<v by omega) : (1:ℝ)<v)
  have H := local_product S v (R v) (q v) (b v) vv ((le_max_right _ _).trans lower) qp
  change |(∏ p ∈ places v (R v),localFactor S (q v) (b v) p)-1| < ε
  apply H.trans_lt (lt_of_le_of_lt (sub_le_sub_right (Real.exp_le_exp.mpr ?_) _) small)
  change (A+2*k*Real.log (q v:ℝ))/((v:ℝ)*Real.log v) ≤ (A+2*k*C)*(Real.log (v:ℝ))⁻¹
  apply (div_le_iff₀ (mul_pos pos logp)).mpr
  have scale : (A+2*k*C)*(Real.log (v:ℝ))⁻¹*((v:ℝ)*Real.log v) = (A+2*k*C)*v := by field_simp
  rw [scale]
  have kn : 0 ≤ k := by dsimp [k];positivity
  nlinarith only [mul_le_mul_of_nonneg_right one An,mul_le_mul_of_nonneg_left size (show 0≤2*k by linarith)]

end
end Sun28.ArtinCube
#print axioms Sun28.ArtinCube.local_product
#print axioms Sun28.ArtinCube.product_tends_to_one

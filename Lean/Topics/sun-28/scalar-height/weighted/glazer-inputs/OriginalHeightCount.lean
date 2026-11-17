import OriginalRows
import SmallKernelCount

namespace ZInQBlueprint.OriginalHeightCount
open scoped Classical
open Finset Filter Topology Height Sun28.Ordinary ZInQBlueprint.SmallKernelCount
noncomputable section

/-- Both coordinates of every exceptional slope belong to the same set of square multiples. -/
theorem covered_by_small_kernels {B K : ℕ}
    (threshold : Real.log (B:ℝ)≤((K+1:ℕ):ℝ)^24) :
    exceptions B ⊆ signedPairs (smallValues B K) := by
  intro x hx
  obtain ⟨box,off,_⟩ := (mem_exceptions x B).mp hx
  obtain ⟨d,u,dp,dk,eq⟩ := row_square_at_failure hx threshold 1
  obtain ⟨e,v,ep,ek,eqb⟩ := row_square_at_failure hx threshold 0
  have p : x.num≠0 := by simpa [oldForm] using off 1
  have ae : x.num.natAbs=d*u^2 := by simpa [oldForm] using eq
  have be : x.den=e*v^2 := by simpa [oldForm] using eqb
  exact mem_signedPairs x
    (mem_of_repr (Int.natAbs_pos.mpr p) (max_le_iff.mp box).1 dp dk ae)
    (mem_of_repr x.den_pos (max_le_iff.mp box).2 ep ek be)

theorem original_exceptional_count {B K : ℕ}
    (threshold : Real.log (B:ℝ)≤((K+1:ℕ):ℝ)^24) :
    (exceptions B).card≤8*B*K := by
  let S:=smallValues B K
  have sub := card_le_card (covered_by_small_kernels threshold)
  have product : (signedPairs S).card≤2*S.card^2 := by
    unfold signedPairs
    apply card_image_le.trans
    simp only [card_product,card_univ,Fintype.card_bool]
    rw [pow_two]
  have h : ((exceptions B).card:ℝ)≤2*(S.card:ℝ)^2 := by exact_mod_cast sub.trans product
  have s : (S.card:ℝ)≤2*Real.sqrt (B:ℝ)*Real.sqrt (K:ℝ) := card_smallValues B K
  have ss := pow_le_pow_left₀ (show 0≤(S.card:ℝ) by positivity) s 2
  have budget : ((exceptions B).card:ℝ)≤8*(B:ℝ)*(K:ℝ) := by
    calc
      _ ≤ 2*(2*Real.sqrt (B:ℝ)*Real.sqrt (K:ℝ))^2 := h.trans (mul_le_mul_of_nonneg_left ss (by norm_num))
      _ = _ := by rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity : 0≤(B:ℝ)),Real.sq_sqrt (by positivity : 0≤(K:ℝ))];ring
  exact_mod_cast budget

/-- The exception set for the original five-contact height inequality has zero density
on the quadratic scale of all reduced rational slopes. -/
theorem original_exceptional_density :
    Tendsto (fun B : ℕ => ((exceptions B).card:ℝ)/(B:ℝ)^2) atTop (𝓝 0) := by
  have loglim : Tendsto (fun B : ℕ => Real.log (B:ℝ)/(B:ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))
  have lim : Tendsto (fun B : ℕ => 8*(Real.log (B:ℝ)/(B:ℝ))+8/(B:ℝ)) atTop (𝓝 0) := by
    simpa using (loglim.const_mul (8:ℝ)).add (tendsto_const_div_atTop_nhds_zero_nat (8:ℝ))
  apply squeeze_zero' (Eventually.of_forall fun B => by positivity) _ lim
  filter_upwards [eventually_ge_atTop (1:ℕ)] with B bp
  let K:=⌈Real.log (B:ℝ)⌉₊
  have non : 0≤Real.log (B:ℝ) := Real.log_nonneg (by exact_mod_cast bp)
  have le : Real.log (B:ℝ)≤(K:ℝ) := Nat.le_ceil _
  have add : Real.log (B:ℝ)≤((K+1:ℕ):ℝ) := by push_cast;linarith
  have one : (1:ℝ) ≤ ((K+1:ℕ):ℝ) := by exact_mod_cast (Nat.succ_pos K)
  have pl := pow_le_pow_right₀ one (show 1≤24 by decide)
  rw [pow_one] at pl
  have hc : ((exceptions B).card:ℝ)≤8*(B:ℝ)*(K:ℝ) := by exact_mod_cast original_exceptional_count (add.trans pl)
  have ceil := (Nat.ceil_lt_add_one non).le
  have pos : (0:ℝ)<B := by exact_mod_cast bp
  calc
    ((exceptions B).card:ℝ)/(B:ℝ)^2 ≤ (8*B*(Real.log (B:ℝ)+1))/(B:ℝ)^2 :=
      div_le_div_of_nonneg_right (hc.trans (mul_le_mul_of_nonneg_left ceil (by positivity))) (by positivity)
    _ = 8*(Real.log (B:ℝ)/(B:ℝ))+8/(B:ℝ) := by field_simp

end
end ZInQBlueprint.OriginalHeightCount
#print axioms ZInQBlueprint.OriginalHeightCount.covered_by_small_kernels
#print axioms ZInQBlueprint.OriginalHeightCount.original_exceptional_count
#print axioms ZInQBlueprint.OriginalHeightCount.original_exceptional_density

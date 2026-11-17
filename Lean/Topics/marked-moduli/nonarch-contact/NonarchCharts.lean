import TwoCentreWeights
import PoleHeight
import EmbeddedBranches

/-! Clearing the pole form in both integral charts yields a single denominator for all parameters. -/
open Polynomial
namespace ZInQBlueprint.NonarchContact
open DirectCharts IntegralSextic BranchDepth ResidualFactors SexticIgusaChart SexticThetaHeight
noncomputable section

def denominator (u : ℚ) : ℕ := 144*3^4*27^2*(poleNorm u)^6

theorem pole_positive (u : ℚ) : 0 < poleForm u.num (u.den:ℤ) := by
  have hb : 0 < (u.den:ℤ) := by exact_mod_cast u.den_pos
  unfold poleForm
  nlinarith [sq_pos_of_pos hb, sq_nonneg (7*u.num+150*(u.den:ℤ))]

theorem denominator_pos (u : ℚ) : 0 < denominator u := by
  have : 0 < poleNorm u := Int.natAbs_pos.mpr (pole_positive u).ne'
  unfold denominator
  positivity

theorem denominator_pole (u : ℚ) :
    (denominator u:ℤ) = 144*3^4*27^2*(poleForm u.num (u.den:ℤ))^6 := by
  simp [denominator,poleNorm,abs_of_pos (pole_positive u)]

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]

omit [IsUltrametricDist K] [CharZero K] in
/-- The distinguished sum can be recovered directly from its six roots over any
characteristic-zero normed field, including the algebraic closure of a completion. -/
theorem sum_roots {t : K} (r : Fin 6 → K) (hr : Function.Injective r)
    (hz : ∀ i, form 1 t (r i) 1=0) :
    ∑ i, weight r i = -144*t^2*(t^2+27)^2 := by
  classical
  apply monic_weight_sum
  let f := monicSextic t
  let e : Fin 6 ↪ K := ⟨r,hr⟩
  let S := Finset.univ.map e
  have hc : S.card=6 := by simp [S]
  have hd : f.natDegree=6 := (monic_six _).2
  have hR : f.roots = S.val := roots_eq_of_natDegree_le_card_of_ne_zero (fun x hx => by
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    change (monicSextic t).eval (r i) = 0
    exact (monic_eval _ _).trans (hz i)) (hd.trans hc.symm).le (monic_six _).1.ne_zero
  have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (monic_six t).1 (hR ▸ hc.trans hd.symm)
  rw [hR] at h
  convert h using 1
  change (∏ i, (X-C (r i))) = ∏ x ∈ S, (X-C x)
  rw [Finset.prod_map]
  rfl

private theorem chart_bound {t : K} (ht : t≠0) (hD : t^2+27≠0) (hti : ‖t‖ ≤ 1)
    (r : Fin 6 → K) (hr : Function.Injective r) (hz : ∀ i, form 1 t (r i) 1=0)
    (i : Fin 10) : ‖normalized (weight r) i‖ * ‖144*(3:K)^4*(t^2+27)^2‖ ≤ 1 := by
  have h144 : ‖(144:K)‖ ≠ 0 := norm_ne_zero_iff.mpr (by norm_num)
  have hρ : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  have hd : ‖t^2+27‖ ≠ 0 := norm_ne_zero_iff.mpr hD
  have rat : ‖normalized (weight r) i‖ * ‖144*(3:K)^4*(t^2+27)^2‖ =
      ‖weight r i‖*‖(3:K)‖^4 / ‖t‖^2 := by
    simp only [normalized,norm_div,sum_roots r hr hz,norm_mul,norm_neg,norm_pow]
    field_simp [h144,hρ,hd]
  rw [rat,div_le_one (by positivity)]
  exact weight_bound hti r hz i

omit [IsUltrametricDist K] in
private theorem reciprocal_pair {t : K} (ht : t≠0) (r : Fin 6 → K) (hr : Function.Injective r)
    (hz : ∀ i, form 1 t (r i) 1=0) :
    ∃ s : Fin 6 → K, Function.Injective s ∧ (∀ j, form 1 (27/t) (s j) 1=0) ∧
      (∀ i, normalized (weight s) i=normalized (weight r) i) := by
  have hn (i) : r i≠0 := by
    intro he
    have := hz i
    simp [he,form,alpha,beta,gamma,ht] at this
  let s (i : Fin 6) := 6/r i
  have hi : Function.Injective s := by
    intro i k h
    apply hr
    change 6/r i = 6/r k at h
    simp only [div_eq_mul_inv] at h
    exact inv_injective (mul_left_cancel₀ (by norm_num : (6:K)≠0) h)
  refine ⟨s,hi,?_,?_⟩
  · intro i
    have he : (r i)^6*t^2*form 1 (27/t) (s i) 1 = 5832*form 1 t (r i) 1 := by
      unfold form alpha beta gamma s
      field_simp [ht,hn i]
      ring
    rw [hz i,mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero (pow_ne_zero _ (hn i)) (pow_ne_zero _ ht))
  · intro i
    simpa [s,mobius] using normalized_mobius r 0 6 1 0 (by norm_num)
      (fun j => by simpa using hn j) i

/-- For an integral homogeneous pair, the ordinary or reciprocal parameter is integral.
The clearing factor divides the one appearing in the chart estimate. -/
theorem homogeneous_bound {m n G : K} (hm : m≠0) (hn : n≠0) (hg : G≠0)
    (hi : ‖m‖ ≤ 1) (hj : ‖n‖ ≤ 1) (hid : G^3=27*m^2+n^2)
    (r : Fin 6 → K) (hr : Function.Injective r) (hz : ∀ j, form 1 (n/m) (r j) 1=0)
    (i : Fin 10) : ‖normalized (weight r) i‖ * ‖144*(3:K)^4*27^2*G^6‖ ≤ 1 := by
  let t := n/m
  have htn : t≠0 := div_ne_zero hn hm
  have h27 : (27:K)≠0 := by norm_num
  have h27le : ‖(27:K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K 27
  have hd : t^2+27=G^3/m^2 := by
    dsimp [t]
    field_simp [hm]
    linear_combination -hid
  have hd₀ : t^2+27≠0 := hd ▸ div_ne_zero (pow_ne_zero _ hg) (pow_ne_zero _ hm)
  have reduce {tt : K} {z : Fin 6 → K} (heq : normalized (weight r) i=normalized (weight z) i)
      (hp : ‖normalized (weight z) i‖*‖144*(3:K)^4*(tt^2+27)^2‖ ≤ 1)
      (f : K) (hf : ‖f‖ ≤ 1) (hscale : 144*(3:K)^4*27^2*G^6=(144*(3:K)^4*(tt^2+27)^2)*f) :
      ‖normalized (weight r) i‖ * ‖144*(3:K)^4*27^2*G^6‖ ≤ 1 := by
    rw [heq,hscale,norm_mul,←mul_assoc]
    exact (mul_le_of_le_one_right (by positivity) hf).trans hp
  by_cases hti : ‖t‖ ≤ 1
  · refine reduce rfl (chart_bound htn hd₀ hti r hr hz i) (27^2*m^4) ?_ ?_
    · rw [norm_mul,norm_pow,norm_pow]
      exact (mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) hi)).trans
        (pow_le_one₀ (norm_nonneg _) h27le)
    · rw [hd]
      field_simp [hm]
  · obtain ⟨z,hz₁,hz₂,hz₃⟩ := reciprocal_pair htn r hr hz
    let tt := 27/t
    have htt : ‖tt‖ ≤ 1 := by
      change ‖(27:K)/t‖ ≤ 1
      rw [norm_div,div_le_one (norm_pos_iff.mpr htn)]
      linarith
    have he : tt^2+27=27*G^3/n^2 := by
      dsimp [tt,t]
      field_simp [hm,hn]
      linear_combination -hid
    have hd' : tt^2+27≠0 := he ▸ div_ne_zero (mul_ne_zero h27 (pow_ne_zero _ hg)) (pow_ne_zero _ hn)
    refine reduce (tt:=tt) (hz₃ i).symm (chart_bound (div_ne_zero h27 htn) hd' htt z hz₁ hz₂ i) (n^4) ?_ ?_
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hj
    · rw [he]
      field_simp [hn]

end
end ZInQBlueprint.NonarchContact
#print axioms ZInQBlueprint.NonarchContact.pole_positive
#print axioms ZInQBlueprint.NonarchContact.denominator_pos
#print axioms ZInQBlueprint.NonarchContact.denominator_pole
#print axioms ZInQBlueprint.NonarchContact.sum_roots
#print axioms ZInQBlueprint.NonarchContact.homogeneous_bound

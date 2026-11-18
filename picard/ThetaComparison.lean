import PicardCriterion
import PicardDiscriminant
import ThetaQuotient
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Picard sextic and the height of its theta point

Streng, *Computing Igusa class polynomials*, §§2.1, 7.1, (7.1), Lemma 7.3,
uses the sum over the fifteen matchings to define I₂ and the ordinary
discriminant for I₁₀. The unscaled sixth transvectant used here is A = −I₂/120.
Thus A⁵/disc = h₁₂⁵ / ((−120)⁵ h₁₀⁶), homogeneous of degree 120 in
the sixteen theta nulls. Only h₁₀ must be nonzero. The stable-height comparison
uses Pazuki, Corollary 1.3(1), with dimension and even level both equal to two.
The uniform degree bound compares the original stable heights of the Jacobian
power and its isogenous factor after passage to a common semistable extension.

* [Streng, §2.1, (7.1), Lemma 7.3 and Remark 7.10](https://arxiv.org/pdf/0903.4766#page=18).
* [Pazuki, Corollary 1.3(1) and Definition 2.6](https://doi.org/10.24033/bsmf.2623).
* [von Känel, §2.1 and (3.1)](https://doi.org/10.1017/fms.2021.29).
-/

namespace ZOverQ.Qualitative.Picard.Theta
open Polynomial Height Height.AdmissibleAbsValues ZInQBlueprint.ThetaQuotient
open ZInQ ZInQ.QualitativeHeight
noncomputable section
variable {K : Type*} [Field K]

/-- The three matchings of four roots. -/
def matchFour (a b c d : K) : K :=
  ((a-b)*(c-d))^2 + ((a-c)*(b-d))^2 + ((a-d)*(b-c))^2

/-- Streng's I₂ in roots, grouped according to the partner of the first root. -/
def rootI2 (a : K) (r : Fin 6 → K) : K := a^2 *
  ((r 0-r 1)^2 * matchFour (r 2) (r 3) (r 4) (r 5) +
   (r 0-r 2)^2 * matchFour (r 1) (r 3) (r 4) (r 5) +
   (r 0-r 3)^2 * matchFour (r 1) (r 2) (r 4) (r 5) +
   (r 0-r 4)^2 * matchFour (r 1) (r 2) (r 3) (r 5) +
   (r 0-r 5)^2 * matchFour (r 1) (r 2) (r 3) (r 4))

set_option maxHeartbeats 3000000 in
/-- The conversion holds for arbitrary six algebraic roots, without any
separability assumption. In particular it also checks the sign. -/
theorem matchings_eq_transvectant [CharZero K] (a : K) (r : Fin 6 → K) :
    rootI2 a r = (-120) * secondInvariant
      (fun i => (C a * ∏ j : Fin 6, (X - C (r j))).coeff i.val) := by
  simp only [rootI2, matchFour, secondInvariant, coeff_C_mul, Fin.prod_univ_succ, Fin.val_zero,
    Fin.val_one, Fin.reduceSucc, Fin.isValue]
  norm_num [coeff_X_sub_C_mul, Nat.reduceAdd, mul_one, coeff_X, coeff_C]
  ring

/-- The integer labels of the even half-characteristics, in Streng's order. -/
def evens : Finset (Fin 16) := {0,1,2,3,4,6,8,9,12,15}

private def bitSum (S : Finset (Fin 16)) (i : ℕ) : ℕ := ∑ c ∈ S, (c.val / 2^i) % 2
private def integralSum (S : Finset (Fin 16)) : Bool :=
  decide (bitSum S 0 % 2 = 0 ∧ bitSum S 1 % 2 = 0 ∧
    bitSum S 2 % 2 = 0 ∧ bitSum S 3 % 2 = 0)

/-- The actual fifteen Göpel quadruples. Their characteristic sum is integral. -/
def gopel : Finset (Finset (Fin 16)) := (evens.powersetCard 4).filter (integralSum · = true)

theorem evens_card : evens.card = 10 := by decide
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem gopel_card : gopel.card = 15 := by decide

theorem complement_card {S : Finset (Fin 16)} (hS : S ∈ gopel) : (evens \ S).card = 6 := by
  have h := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1
  rw [Finset.card_sdiff_of_subset h.1, evens_card, h.2]

def h10 (x : Fin 16 → K) : K := ∏ i ∈ evens, x i ^ 2
def h12 (x : Fin 16 → K) : K := ∑ S ∈ gopel, ∏ i ∈ evens \ S, x i ^ 4
def thetaRatio (x : Fin 16 → K) : K := h12 x ^ 5 / ((-120)^5 * h10 x ^ 6)

/-- Eliminate a common weighted scaling from Streng's modular forms. -/
theorem scale_cancels [CharZero K] {U V h₁₀ h₁₂ c : K} (hc : c ≠ 0)
    (hd : h₁₀ ≠ 0) (h2 : (-120)*secondInvariant (coefficients U V) = c*h₁₂/h₁₀)
    (h10eq : discriminantValue U V = c^5*h₁₀) :
    ratio U V = h₁₂^5/((-120)^5*h₁₀^6) := by
  unfold ratio
  rw [h10eq]
  have hz := (eq_div_iff hd).mp h2
  have h5 := congrArg (fun a : K => a^5) hz
  field_simp [hc,hd]
  linear_combination -h5


/-- Uniform arithmetic–geometric mean for any subset of the coordinates. -/
private theorem subset_mean (a : Fin 16 → ℝ) (ha : ∀ i, 0 ≤ a i)
    (S : Finset (Fin 16)) {n : ℕ} (hS : S.card = n) (hn : 0<n) :
    ∏ i ∈ S, a i ≤ ((∑ i, a i)/(n : ℝ))^n := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hm := Real.geom_mean_le_arith_mean S (fun _ => (1:ℝ)) a
    (fun _ _ => zero_le_one) (by simpa [hS] using hn') (fun i _ => ha i)
  have hm' : (∏ i ∈ S, a i)^((n:ℝ)⁻¹) ≤ (∑ i ∈ S, a i)/(n:ℝ) := by
    simpa [hS] using hm
  have hsub : (∑ i ∈ S, a i) ≤ ∑ i, a i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => ha i)
  have hp := Finset.prod_nonneg (fun i (_ : i ∈ S) => ha i)
  calc
    _ = ((∏ i ∈ S, a i)^((n:ℝ)⁻¹))^n :=
        (Real.rpow_inv_natCast_pow hp (Nat.ne_of_gt hn)).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hp _)
      (hm'.trans (div_le_div_of_nonneg_right hsub hn'.le)) n

private def pair (x : Fin 16 → K) : Fin 2 → K :=
  ![h12 x ^ 5, (-120)^5 * h10 x ^ 6]

/-- The Euclidean norm absorbs both the fifteen summands and the factor 120. -/
theorem arch_bound (v : AbsoluteValue K ℝ) (x : Fin 16 → K) :
    (⨆ i, v (pair x i)) ≤ (Real.sqrt (∑ i, v (x i)^2))^120 := by
  let a (i : Fin 16) := v (x i)^2
  let T := ∑ i, a i
  have ha (i : Fin 16) : 0 ≤ a i := sq_nonneg _
  have ht : 0 ≤ T := Finset.sum_nonneg fun i _ => ha i
  have hd : v (h10 x) ≤ (T/10)^10 := by
    simpa [h10, a, T] using subset_mean a ha evens evens_card (by decide)
  have hs (S) (hS : S ∈ gopel) : v (∏ i ∈ evens \ S, x i ^ 4) ≤ (T/6)^12 := by
    let U := evens \ S
    have hp := subset_mean a ha U (complement_card hS) (by decide)
    calc
      _ = (∏ i ∈ U, a i)^2 := by
        simp only [U,a,map_prod,map_pow,Finset.prod_pow]
        ring_nf
      _ ≤ ((T/6)^6)^2 := pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => ha i) hp _
      _ = _ := by ring
  have hu : v (h12 x) ≤ 15*(T/6)^12 := calc
    _ ≤ ∑ S ∈ gopel, v (∏ i ∈ evens \ S, x i ^ 4) := v.sum_le _ _
    _ ≤ ∑ _ ∈ gopel, (T/6)^12 := Finset.sum_le_sum hs
    _ = _ := by simp [gopel_card]
  change _ ≤ (Real.sqrt T)^120
  rw [show (120 : ℕ) = 2*60 by decide, pow_mul, Real.sq_sqrt ht]
  refine ciSup_le fun i => ?_
  fin_cases i
  · change v (h12 x ^ 5) ≤ _
    rw [map_pow]
    calc
      _ ≤ (15*(T/6)^12)^5 := pow_le_pow_left₀ (v.nonneg _) hu _
      _ = ((15/(6:ℝ)^12)^5)*T^60 := by ring
      _ ≤ 1*T^60 := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg ht _)
      _ = _ := one_mul _
  · change v ((-120)^5*h10 x ^ 6) ≤ _
    rw [map_mul,map_pow,map_neg_eq_map v,map_pow]
    calc
      _ ≤ (120:ℝ)^5*((T/10)^10)^6 :=
        mul_le_mul (pow_le_pow_left₀ (v.nonneg _) (v.apply_nat_le_self 120) _)
          (pow_le_pow_left₀ (v.nonneg _) hd _) (by positivity) (by positivity)
      _ = ((120:ℝ)^5/10^60)*T^60 := by ring
      _ ≤ 1*T^60 := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg ht _)
      _ = _ := one_mul _

private theorem finite_bound (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) (x : Fin 16 → K) :
    (⨆ i, v (pair x i)) ≤ (⨆ i, v (x i)) ^ 120 := by
  let T := ⨆ i, v (x i)
  have ht : 0 ≤ T := Real.iSup_nonneg_of_nonnegHomClass v _
  have hb (S : Finset (Fin 16)) (e : ℕ) :
      v (∏ i ∈ S, (x i)^e) ≤ (T^e)^S.card := by
    rw [map_prod]
    simpa using Finset.prod_le_prod₀ (s := S) (fun i _ => v.nonneg ((x i)^e))
      (g := fun _ => T^e) (fun i _ => by
        rw [map_pow]
        exact pow_le_pow_left₀ (v.nonneg _) (Finite.le_ciSup (fun j => v (x j)) i) _)
  have h₁₀ : v (h10 x) ≤ T^20 := by
    simpa [h10,evens_card, ← pow_mul] using hb evens 2
  have h₁₂ : v (h12 x) ≤ T^24 := by
    have : Nonempty (↥gopel) := by rw [Finset.nonempty_coe_sort]; exact Finset.card_pos.mp (by rw [gopel_card]; decide)
    refine hv.apply_sum_le.trans (ciSup_le fun S => ?_)
    simpa only [complement_card S.prop, ← pow_mul] using hb (evens \ S.val) 4
  refine ciSup_le fun i => ?_
  fin_cases i
  · change v (h12 x ^ 5) ≤ T^120
    simpa [← pow_mul] using pow_le_pow_left₀ (v.nonneg _) h₁₂ 5
  · change v ((-120)^5*h10 x ^ 6) ≤ T^120
    rw [map_mul,map_pow,map_pow,map_neg_eq_map v]
    have hc : v (120:K) ≤ 1 := hv.apply_natCast_le_one (map_zero_le v 1) (map_one v) (n := 120)
    calc
      _ ≤ 1^5 * (T^20)^6 := mul_le_mul (pow_le_pow_left₀ (v.nonneg _) hc _)
        (pow_le_pow_left₀ (v.nonneg _) h₁₀ _) (by positivity) (by positivity)
      _ = _ := by ring

/-- A rational value of the actual weight-zero modular function is bounded over
every field of definition of its projective theta point, with no additive constant. -/
theorem height_of_theta [NumberField K] (x : Fin 16 → K) (R : ℚ)
    (h : (R : K) = thetaRatio x) (hd : h10 x ≠ 0) :
    ratHeight R ≤ 120 * euclideanHeight x := by
  classical
  have den : (-120:K)^5 * h10 x ^ 6 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hd)
  have hp : pair x ≠ 0 := fun h => den (congrFun h 1)
  have hx : x ≠ 0 := by rintro rfl; simp [h10,evens] at hd
  let A := ((archAbsVal (K := K)).map fun v : AbsoluteValue K ℝ =>
    Real.sqrt (∑ i, v (x i)^2)).prod
  let F := ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i)
  have ha : ((archAbsVal (K := K)).map fun v => ⨆ i, v (pair x i)).prod ≤ A^120 := by
    unfold A
    rw [← Multiset.prod_map_pow]
    exact Multiset.prod_map_le_prod_map₀ _ _ (fun v _ => Real.iSup_nonneg_of_nonnegHomClass v _)
      fun v _ => arch_bound v x
  have hf : (∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (pair x i)) ≤ F^120 := by
    unfold F
    rw [finprod_pow (by fun_prop (disch := assumption))]
    refine finprod_le_finprod₀ (by fun_prop (disch := assumption))
      (fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _) (by fun_prop (disch := assumption))
      fun v => finite_bound v.val (isNonarchimedean _ v.prop) x
  have hm : Height.mulHeight (pair x) ≤ (A*F)^120 := by
    rw [Height.mulHeight_eq hp,mul_pow]
    exact mul_le_mul ha hf (finprod_nonneg fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _)
      (by positivity)
  have hl := Real.log_le_log (Height.mulHeight_pos _) hm
  rw [Real.log_pow] at hl
  change Height.logHeight (pair x) ≤ 120*Real.log (A*F) at hl
  rw [show Height.logHeight (pair x) = Height.logHeight₁ (R:K) by
    rw [h,thetaRatio,Height.logHeight₁_div_eq_logHeight]; rfl, relative_rational_height] at hl
  have hdeg : 0 < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  unfold euclideanHeight
  simp only [hx, ↓reduceIte]
  change ratHeight R ≤ 120*(Real.log (A*F)/(Module.finrank ℚ K:ℝ))
  rw [← mul_div_assoc, le_div_iff₀ hdeg]
  linarith


private theorem product_scale {E : Type*} [Field E] (u : E) (x : Fin 16 → E)
    (S : Finset (Fin 16)) (n : ℕ) :
    (∏ i ∈ S, (u*x i)^n) = u^(n*S.card)*(∏ i ∈ S, x i ^ n) := by
  simp [mul_pow,Finset.prod_mul_distrib,pow_mul]

/-- The algebraic representative can have any nonzero projective scale. -/
theorem scale_h10_h12 {E : Type*} [Field E] (u : E) (x : Fin 16 → E) :
    h10 (fun i => u*x i) = u^20*h10 x ∧ h12 (fun i => u*x i) = u^24*h12 x := by
  constructor
  · simpa [h10,evens_card] using product_scale u x evens 2
  · unfold h12
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S hS => ?_
    simpa only [complement_card hS] using product_scale u x (evens \ S) 4

private theorem map_ratio {E : Type*} [Field E] (emb : K →+* E) (x : Fin 16 → K) :
    emb (thetaRatio x) = thetaRatio (emb ∘ x) := by
  simp [thetaRatio,h10,h12,map_ofNat]

/-- Smoothness on the whole Picard parameter chart, and the rational
invariant in that chart. This includes the ordinary value s=5. -/
theorem chart_invariants [CharZero K] (ρ : K) (hρ : ρ^2 = -3)
    (s : ℚ) (hb : primitiveBranch s ≠ 0) :
    let U := ((s:K)+ρ)^6
    let V := ((s:K)-ρ)^6
    discriminantValue U V ≠ 0 ∧ ratio U V = (igusaRatio (chart s) : ℚ) := by
  dsimp only
  let U := ((s:K)+ρ)^6
  let V := ((s:K)-ρ)^6
  have hpr : primitiveBranch s = (s.den:ℚ)^6 * branchForm s 1 := by
    unfold primitiveBranch
    rw [← Rat.mul_den_eq_num s]
    unfold branchForm
    ring
  have hv : branchForm s 1 ≠ 0 := by
    intro hz
    exact hb (by rw [hpr,hz,mul_zero])
  have hρ' : ρ ≠ 0 := by intro he; rw [he] at hρ; norm_num at hρ
  have hf : ((branchForm s 1 : ℚ):K) ≠ 0 := Rat.cast_ne_zero.mpr hv
  have hN : ((s:K)^2+3) ≠ 0 := by
    have hn : (s^2+3:ℚ) ≠ 0 := by positivity
    have hc := (Rat.cast_ne_zero (α := K)).2 hn
    push_cast at hc
    exact hc
  have hprod : U*V = ((s:K)^2+3)^6 := sixth_product _ _ hρ
  have hd : U-V = 12*ρ*((branchForm s 1 : ℚ):K) := by
    rw [show U-V = _ from sixth_difference _ ρ hρ]
    simp [branchForm]
  have hp : U*V ≠ 0 := hprod ▸ pow_ne_zero _ hN
  have hD : U-V ≠ 0 := by rw [hd]; exact mul_ne_zero (mul_ne_zero (by norm_num) hρ') hf
  have hU := left_ne_zero_of_mul hp
  have hV := right_ne_zero_of_mul hp
  change discriminantValue U V ≠ 0 ∧ ratio U V = _
  constructor
  · unfold discriminantValue
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num))
      (pow_ne_zero _ hU)) (pow_ne_zero _ hV)) (pow_ne_zero _ hD)
  · have shape : (U-V)^2/(U*V) = (27/4:K)*(chart s : K) := by
      rw [hd,hprod]
      unfold chart
      push_cast
      field_simp [hN]
      linear_combination 576*hρ
    have jn : (chart s:K) ≠ 0 := by
      intro hj
      have hh := div_ne_zero (pow_ne_zero 2 hD) hp
      exact hh (by rw [shape,hj,mul_zero])
    have id : ratio U V = (((U-V)^2/(U*V))+27)^5 / (9112500*((U-V)^2/(U*V))^3) := by
      rw [ratio,secondInvariant_eq,discriminantValue]
      field_simp [hU,hV,hD]
      ring
    rw [id,shape]
    unfold igusaRatio
    push_cast
    field_simp [jn]
    ring

/-- Streng's two weighted equations on the smooth sextic, with the weighted
scale and the independent projective scale of the algebraic theta representative. -/
structure PeriodForms (s : ℚ) (x : Fin 16 → K) (emb : K →+* ℂ) where
  ρ : ℂ
  root : ρ^2 = -3
  analytic : Fin 16 → ℂ
  projective : ℂˣ
  coordinates : ∀ i, emb (x i) = (projective:ℂ)*analytic i
  weighted : ℂˣ
  degreeTwo : -120*secondInvariant (coefficients (((s:ℂ)+ρ)^6) (((s:ℂ)-ρ)^6)) =
    (weighted:ℂ)*h12 analytic/h10 analytic
  degreeTen : discriminantValue (((s:ℂ)+ρ)^6) (((s:ℂ)-ρ)^6) = (weighted:ℂ)^5*h10 analytic

/-- For the literal rational chart, the weight-ten identity proves the
denominator is nonzero; the quadratic invariant may vanish. -/
theorem picard_invariant_height [NumberField K] {s : ℚ} (hb : primitiveBranch s ≠ 0)
    {x : Fin 16 → K} {emb : K →+* ℂ} (data : PeriodForms s x emb) :
    ratHeight (igusaRatio (chart s)) ≤ 120*euclideanHeight x := by
  obtain ⟨dn, rid⟩ := chart_invariants data.ρ data.root s hb
  have hn : h10 data.analytic ≠ 0 := by
    intro he
    exact dn (by rw [data.degreeTen,he,mul_zero])
  have eqn := (scale_cancels data.weighted.ne_zero hn data.degreeTwo data.degreeTen).symm.trans rid
  have prod := scale_h10_h12 (data.projective:ℂ) data.analytic
  have coords : emb ∘ x = fun i => (data.projective:ℂ)*data.analytic i := funext data.coordinates
  have hmap : emb (h10 x) = (data.projective:ℂ)^20*h10 data.analytic := by
    calc
      _ = h10 (emb ∘ x) := by simp [h10]
      _ = _ := by rw [coords]; exact prod.1
  have hd : h10 x ≠ 0 := by
    apply (map_ne_zero emb).mp
    rw [hmap]
    exact mul_ne_zero (pow_ne_zero _ data.projective.ne_zero) hn
  refine height_of_theta x _ ?_ hd
  apply emb.injective
  rw [map_ratCast, map_ratio,coords]
  unfold thetaRatio
  rw [prod.1,prod.2,← eqn]
  field_simp [data.projective.ne_zero,hn]


/-- The period and the sixteen theta nulls in Streng's indexing convention,
§7. The leading principal minors express positivity of the imaginary part. -/
structure SiegelMatrix where
  z11 : ℂ
  z12 : ℂ
  z22 : ℂ
  positive : 0 < z11.im
  determinant : 0 < z11.im*z22.im - z12.im^2

private def half (m : Fin 16) (i : ℕ) : ℂ := ((m.val / 2^i % 2 : ℕ):ℂ)/2

def nulls (Z : SiegelMatrix) (m : Fin 16) : ℂ := ∑' n : ℤ × ℤ,
  let p := (n.1:ℂ) + half m 2
  let q := (n.2:ℂ) + half m 3
  Complex.exp (2*Real.pi*Complex.I*((p^2*Z.z11 + 2*p*q*Z.z12 + q^2*Z.z22)/2 +
    p*half m 0 + q*half m 1))

private theorem actual_coeff [CharZero K] (U V : K) (i : Fin 7) :
    (PicardLocal.sextic U V).coeff i.val = coefficients U V i := by
  have e : PicardLocal.sextic U V = ∑ j : Fin 7, C (coefficients U V j)*X^j.val := by
    unfold PicardLocal.sextic PicardLocal.quadratic PicardLocal.quartic
    simp [coefficients, Fin.sum_univ_succ, map_ofNat]
    ring
  rw [e,finsetSum_coeff]
  fin_cases i <;> norm_num [Fin.sum_univ_succ,coeff_C_mul_X_pow]

/-- Streng §2.1 and Lemma 7.3 as the two literal equalities for the actual
split sextic at a period of its canonical principally polarized Jacobian.
The factored leading coefficient and roots only specify its polynomial.
Streng Remark 7.10 guarantees h₁₀ ≠ 0 for its reduced period. -/
def of_streng {s : ℚ} {x : Fin 16 → K} {emb : K →+* ℂ}
    (ρ : ℂ) (hρ : ρ^2 = -3) (Z : SiegelMatrix) (projective weighted : ℂˣ)
    (coords : ∀ i, emb (x i) = (projective:ℂ)*nulls Z i)
    (a : ℂ) (roots : Fin 6 → ℂ)
    (split : PicardLocal.sextic (((s:ℂ)+ρ)^6) (((s:ℂ)-ρ)^6) =
      C a * ∏ j, (X - C (roots j)))
    (two : rootI2 a roots = (weighted:ℂ)*h12 (nulls Z)/h10 (nulls Z))
    (ten : (PicardLocal.sextic (((s:ℂ)+ρ)^6) (((s:ℂ)-ρ)^6)).discr =
      (weighted:ℂ)^5 * h10 (nulls Z)) : PeriodForms s x emb := by
  refine ⟨ρ,hρ,nulls Z,projective,coords,weighted,?_,?_⟩
  · rw [matchings_eq_transvectant,←split] at two
    simpa only [actual_coeff] using two
  · have hs : ((s:ℂ)^2+3) ≠ 0 := by
      have hq : s^2+3 ≠ 0 := by positivity
      exact_mod_cast hq
    have hp := sixth_product (s:ℂ) ρ hρ
    have hv := right_ne_zero_of_mul (hp.trans_ne (pow_ne_zero 6 hs))
    rwa [discr_sextic _ _ hv] at ten


/-- The inequality of Pazuki Cor. 1.3(1), with its original
weight, level and archimedean norm. Here H is the original stable Faltings
height. Pazuki's Deligne height in genus two is H + log π. -/
def PazukiAt (θ H : ℝ) : Prop :=
  |θ - (H + Real.log Real.pi)/2| ≤ 96*Real.log 16 * Real.log (max θ 1 + 2)

/-- The price of the fixed isogeny J^r → B (or B → J^r). The upper bound
passes from the stable height of B to J in either orientation. The explicit
affine constants use the tangent line to log at 1024. -/
theorem theta_of_isogeny {θ H B : ℝ} {r D : ℕ} (hr : 0<r) (hD : 0<D)
    (pazuki : PazukiAt θ H) (isogeny : |(r:ℝ)*H-B| ≤ Real.log D/2) :
    θ ≤ (7/10)*max 1 B + (7/20)*Real.log D + 2410 := by
  have hM : (1:ℝ) ≤ max 1 B := le_max_left _ _
  have hMB : B ≤ max 1 B := le_max_right _ _
  have hL : 0 ≤ Real.log (D:ℝ) := Real.log_nonneg (by exact_mod_cast hD : (1:ℝ) ≤ D)
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  have im := (le_abs_self ((r:ℝ)*H-B)).trans isogeny
  have hf : H ≤ max 1 B + Real.log D/2 := by
    by_cases hn : 0 ≤ H
    · linarith [mul_le_mul_of_nonneg_right hr' hn]
    · linarith
  have l16 : Real.log 16 ≤ 3 := by
    rw [show (16:ℝ) = 2^4 by norm_num,Real.log_pow]
    push_cast
    linarith only [Real.log_two_lt_d9]
  have l4 : Real.log 4 ≤ 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]
    push_cast
    linarith only [Real.log_two_lt_d9]
  have lπ := (Real.log_le_log Real.pi_pos Real.pi_lt_four.le).trans l4
  by_cases hx : θ ≤ 1
  · linarith
  have ht : 1 ≤ θ := le_of_lt (lt_of_not_ge hx)
  have l1024 : Real.log 1024 ≤ 7 := by
    rw [show (1024:ℝ) = 2^10 by norm_num,Real.log_pow]
    push_cast
    linarith only [Real.log_two_lt_d9]
  have tangent := Real.log_le_sub_one_of_pos (show 0 < (θ+2)/1024 by linarith)
  rw [Real.log_div (by linarith) (by norm_num)] at tangent
  have hz : 0 ≤ Real.log (θ+2) := Real.log_nonneg (by linarith)
  have hc : 96*Real.log 16 ≤ 288 := by linarith
  have p := (le_abs_self (θ - (H + Real.log Real.pi)/2)).trans pazuki
  rw [max_eq_left ht] at p
  linarith [mul_le_mul_of_nonneg_right hc hz]

/-- The actual Picard ratio satisfies exactly the form of the comparison
required by PicardCriterion. D bounds the degree uniformly on the chosen open. -/
theorem invariant_of_isogeny [NumberField K] {s : ℚ} (hb : primitiveBranch s ≠ 0)
    {x : Fin 16 → K} {emb : K →+* ℂ} (period : PeriodForms s x emb)
    {H B : ℝ} {r D : ℕ} (hr : 0<r) (hD : 0<D)
    (pazuki : PazukiAt (euclideanHeight x) H) (isogeny : |(r:ℝ)*H-B| ≤ Real.log D/2) :
    ratHeight (igusaRatio (chart s)) ≤ 84 * max 1 B + (42 * Real.log D + 289200) := by
  linarith only [picard_invariant_height hb period, theta_of_isogeny hr hD pazuki isogeny]

/-- All classical data at one rational Picard parameter, allowing a different
number field, period, height and multiplicity at every fibre. Only the uniform
upper bound D on the isogeny degrees is common to the family. -/
def FibreAt (s : ℚ) (B : ℝ) (D : ℕ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (emb : L →+* ℂ) (x : Fin 16 → L)
    (H : ℝ) (r : ℕ), 0<r ∧ Nonempty (PeriodForms s x emb) ∧
      PazukiAt (euclideanHeight x) H ∧ |(r:ℝ)*H-B| ≤ Real.log D/2

theorem comparison_of_fibre {s : ℚ} {B : ℝ} {D : ℕ} (hb : primitiveBranch s ≠ 0)
    (hD : 0<D) (fibre : FibreAt s B D) :
    ratHeight (igusaRatio (chart s)) ≤ 84 * max 1 B + (42 * Real.log D + 289200) := by
  obtain ⟨L,fieldL,numberL,emb,x,H,r,hr,⟨forms⟩,hp,hi⟩ := fibre
  exact invariant_of_isogeny hb forms hr hD hp hi

/-- The same GL₂-factor height is used in both the isogeny estimate and the
effective Shafarevich input. Rational exceptional fibres may be discarded
before producing the single integer polynomial. -/
theorem integer_polynomial_of_periods (g D : ℕ) (hD : 0<D)
    (fixed : Finset ℕ) (except : Finset ℚ) (bad : ℚ → Finset ℕ) (B : ℚ → ℝ)
    (fixedPrimes : ∀ p ∈ fixed, p.Prime)
    (support : ∀ s : ℚ, s ∉ except → primitiveBranch s ≠ 0 →
      ∀ p ∈ bad s, p.Prime ∧ (p ∈ fixed ∨ Odd (padicValRat p (primitiveBranch s))))
    (effective : ∀ s : ℚ, s ∉ except → primitiveBranch s ≠ 0 →
      B s ≤ vonKanelBound g (bad s))
    (periods : ∀ s : ℚ, s ∉ except → primitiveBranch s ≠ 0 → FibreAt s (B s) D)
    (tian : ZInQBlueprint.OriginalRank.PublishedGenusRows.PublishedTian47)
    (grossZagier : ZOverQ.Bounded.SimpleZeroRank) : ZOverQ.Qualitative.IntegerPolynomial := by
  exact integer_polynomial_of_fibre_estimates g fixed except bad B
    (a:=84) (b:=42*Real.log D+289200) (by norm_num) fixedPrimes support effective
    (fun s hs hb => comparison_of_fibre hb hD (periods s hs hb)) tian grossZagier

end
end ZOverQ.Qualitative.Picard.Theta
#print axioms ZOverQ.Qualitative.Picard.Theta.matchings_eq_transvectant
#print axioms ZOverQ.Qualitative.Picard.Theta.gopel_card
#print axioms ZOverQ.Qualitative.Picard.Theta.complement_card
#print axioms ZOverQ.Qualitative.Picard.Theta.scale_cancels
#print axioms ZOverQ.Qualitative.Picard.Theta.arch_bound
#print axioms ZOverQ.Qualitative.Picard.Theta.height_of_theta
#print axioms ZOverQ.Qualitative.Picard.Theta.scale_h10_h12
#print axioms ZOverQ.Qualitative.Picard.Theta.chart_invariants
#print axioms ZOverQ.Qualitative.Picard.Theta.picard_invariant_height
#print axioms ZOverQ.Qualitative.Picard.Theta.theta_of_isogeny
#print axioms ZOverQ.Qualitative.Picard.Theta.invariant_of_isogeny
#print axioms ZOverQ.Qualitative.Picard.Theta.of_streng
#print axioms ZOverQ.Qualitative.Picard.Theta.comparison_of_fibre
#print axioms ZOverQ.Qualitative.Picard.Theta.integer_polynomial_of_periods

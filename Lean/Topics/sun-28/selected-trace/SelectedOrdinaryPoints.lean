import SelectedRationalTrace
import RatioConsequences
import UnconditionalOrdinaryCharts

/-! The two formal anchors imply all sixteen selected-prime leaf tests for
the same nine points. -/
namespace Sun28.SelectedTrace
open ZInQ ZInQ.Mult Sun28.Scalar Sun28.ScalarTrace Sun28.Ordinary Sun28.Forward Sun28.WitnessIndices
open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section

/-- The inverse abscissa has positive order throughout the genuine formal
neighborhood, including the point at infinity. -/
theorem reciprocal_of_formal {K : Type*} [Field K] [DecidableEq K]
    (v : AddValuation K (WithTop ℤ)) {b : K} {Q : (curve b).Point} (formal : Q∈W1 v b) :
    (1:WithTop ℤ)≤v (reciprocal Q) := by
  cases Q with
  | zero => simp [reciprocal]
  | some x y on =>
    change v x<0 at formal
    have nz : x≠0 := by rintro rfl; rw [v.map_zero] at formal; exact (not_lt_of_ge le_top) formal
    obtain ⟨d,hd⟩ := finite_order v nz
    have neg : d<0 := WithTop.coe_lt_coe.mp (hd ▸ formal)
    change (1:WithTop ℤ)≤v x⁻¹
    rw [val_inv_coe hd]
    exact WithTop.coe_le_coe.mpr (show (1:ℤ)≤ -d by omega)

variable {p : ℕ} [hp : Fact p.Prime] (large : 65<p) (w : HeightOneSpectrum (𝓞 K0))
    [lies : w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,hp.out⟩).asIdeal]
include large lies

/-- All integer multiples of a formal anchor have positive reciprocal order.
Their degree-64 logarithm ratios recover the multiplying integer modulo
the 64th power at the same place. -/
theorem formal_multiple_tests (τ : K0 ≃ₐ[ℚ] K0) (h : ℤ) (hh : h≠0)
    (formal : h • paperGenerator sqrt2_sq ∈ W1 ((discreteOrder (w.valuation K0)).comap τ.toRingHom) (-(3-sqrt2)^2))
    (n : ℤ) :
    (1:WithTop ℤ)≤discreteOrder (w.valuation K0) (τ (reciprocal ((h*n) • paperGenerator sqrt2_sq))) ∧
    Near (discreteOrder (w.valuation K0)) 64 (τ (ordinaryRatio (paperGenerator sqrt2_sq) (h*n) h)) n := by
  let u:=discreteOrder (w.valuation K0)
  let v:=u.comap τ.toRingHom
  have hb := (good_scalar_prime (by omega : 2<p) (by omega : p≠7) w τ sqrt2_sq).2.1
  have multi : (h*n) • paperGenerator sqrt2_sq ∈ W1 v (-(3-sqrt2)^2) := by
    rw [mul_comm h n,mul_zsmul]
    exact (zsmul_mem_W1 hb formal n).1
  have num := reciprocal_of_formal v multi
  have approx := ordinary_relative_ratio64 large w sqrt2_sq (Sun28.ShortFormal.ordinaryFormalChart p w) τ
    (h*n) h hh num (reciprocal_of_formal v formal)
  have hn : (h:K0)≠0 := by exact_mod_cast hh
  have exactq : ((h*n:ℤ):K0)/(h:K0)=(n:K0) := by push_cast; field_simp
  rw [exactq] at approx
  exact ⟨num,approx.2.2 (integral_int u n)⟩

/-- The ten point tests, four differences, Lucas test and beta test hold
at one prime, using only the two formal anchors. -/
theorem sixteen_from_formal (c h : ℤ) (n : Fin 4→ℤ) (β : ℚ)
    (hh : h≠0) (hc : h-c≠0) (root : lucas (n 1) (n 2) (n 3)=0) (firstRoot : β=(n 0:ℚ))
    (plus : h • paperGenerator sqrt2_sq ∈ W1 (discreteOrder (w.valuation K0)) (-(3-sqrt2)^2))
    (minus : (h-c) • paperGenerator sqrt2_sq ∈
      W1 ((discreteOrder (w.valuation K0)).comap conjugation.toRingHom) (-(3-sqrt2)^2)) :
    ∀ i, (orderRequired i:WithTop ℤ) ≤ discreteOrder (w.valuation K0)
      (ordinaryTests sqrt2_sq conjugation c h n (fun i=>h*n i) β i) := by
  let u:=discreteOrder (w.valuation K0)
  have first (i : Fin 4) := formal_multiple_tests large w 1 h hh plus (n i)
  have second (i : Fin 4) := formal_multiple_tests large w conjugation (h-c) hc minus (n i)
  have hp' := reciprocal_of_formal u plus
  have hm := reciprocal_of_formal (u.comap conjugation.toRingHom) minus
  intro i
  cases i with
  | h => exact hp'
  | u i => exact (first i).1
  | v₀ => exact hm
  | v i =>
    simpa only [ordinaryTests,orderRequired,Nat.cast_one,sub_mul] using (second i).1
  | difference i =>
    have e := ((first i).2).sub u (second i).2
    simpa only [ordinaryTests,orderRequired,Near,AlgEquiv.one_apply,sub_self,Int.cast_zero,sub_zero,sub_mul] using e
  | delta =>
    have e := lucas_congruence u (first 1).2 (first 2).2 (first 3).2
    simpa only [ordinaryTests,orderRequired,Near,AlgEquiv.one_apply,root,Int.cast_zero,sub_zero] using e
  | beta =>
    change (16:WithTop ℤ)≤u (ordinaryRatio (paperGenerator sqrt2_sq) (h*n 0) h-algebraMap ℚ K0 β)
    rw [firstRoot,map_intCast]
    exact (by decide : (16:WithTop ℤ)≤64).trans (first 0).2

/-- The selected-prime endpoint on the stated nine points with m_i=h n_i.
The two anchors belong to the two indicated elliptic formal neighborhoods;
all sixteen valuations are conclusions. -/
theorem selected_ordinary_pole_of_formal {points : NinePoints} {M : ℕ} {c q h : ℤ} {n : Fin 4→ℤ}
    (represented : Consequences points M c ⟨q,h,n,fun i=>h*n i⟩)
    (β A t : ℚ) (root : lucas (n 1) (n 2) (n 3)=0) (firstRoot : β=(n 0:ℚ))
    (plus : h • paperGenerator sqrt2_sq ∈ W1 (discreteOrder (w.valuation K0)) (-(3-sqrt2)^2))
    (minus : (h-c) • paperGenerator sqrt2_sq ∈
      W1 ((discreteOrder (w.valuation K0)).comap conjugation.toRingHom) (-(3-sqrt2)^2))
    (detect : padicValRat p (detector A t)=1) (guard : t≠3) (unit : padicValRat p (t-3)=0) :
    let T:=ordinaryTraceAt points M c β A t
    T≠0 ∧ padicValRat p T=0 ∧ padicValRat p (detector A t/T^2)=1 := by
  apply selected_ordinary_pole (by omega : 2<p) w points M c β A t detect guard unit
  rw [← ordinaryAt_eq represented]
  exact sixteen_from_formal large w c h n β represented.h_nonzero represented.base_nonzero root firstRoot plus minus

end
end Sun28.SelectedTrace
#print axioms Sun28.SelectedTrace.reciprocal_of_formal
#print axioms Sun28.SelectedTrace.formal_multiple_tests
#print axioms Sun28.SelectedTrace.sixteen_from_formal
#print axioms Sun28.SelectedTrace.selected_ordinary_pole_of_formal

import SelectedProductResidue
import PoleParameters

/-! Selected-prime orders for Sun's ordinary trace on the actual nine points. -/
namespace Sun28.SelectedTrace
open ZInQ Sun28.Scalar Sun28.ScalarTrace Sun28.Ordinary Sun28.Forward Sun28.WitnessIndices
open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section

/-- On one actual prime of ℚ(√2), success of the ordinary leaves gives both
the rational trace guard and the exact rational pole order. The coordinate
normalizer t−3 can be any nonzero rational p-adic unit. -/
theorem selected_ordinary_pole {p : ℕ} [hp : Fact p.Prime] (odd : 2<p)
    (w : HeightOneSpectrum (𝓞 K0))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,hp.out⟩).asIdeal]
    (points : NinePoints) (M : ℕ) (c : ℤ) (β A t : ℚ)
    (detect : padicValRat p (detector A t)=1) (guard : t≠3) (unit : padicValRat p (t-3)=0)
    (success : ∀ i, (orderRequired i:WithTop ℤ) ≤ discreteOrder (w.valuation K0) (ordinaryAt points M c β i)) :
    let T:=ordinaryTraceAt points M c β A t
    T≠0 ∧ padicValRat p T=0 ∧ padicValRat p (detector A t/T^2)=1 := by
  let v := (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,hp.out⟩
  have name : (Rat.HeightOneSpectrum.primesEquiv v).1=p :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).apply_symm_apply ⟨p,hp.out⟩)
  have unram := sqrtTwo_unramified sqrt2_sq v w name odd
  let u:=discreteOrder (w.valuation K0)
  have base {q : ℚ} (nq : q≠0) : u (algebraMap ℚ K0 q)=((padicValRat p q:ℤ):WithTop ℤ) := by
    simpa [u,name,unram] using prime_order_rat v w nq
  have r0 : detector A t≠0 := by intro h; simp [h] at detect
  have rone : u (algebraMap ℚ K0 (detector A t))=1 := by rw [base r0,detect]; rfl
  have sun : u (algebraMap ℚ K0 (t-3))=0 := by rw [base (sub_ne_zero.mpr guard),unit]; rfl
  have two : u (2:K0)=0 := by
    have no2 : ¬p∣2 := fun e => (Nat.not_lt_of_ge (Nat.le_of_dvd (by decide) e)) odd
    have h : padicValRat p (2:ℚ)=0 := by
      simpa [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd no2] using (padicValRat.of_nat (p:=p) (n:=2))
    simpa [h,map_ofNat] using base (q:=2) (by norm_num)
  let T:=ordinaryTraceAt points M c β A t
  have vt : u (algebraMap ℚ K0 T)=0 := by
    apply ordinary_trace_unit u conjugation conjugation_nontrivial (detector A t) rone two
    left
    intro i
    simpa only [u.map_div,u.map_pow,sun,nsmul_zero,sub_zero] using success i
  have tn : T≠0 := by intro bad; rw [bad,map_zero,u.map_zero] at vt; exact WithTop.top_ne_coe vt
  have val : padicValRat p T=0 := WithTop.coe_inj.mp ((base tn).symm.trans vt)
  refine ⟨tn,val,?_⟩
  rw [padicValRat.div r0 (pow_ne_zero _ tn),padicValRat.pow,detect,val]
  norm_num

end
end Sun28.SelectedTrace
#print axioms Sun28.SelectedTrace.selected_ordinary_pole

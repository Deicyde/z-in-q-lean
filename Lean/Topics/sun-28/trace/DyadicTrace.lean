import PrimeTrace
import PreparedTrace

/-! The normalized trace is a rational dyadic unit under local preparation, also at a ramified prime. -/
namespace Sun28.ScalarTrace
open IsDedekindDomain NumberField
open scoped NumberField

/-- Local preparation in the ideal (2) on both conjugate branches implies that
the rational normalized trace is 1 modulo 2. The ramification index is unrestricted. -/
theorem dyadic_scalarTheta {K : Type*} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]
    (v : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver v.asIdeal]
    (hname : (Rat.HeightOneSpectrum.primesEquiv v).1=2)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ≠1) {r : ℚ} (hr : 0≤padicValRat 2 r) {x y : K}
    (hx : discreteOrder (w.valuation K) (2:K) ≤ discreteOrder (w.valuation K) (x/algebraMap ℚ K r))
    (hy : discreteOrder (w.valuation K) (2:K) ≤ discreteOrder (w.valuation K) (y/algebraMap ℚ K r^48))
    (hx' : discreteOrder (w.valuation K) (2:K) ≤ discreteOrder (w.valuation K) (σ x/algebraMap ℚ K r))
    (hy' : discreteOrder (w.valuation K) (2:K) ≤ discreteOrder (w.valuation K) (σ y/algebraMap ℚ K r^48)) :
    scalarTheta r x y ≠ 0 ∧ padicValRat 2 (scalarTheta r x y)=0 ∧
    (scalarTheta r x y=1 ∨ 1≤padicValRat 2 (scalarTheta r x y-1)) := by
  let u := discreteOrder (w.valuation K)
  let e : ℤ := w.asIdeal.ramificationIdx (𝓞 ℚ)
  have he : 0<e := by
    dsimp [e]
    exact_mod_cast (Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal v.ne_bot)
  have base {a : ℚ} (ha : a≠0) : u (algebraMap ℚ K a)=((e*padicValRat 2 a:ℤ):WithTop ℤ) := by
    simpa [u,e,hname] using prime_order_rat v w ha
  have ht : u (2:K)=(e:WithTop ℤ) := by
    have hh : padicValRat 2 (2:ℚ)=1 := padicValRat.self (p:=2) (by decide)
    have h := base (a:=2) (by norm_num)
    rw [hh,mul_one,map_ofNat] at h
    exact h
  have hInt : (0:WithTop ℤ) ≤ u (algebraMap ℚ K r) := by
    rcases eq_or_ne r 0 with rfl | hz
    · simp
    rw [base hz]
    exact WithTop.coe_le_coe.mpr (mul_nonneg he.le hr)
  obtain ⟨congr,unit⟩ := prepared_scalarTheta u σ hσ he (le_refl e) ht hInt
    (ht ▸ hx) (ht ▸ hy) (ht ▸ hx') (ht ▸ hy')
  have nonzero : scalarTheta r x y ≠ 0 := by
    intro h
    rw [h,map_zero,u.map_zero] at unit
    exact WithTop.top_ne_coe unit
  refine ⟨nonzero,?_,?_⟩
  · rw [base nonzero] at unit
    have hh : e*padicValRat 2 (scalarTheta r x y)=0 := WithTop.coe_inj.mp unit
    exact (mul_eq_zero.mp hh).resolve_left (ne_of_gt he)
  · rcases eq_or_ne (scalarTheta r x y) 1 with eq | ne
    · exact Or.inl eq
    right
    have nz := sub_ne_zero.mpr ne
    rw [←map_one (algebraMap ℚ K),←map_sub,base nz] at congr
    have hh := WithTop.coe_le_coe.mp congr
    by_contra! h
    have hn : padicValRat 2 (scalarTheta r x y-1) ≤ 0 := by omega
    have hm := mul_nonpos_of_nonneg_of_nonpos he.le hn
    omega

end Sun28.ScalarTrace
#print axioms Sun28.ScalarTrace.dyadic_scalarTheta

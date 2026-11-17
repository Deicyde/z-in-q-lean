import QuadraticAverage
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Valuation

/-! Additive orders of actual height-one primes and their restriction to the rationals. -/
namespace Sun28.ScalarTrace
open IsDedekindDomain NumberField WithZero
open scoped NumberField

private noncomputable def negLog (a : ℤᵐ⁰) : WithTop ℤ :=
  if a=0 then ⊤ else ((-WithZero.log a : ℤ) : WithTop ℤ)

private theorem negLog_anti : Antitone negLog := by
  intro a b h
  rcases eq_or_ne a 0 with rfl | ha
  · simp [negLog]
  have hb : b≠0 := ((lt_of_le_of_ne zero_le ha.symm).trans_le h).ne'
  simp only [negLog,ite_eq_right ha,ite_eq_right hb,WithTop.coe_le_coe,neg_le_neg_iff]
  exact (WithZero.log_le_log ha hb).mpr h

/-- The additive normalization of a multiplicative discrete valuation, with order of zero infinite. -/
noncomputable def discreteOrder {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰) :
    AddValuation K (WithTop ℤ) :=
  AddValuation.of (fun a => negLog (v a)) (by simp [negLog]) (by simp [negLog])
    (fun a b => by
      have h := negLog_anti (v.map_add a b)
      simpa only [negLog_anti.map_max] using h)
    (fun a b => by
      rcases eq_or_ne a 0 with rfl | ha
      · simp [negLog]
      rcases eq_or_ne b 0 with rfl | hb
      · simp [negLog]
      have h₁ := (Valuation.ne_zero_iff v).mpr ha
      have h₂ := (Valuation.ne_zero_iff v).mpr hb
      simp [negLog,v.map_mul,h₁,h₂,mul_ne_zero h₁ h₂,WithZero.log_mul h₁ h₂,add_comm])

/-- A fixed integral base prime has the same normalization as the rational p-adic valuation. -/
theorem rationalPrime_value (v : HeightOneSpectrum (𝓞 ℚ)) {q : ℚ} (hq : q≠0) :
    v.valuation ℚ q = WithZero.exp (-padicValRat (Rat.HeightOneSpectrum.primesEquiv v).1 q) := by
  let p : ℕ := (Rat.HeightOneSpectrum.primesEquiv v).1
  let _ : Fact p.Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  let φ := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have ideal : v.asIdeal = Ideal.span {(p:𝓞 ℚ)} := by
    have h : v.asIdeal.map φ = (Ideal.span {(p:𝓞 ℚ)}).map φ := by
      rw [Ideal.map_span,Set.image_singleton,map_natCast]
      exact (Rat.HeightOneSpectrum.span_natGenerator v).symm
    simpa [Ideal.comap_map_of_bijective _ φ.bijective] using congrArg (Ideal.comap φ) h
  have hp₀ : (p:𝓞 ℚ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpv : v.valuation ℚ (p:ℚ) = WithZero.exp (-1:ℤ) := by
    simpa [HeightOneSpectrum.valuation_of_algebraMap] using
      (v.valuation_of_algebraMap (K:=ℚ) (p:𝓞 ℚ)).trans (v.intValuation_singleton hp₀ ideal)
  let n := padicValRat p q
  have hev : (v.valuation ℚ).IsEquiv (Rat.padicValuation p) :=
    Rat.HeightOneSpectrum.valuation_equiv_padicValuation v
  have hpow : (WithZero.exp (-1:ℤ))^n = WithZero.exp (-n) := by rw [←WithZero.exp_zsmul]; simp
  have heq : v.valuation ℚ q = v.valuation ℚ ((p:ℚ)^n) := by
    apply hev.eq_iff.mpr
    rw [map_zpow₀,Rat.padicValuation_self,hpow]
    simp [Rat.padicValuation,hq,n]
  rw [heq,map_zpow₀,hpv,hpow]

/-- The order of a nonzero rational element is exactly the ramification index times
its rational p-adic order. This also covers the dyadic ramified prime. -/
theorem prime_order_rat {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver v.asIdeal]
    {q : ℚ} (hq : q≠0) :
    discreteOrder (w.valuation K) (algebraMap ℚ K q) =
      (((w.asIdeal.ramificationIdx (𝓞 ℚ):ℤ)*padicValRat (Rat.HeightOneSpectrum.primesEquiv v).1 q:
          ℤ):WithTop ℤ) := by
  change negLog (w.valuation K (algebraMap ℚ K q)) = _
  rw [←HeightOneSpectrum.valuation_liesOver K v w, rationalPrime_value v hq]
  simp [negLog,←WithZero.exp_nsmul]

/-- At a positive contact, a unit numerator and an integral coefficient give
the required unit front factor. -/
theorem front_unit {K : Type*} [Field K] (w : AddValuation K (WithTop ℤ))
    {r Γ D₀ : K} {α : ℤ} (ha : 0<α) (hr : w r=(α:WithTop ℤ))
    (hg : w Γ=0) (hD : (0:WithTop ℤ) ≤ w D₀) :
    w (Γ/(1+D₀*r^2))=0 := by
  have hR : (0:WithTop ℤ) < w (D₀*r^2) := by
    rw [w.map_mul,w.map_pow,hr,two_nsmul]
    calc
      (0:WithTop ℤ) < (α:WithTop ℤ)+(α:WithTop ℤ) := WithTop.coe_lt_coe.mpr (show (0:ℤ) < α+α by omega)
      _ ≤ w D₀+((α:WithTop ℤ)+(α:WithTop ℤ)) := le_add_of_nonneg_left hD
  have hu := w.map_add_eq_of_lt_left (x:=(1:K)) (y:=D₀*r^2) (by rw [w.map_one]; exact hR)
  rw [w.map_div,hu,w.map_one,hg,sub_zero]

/-- Both sharp test orders hold at the same branch of an actual unramified
number-field prime. The scalar pole is tested by its ordinary rational order.
The front-factor unit follows from the stated constant and contact conditions. -/
theorem unramified_two_tests {K : Type*} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]
    (v : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver v.asIdeal]
    (unramified : w.asIdeal.ramificationIdx (𝓞 ℚ)=1)
    {p : ℕ} (hname : (Rat.HeightOneSpectrum.primesEquiv v).1=p) (hp : 2<p)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ≠1) {r Γ : ℚ} (D₀ : ℕ) {x y : K}
    (hr : 0<padicValRat p r) (ho : Odd (padicValRat p r))
    (hgn : Γ ≠ 0) (hg : padicValRat p Γ=0) (hn : scalarTheta r x y ≠ 0)
    (hpole : 0≤padicValRat p (scalarValue r Γ D₀ x y)) :
    Precise (discreteOrder (w.valuation K)) (padicValRat p r) x y ∨
    Precise (discreteOrder (w.valuation K)) (padicValRat p r) (σ x) (σ y) := by
  let u := discreteOrder (w.valuation K)
  have base {a : ℚ} (ha : a≠0) :
      u (algebraMap ℚ K a) = ((padicValRat p a : ℤ):WithTop ℤ) := by
    simpa [u,unramified,hname] using prime_order_rat v w ha
  have hrn : r≠0 := by rintro rfl; simp at hr
  have hv2 : u (2:K)=0 := by
    have h2p : ¬p ∣ 2 := fun h => (Nat.not_lt_of_ge (Nat.le_of_dvd (by decide) h)) hp
    have ht : padicValRat p (2:ℚ)=0 := by
      simpa [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd h2p] using (padicValRat.of_nat (p:=p) (n:=2))
    simpa [ht,map_ofNat] using base (a:=2) (by norm_num)
  have hD : (0:WithTop ℤ) ≤ u (algebraMap ℚ K (D₀:ℚ)) := by
    rcases eq_or_ne D₀ 0 with rfl | hd
    · simp
    rw [base (by exact_mod_cast hd)]
    exact WithTop.coe_le_coe.mpr (zero_le_padicValRat_of_nat (p:=p) D₀)
  have unit : u (algebraMap ℚ K (Γ/(1+D₀*r^2)))=0 := by
    have hga : u (algebraMap ℚ K Γ)=0 := by rw [base hgn,hg]; rfl
    simpa only [map_div₀,map_add,map_one,map_mul,map_pow] using
      front_unit u hr (base hrn) hga hD
  have hvn : Γ/(1+D₀*r^2)≠0 := by
    intro hz
    rw [hz,map_zero,u.map_zero] at unit
    exact WithTop.top_ne_coe unit
  have bn : scalarValue r Γ D₀ x y≠0 :=
    div_ne_zero (mul_ne_zero (pow_ne_zero _ hvn) hrn) (pow_ne_zero _ hn)
  have integral : (0:WithTop ℤ) ≤ u (algebraMap ℚ K (scalarValue r Γ D₀ x y)) := by
    rw [base bn]
    exact WithTop.coe_le_coe.mpr hpole
  exact (two_tests_sharp u σ hσ (base hrn) ho hv2 unit hn integral).2

end Sun28.ScalarTrace
#print axioms Sun28.ScalarTrace.rationalPrime_value
#print axioms Sun28.ScalarTrace.prime_order_rat
#print axioms Sun28.ScalarTrace.front_unit
#print axioms Sun28.ScalarTrace.unramified_two_tests

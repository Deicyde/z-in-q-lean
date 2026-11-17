import DyadicGeneratorDepth
import OddPrimeIndex

/-! Infinite order of Sun's displayed point from its dyadic abscissa, and the
odd-contact theorem with only formal comparison left on the elliptic side. -/
namespace Sun28.Scalar
open Sun28.ScalarTrace IsDedekindDomain NumberField WeierstrassCurve.Affine
open scoped NumberField
variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]

omit [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K] in
/-- The reciprocal abscissa of the displayed generator has order 3e at every
dyadic prime, where e is the order of 2. -/
theorem generator_dyadic_abscissa {ρ : K} (root : ρ^2=2)
    (v : HeightOneSpectrum (𝓞 ℚ)) (name : (Rat.HeightOneSpectrum.primesEquiv v).1=2)
    (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver v.asIdeal] :
    ∃ (e : ℤ), 0<e ∧ discreteOrder (w.valuation K) (2:K)=(e:WithTop ℤ) ∧
      0≤discreteOrder (w.valuation K) (-(3-ρ)^2) ∧
      discreteOrder (w.valuation K) (generatorX ρ)⁻¹=((3*e:ℤ):WithTop ℤ) := by
  let u := discreteOrder (w.valuation K)
  let e : ℤ := w.asIdeal.ramificationIdx (𝓞 ℚ)
  have he : 0<e := by
    dsimp [e]
    exact_mod_cast (Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal v.ne_bot)
  have h2 : u (2:K)=(e:WithTop ℤ) := by
    have h := prime_order_rat v w (q:=2) (by norm_num)
    have hself : padicValRat 2 (2:ℚ)=1 := padicValRat.self (p:=2) (by decide)
    rw [name,hself,mul_one,map_ofNat] at h
    exact h
  have natInt (k:ℕ) : (0:WithTop ℤ) ≤ u (k:K) := by
    induction k with
    | zero => simp
    | succ k ik =>
      rw [Nat.cast_succ]
      exact u.map_le_add ik (by simp)
  have nzrho : ρ≠0 := by rintro rfl; norm_num at root
  obtain ⟨t,ht⟩ := finite_order u nzrho
  have eq := congrArg u root
  rw [u.map_pow,ht,h2] at eq
  have te : 2*t=e := by exact_mod_cast eq
  have rhoInt : (0:WithTop ℤ) ≤ u ρ := ht ▸ WithTop.coe_le_coe.mpr (show 0≤t by omega)
  have bInt : (0:WithTop ℤ) ≤ u (-(3-ρ)^2) := by
    rw [u.map_neg,u.map_pow,two_nsmul]
    have h := u.map_le_sub (natInt 3) rhoInt
    exact add_nonneg h h
  have uInt : (0:WithTop ℤ)≤u (14*(2-ρ)) := by
    rw [u.map_mul]
    exact add_nonneg (natInt 14) (u.map_le_sub (natInt 2) rhoInt)
  have high : (0:WithTop ℤ) < u (2*(14*(2-ρ))) := by
    rw [u.map_mul,h2]
    exact (WithTop.coe_lt_coe.mpr he).trans_le (le_add_of_nonneg_right uInt)
  have nunit : u (57-28*ρ)=0 := by
    rw [show (57:K)-28*ρ=1+2*(14*(2-ρ)) by ring]
    rw [u.map_add_eq_of_lt_left (x:=(1:K)) (y:=2*(14*(2-ρ))) (by rw [u.map_one]; exact high),u.map_one]
  have h8 : u (8:K)=((3*e:ℤ):WithTop ℤ) := by
    rw [show (8:K)=2^3 by norm_num,u.map_pow,h2]
    exact_mod_cast (show 3 • e=3*e by simp)
  have hx : generatorX ρ=(57-28*ρ)/8 := by unfold generatorX; ring
  refine ⟨e,he,h2,bInt,?_⟩
  change u (generatorX ρ)⁻¹=_
  rw [hx,u.map_inv,u.map_div,nunit,h8,zero_sub,neg_neg]

omit [Algebra.IsQuadraticExtension ℚ K] in
/-- Sun's displayed point has infinite order. The proof chooses a dyadic prime
by lying-over and builds an infinite sequence of distinct doubles. -/
theorem paperGenerator_infinite {ρ : K} (root : ρ^2=2) :
    addOrderOf (paperGenerator root)=0 := by
  let v := (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨2,Nat.prime_two⟩
  have name : (Rat.HeightOneSpectrum.primesEquiv v).1=2 :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).apply_symm_apply ⟨2,Nat.prime_two⟩)
  obtain ⟨W,hmax,lies⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S:=𝓞 K) v.asIdeal
  let _ : W.LiesOver v.asIdeal := lies
  let w : HeightOneSpectrum (𝓞 K) := ⟨W,hmax.isPrime,Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot W⟩
  let _ : w.asIdeal.LiesOver v.asIdeal := lies
  let u := discreteOrder (w.valuation K)
  obtain ⟨e,he,h2,bInt,inv⟩ := generator_dyadic_abscissa root v name w
  obtain ⟨d,hd,par,_⟩ := formal_parameter u bInt (generator_on_curve root) (by omega) inv
  exact infinite_of_dyadic_depth u bInt he h2 (paperGenerator root) hd par

/-- The scalar divisibility conclusion from rational contact, numerator, and pole orders.
The prime above p is arbitrary. -/
theorem odd_prime_scalar48_of_formalComparison {p : ℕ} [Fact p.Prime] (hp : 2<p)
    (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩).asIdeal]
    {ρ : K} (root : ρ^2=2)
    (comparison : ∀ τ : K ≃ₐ[ℚ] K,
       FormalComparison p ((discreteOrder (w.valuation K)).comap τ.toRingHom) (paperGenerator root))
    {h s : ℤ} (hh : h≠0) {r Γ : ℚ} (D₀ : ℕ)
    (hr : 0<padicValRat p r) (odd : Odd (padicValRat p r))
    (hgn : Γ≠0) (unit : padicValRat p Γ=0)
    (live : scalarTheta r (reciprocal (h • paperGenerator root))
      (parameter ((s-1) • paperGenerator root)/parameter (h • paperGenerator root)) ≠ 0)
    (pole : 0≤padicValRat p (scalarValue r Γ D₀ (reciprocal (h • paperGenerator root))
      (parameter ((s-1) • paperGenerator root)/parameter (h • paperGenerator root)))) :
    (p:ℤ)^48 ∣ s-1 :=
  odd_prime_scalar48 hp w root (paperGenerator_infinite root) comparison hh D₀ hr odd hgn unit live pole

end Sun28.Scalar
#print axioms Sun28.Scalar.generator_dyadic_abscissa
#print axioms Sun28.Scalar.paperGenerator_infinite
#print axioms Sun28.Scalar.odd_prime_scalar48_of_formalComparison
